//! Exact mathematical integer terms.
//!
//! `IntegerTerm` is deliberately separate from `MachineTerm`: the latter
//! is also the arena for C machine values and therefore carries machine-width
//! and overflow semantics.  Mathematical integers have no C representation.

use super::*;
use crate::kernel::{MachineCastSpelling, cast_term};
#[cfg(test)]
use crate::kernel::{bits32_constant, constant_u32};
mod machine_view;
mod operand_correspondence;
#[cfg(test)]
use crate::kernel::CompareRelation;
pub(crate) use machine_view::{
    MachineOperandView, clear_shared_machine_variable_cache, shared_machine_conversion_leaves,
    shared_machine_read_leaves, shared_machine_read_uses, shared_machine_syntax_variables,
};
use num_bigint::BigInt;
#[cfg(test)]
use num_traits::ToPrimitive;
use num_traits::{One, Zero};
pub(crate) use operand_correspondence::{
    machine_operand_syntax_cmp, shared_condition_operand_leaf_pairs, shared_machine_syntax_equal,
    shared_operand_leaf_pairs, shared_state_read_pairs,
};
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;
use std::sync::{Arc, Mutex, OnceLock, Weak};

fn charge_integer_bits(value: &BigInt) {
    // BigInt arithmetic and hashing scale with the magnitude, so account for
    // the encoded bit length rather than charging every numeral as a unit.
    crate::instrumentation::record_deterministic_work(value.bits() as usize + 1);
}

fn charge_binary_bits(left: &BigInt, right: &BigInt) {
    charge_integer_bits(left);
    charge_integer_bits(right);
}

fn charge_multiply_bits(left: &BigInt, right: &BigInt) {
    crate::instrumentation::record_deterministic_work(
        (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1),
    );
}

/// A symbolic, signed, unbounded mathematical integer.
///
/// The constructors below perform only root-local canonicalization.  Terms
/// are built bottom-up throughout the kernel, so looking through a complete
/// child tree here would make a long expression quadratic.  Public enum
/// variants remain useful for deserialization and test construction; callers
/// requiring canonical forms should use the constructors.
pub enum IntegerTerm {
    Constant(BigInt),
    Variable(Variable),
    Machine(SharedMachineIntegerTerm),
    Negate(SharedIntegerTerm),
    Add(SharedIntegerTerm, SharedIntegerTerm),
    Subtract(SharedIntegerTerm, SharedIntegerTerm),
    Multiply(SharedIntegerTerm, SharedIntegerTerm),
    /// Explicit truncation toward zero for guarded native machine division.
    /// A zero divisor stays opaque; this is not the surface Integer / policy.
    TruncatingQuotient(SharedIntegerTerm, SharedIntegerTerm),
    TruncatingRemainder(SharedIntegerTerm, SharedIntegerTerm),
    /// An opaque pure specification function application.  The body is
    /// exposed only by the checked `unfold` rule.
    PureFunctionApplication(SharedPureApplication),
    /// Exhaustive elimination of an algebraic value. Unknown scrutinees stay
    /// symbolic until a checked constructor value permits iota reduction.
    AlgebraicMatch {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicIntegerMatchArm>,
    },
    /// A conditional Integer value, the counterpart of the machine
    /// `MachineTerm::If`. Built by [`IntegerTerm::if_then_else`], so a
    /// constant condition or equal branches never stand.
    If {
        condition: Box<ConditionTerm>,
        then_term: SharedIntegerTerm,
        else_term: SharedIntegerTerm,
    },
    RangeFold {
        index: IntegerRangeFoldIndex,
        initial: SharedIntegerTerm,
        accumulator: Variable,
        item: Variable,
        body: SharedIntegerTerm,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicIntegerMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: SharedIntegerTerm,
    /// The written names of `bindings`, for printing only.
    pub binding_names: crate::kernel::BindingNames,
}

/// Canonical shallow node for an opaque pure function application.
/// Integer and pointer results share argument interning, but retain separate
/// value sorts; no pointer is interpreted as a numeric address.
#[derive(Clone)]
pub struct SharedPureApplication(Arc<SharedPureApplicationNode>);

/// The original name remains available for users of the Integer term API.
pub type SharedIntegerApplication = SharedPureApplication;

struct PureApplicationIdentity {
    id: u64,
}

struct SharedPureApplicationNode {
    identity: Arc<PureApplicationIdentity>,
    call: MachineTerm,
}

#[derive(Clone, Eq, PartialEq, Hash)]
enum PureApplicationArgumentKey {
    Machine(SharedMachineIntegerTerm),
    Other(PureFunctionArgument),
}

fn application_argument_keys(
    arguments: &[PureFunctionArgument],
) -> Vec<PureApplicationArgumentKey> {
    arguments
        .iter()
        .map(|argument| match argument.machine_identity() {
            Some(value) => PureApplicationArgumentKey::Machine(value),
            None => PureApplicationArgumentKey::Other(argument.clone()),
        })
        .collect()
}

struct PureApplicationInterner {
    buckets: HashMap<
        u64,
        Vec<(
            String,
            Vec<PureApplicationArgumentKey>,
            Weak<PureApplicationIdentity>,
        )>,
    >,
    cleanup: VecDeque<(u64, usize)>,
    next_id: u64,
}

impl PureApplicationInterner {
    #[cfg(test)]
    fn intern(
        &mut self,
        name: String,
        arguments: Vec<PureFunctionArgument>,
    ) -> SharedPureApplication {
        let keys = application_argument_keys(&arguments);
        self.intern_keyed(name, arguments, keys)
    }

    fn intern_keyed(
        &mut self,
        name: String,
        arguments: Vec<PureFunctionArgument>,
        argument_keys: Vec<PureApplicationArgumentKey>,
    ) -> SharedPureApplication {
        crate::instrumentation::record_deterministic_work(arguments.len().saturating_add(1));
        let mut hasher = crate::id_hash::FingerprintHasher::default();
        name.hash(&mut hasher);
        argument_keys.hash(&mut hasher);
        let key = hasher.finish();
        let cleanup_limit = self.cleanup.len().min(8);
        for _ in 0..cleanup_limit {
            let Some((fingerprint, pointer)) = self.cleanup.pop_front() else {
                break;
            };
            let mut requeue = false;
            if let Some(bucket) = self.buckets.get_mut(&fingerprint) {
                let live = bucket.iter().any(|(_, _, node)| {
                    node.as_ptr() as usize == pointer && node.strong_count() != 0
                });
                if live {
                    requeue = true;
                }
                bucket.retain(|(_, _, node)| {
                    node.as_ptr() as usize != pointer || node.strong_count() != 0
                });
                if bucket.is_empty() {
                    self.buckets.remove(&fingerprint);
                }
            }
            if requeue {
                self.cleanup.push_back((fingerprint, pointer));
            }
        }
        let identity = self
            .buckets
            .get(&key)
            .and_then(|bucket| {
                bucket
                    .iter()
                    .find_map(|(old_name, old_arguments, identity)| {
                        (old_name == &name && old_arguments == &argument_keys)
                            .then(|| identity.upgrade())
                            .flatten()
                    })
            })
            .unwrap_or_else(|| {
                let id = self.next_id;
                self.next_id = self
                    .next_id
                    .checked_add(1)
                    .expect("Pure application interner ID exhausted");
                let identity = Arc::new(PureApplicationIdentity { id });
                self.buckets.entry(key).or_default().push((
                    name.clone(),
                    argument_keys,
                    Arc::downgrade(&identity),
                ));
                self.cleanup
                    .push_back((key, Arc::as_ptr(&identity) as usize));
                identity
            });
        // Semantic identity is interned separately from the exact payload.
        // A caller never receives a previous producer's native/shared reading,
        // and repeated readings do not accumulate a bucket of payload versions.
        SharedPureApplication(Arc::new(SharedPureApplicationNode {
            identity,
            call: MachineTerm::ClickFunctionApplication { name, arguments },
        }))
    }
}

impl SharedPureApplication {
    pub(crate) fn intern(name: String, arguments: Vec<PureFunctionArgument>) -> Self {
        static INTERNER: OnceLock<Mutex<PureApplicationInterner>> = OnceLock::new();
        // Compute word identities outside the application-interner lock.
        let argument_keys = application_argument_keys(&arguments);
        INTERNER
            .get_or_init(|| {
                Mutex::new(PureApplicationInterner {
                    buckets: HashMap::new(),
                    cleanup: VecDeque::new(),
                    next_id: 0,
                })
            })
            .lock()
            .expect("Pure application interner lock poisoned")
            .intern_keyed(name, arguments, argument_keys)
    }
    pub(crate) fn id(&self) -> u64 {
        self.0.identity.id
    }
    /// Exact producer payload identity, distinct from semantic application identity.
    /// A retained application keeps this allocation alive while its key is used.
    pub(crate) fn payload_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }
    pub(crate) fn name(&self) -> &str {
        let MachineTerm::ClickFunctionApplication { name, .. } = &self.0.call else {
            unreachable!("application payload")
        };
        name
    }
    pub(crate) fn arguments(&self) -> &[PureFunctionArgument] {
        let MachineTerm::ClickFunctionApplication { arguments, .. } = &self.0.call else {
            unreachable!("application payload")
        };
        arguments
    }
    pub(crate) fn native_call(&self) -> &MachineTerm {
        &self.0.call
    }
}

impl fmt::Debug for SharedPureApplication {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PureApplication")
            .field("name", &self.name())
            .field("arguments", &self.arguments())
            .finish()
    }
}
impl PartialEq for SharedPureApplication {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}
impl Eq for SharedPureApplication {}
impl PartialOrd for SharedPureApplication {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SharedPureApplication {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}
impl Hash for SharedPureApplication {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum IntegerRangeFoldIndex {
    Int32 {
        start: SharedIntegerRangeEndpoint,
        end: SharedIntegerRangeEndpoint,
    },
    /// A range of unsigned 64-bit values, the type of a `size_t` or `usize`
    /// index. Its order is unsigned 64-bit order and its item is a `uint64`.
    UInt64 {
        start: SharedIntegerRangeEndpoint,
        end: SharedIntegerRangeEndpoint,
    },
    Integer {
        start: SharedIntegerTerm,
        end: SharedIntegerTerm,
    },
}

impl IntegerRangeFoldIndex {
    /// The machine type of the item a body binds, or `None` for a range of
    /// mathematical integers, whose item is an Integer variable.
    pub(crate) fn machine_item_type(&self) -> Option<MachineIntegerType> {
        match self {
            Self::Int32 { .. } => Some(MachineIntegerType::Int32),
            Self::UInt64 { .. } => Some(MachineIntegerType::UInt64),
            Self::Integer { .. } => None,
        }
    }
}

#[derive(Clone)]
pub struct SharedIntegerRangeEndpoint {
    node: SharedMachineIntegerTerm,
}

impl fmt::Debug for SharedIntegerRangeEndpoint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("SharedIntegerRangeEndpoint")
            .field(&self.id())
            .field(self.value())
            .finish()
    }
}

impl PartialEq for SharedIntegerRangeEndpoint {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for SharedIntegerRangeEndpoint {}

impl PartialOrd for SharedIntegerRangeEndpoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SharedIntegerRangeEndpoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}

impl Hash for SharedIntegerRangeEndpoint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

impl SharedIntegerRangeEndpoint {
    pub(crate) fn from_shared(root: KernelTerm) -> Option<Self> {
        SharedMachineIntegerTerm::from_shared(
            MachineIntegerType::Int32,
            root.with_machine_observation_type(MachineIntegerType::Int32),
        )
        .map(|node| Self { node })
    }

    pub(crate) fn machine_operand(&self) -> &SharedMachineIntegerTerm {
        &self.node
    }

    pub(crate) fn with_shared_operand(&self, root: KernelTerm) -> Option<Self> {
        SharedMachineIntegerTerm::from_shared(self.node.ty(), root).map(|node| Self { node })
    }

    pub fn intern(value: MachineTerm) -> Self {
        Self {
            node: SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, value),
        }
    }
    pub fn id(&self) -> u64 {
        self.node.id()
    }
    pub fn value(&self) -> &MachineTerm {
        self.node.value()
    }
}

impl Clone for IntegerTerm {
    fn clone(&self) -> Self {
        match self {
            Self::Constant(value) => Self::Constant(value.clone()),
            Self::Variable(variable) => Self::Variable(*variable),
            Self::Machine(value) => Self::Machine(value.clone()),
            Self::Negate(value) => Self::Negate(value.clone()),
            Self::Add(left, right) => Self::Add(left.clone(), right.clone()),
            Self::Subtract(left, right) => Self::Subtract(left.clone(), right.clone()),
            Self::Multiply(left, right) => Self::Multiply(left.clone(), right.clone()),
            Self::TruncatingQuotient(left, right) => {
                Self::TruncatingQuotient(left.clone(), right.clone())
            }
            Self::TruncatingRemainder(left, right) => {
                Self::TruncatingRemainder(left.clone(), right.clone())
            }
            Self::PureFunctionApplication(application) => {
                Self::PureFunctionApplication(application.clone())
            }
            Self::AlgebraicMatch { scrutinee, arms } => Self::AlgebraicMatch {
                scrutinee: scrutinee.clone(),
                arms: arms.clone(),
            },
            Self::If {
                condition,
                then_term,
                else_term,
            } => Self::If {
                condition: condition.clone(),
                then_term: then_term.clone(),
                else_term: else_term.clone(),
            },
            Self::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => Self::RangeFold {
                index: index.clone(),
                initial: initial.clone(),
                accumulator: *accumulator,
                item: *item,
                body: body.clone(),
            },
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MachineIntegerType {
    Int8,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int64,
    UInt64,
    Int128,
    UInt128,
}

impl MachineIntegerType {
    pub fn symbolic_value(self, variable: Variable) -> ProgramValue {
        let term = MachineTerm::Variable(variable);
        match self {
            Self::Int8 => ProgramValue::Int8(term),
            Self::Int16 => ProgramValue::Int16(term),
            Self::Int32 => ProgramValue::Int32(term),
            Self::UInt8 => ProgramValue::UInt8(term),
            Self::UInt16 => ProgramValue::UInt16(term),
            Self::UInt32 => ProgramValue::UInt32(term),
            Self::Int64 => ProgramValue::Int64(term),
            Self::UInt64 => ProgramValue::UInt64(term),
            Self::Int128 => ProgramValue::Int128(term),
            Self::UInt128 => ProgramValue::UInt128(term),
        }
    }

    pub fn from_program_type(program_type: ProgramType) -> Option<Self> {
        Some(match program_type {
            ProgramType::Int8 => Self::Int8,
            ProgramType::Int16 => Self::Int16,
            ProgramType::Int32 => Self::Int32,
            ProgramType::UInt8 => Self::UInt8,
            ProgramType::UInt16 => Self::UInt16,
            ProgramType::UInt32 => Self::UInt32,
            ProgramType::Int64 => Self::Int64,
            ProgramType::UInt64 => Self::UInt64,
            ProgramType::Int128 => Self::Int128,
            ProgramType::UInt128 => Self::UInt128,
            _ => return None,
        })
    }

    pub fn program_type(self) -> ProgramType {
        match self {
            Self::Int8 => ProgramType::Int8,
            Self::Int16 => ProgramType::Int16,
            Self::Int32 => ProgramType::Int32,
            Self::UInt8 => ProgramType::UInt8,
            Self::UInt16 => ProgramType::UInt16,
            Self::UInt32 => ProgramType::UInt32,
            Self::Int64 => ProgramType::Int64,
            Self::UInt64 => ProgramType::UInt64,
            Self::Int128 => ProgramType::Int128,
            Self::UInt128 => ProgramType::UInt128,
        }
    }
}

/// A signed machine width whose `defined(a + b)` and `defined(a - b)` the
/// `rules` arithmetic certificate's `int32_defined` / `int64_defined` rule
/// establishes from the operands' constant bounds. One checker serves both
/// widths; this names which one a node claims.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SignedDefinedWidth {
    Int32,
    Int64,
}

impl SignedDefinedWidth {
    /// The type name, as the certificate node and diagnostics spell it.
    pub fn name(self) -> &'static str {
        match self {
            Self::Int32 => "int32",
            Self::Int64 => "int64",
        }
    }

    /// The inclusive value range of the width.
    pub fn range(self) -> (i64, i64) {
        match self {
            Self::Int32 => (i64::from(i32::MIN), i64::from(i32::MAX)),
            Self::Int64 => (i64::MIN, i64::MAX),
        }
    }
}

/// Retained machine operand. Deliberately has no native Deref/AsRef: checked
/// consumers inspect `operand_view`; native output conversion is explicit.
pub struct SharedMachineIntegerTerm(Arc<SharedMachineIntegerNode>);

struct SharedMachineIntegerNode {
    id: u64,
    ty: MachineIntegerType,
    operand: MachineIntegerOperand,
    /// The observation's value reading ([`SharedMachineIntegerTerm::value_reading`]),
    /// computed once on first use.
    reading: OnceLock<Option<IntegerTerm>>,
}

enum MachineIntegerOperand {
    Shared {
        term: KernelTerm,
        boxed: OnceLock<MachineTerm>,
        structural: OnceLock<MachineTerm>,
    },
    Legacy(MachineTerm),
    // Keep this producer's complete payload even when legacy equality omits
    // annotations. The retained identity keeps the old native key alive.
    ExactLegacy {
        value: MachineTerm,
        _identity: SharedMachineIntegerTerm,
    },
}

impl Clone for SharedMachineIntegerTerm {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl PartialOrd for SharedMachineIntegerTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SharedMachineIntegerTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}
impl fmt::Debug for SharedMachineIntegerTerm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SharedMachineIntegerTerm")
            .field("id", &self.id())
            .field("type", &self.ty())
            .finish()
    }
}

// Retained observations have exact, format-tagged identities. Hashing or
// comparing a lookup key must not request the boxed operand.
impl PartialEq for SharedMachineIntegerTerm {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}
impl Eq for SharedMachineIntegerTerm {}
impl std::hash::Hash for SharedMachineIntegerTerm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

thread_local! {
    // Reuse explicit boxed imports within one verification, but never make a
    // later verification's work depend on an earlier session's warm interner.
    static MACHINE_OBSERVATION_IMPORTS: std::cell::RefCell<crate::id_hash::U64Map<SharedMachineIntegerTerm>> = Default::default();
}

pub(super) fn clear_machine_observation_memo() {
    MACHINE_OBSERVATION_IMPORTS.with(|seen| seen.borrow_mut().clear());
}

mod observation_identity;

impl SharedMachineIntegerTerm {
    /// An explicit native operand already imported in this verification.
    /// Read-only: a miss does not import syntax or retain an opaque payload.
    pub(crate) fn retained_import(ty: MachineIntegerType, value: &MachineTerm) -> Option<Self> {
        let key = MachineIntegerKey::native(ty, value.clone());
        let found = MACHINE_INTEGER_INTERNER
            .get()?
            .lock()
            .expect("machine Integer interner lock poisoned")
            .find(&key)?;
        (found.shared_operand().is_some()
            && MACHINE_OBSERVATION_IMPORTS.with(|seen| seen.borrow().contains_key(&found.id())))
        .then_some(found)
    }

    /// An address index owns its exact structure. Import shared operands
    /// directly: a cached native input may still contain a reserved name,
    /// and native state equality is not a cross-arena structural key.
    pub(crate) fn index(ty: MachineIntegerType, value: MachineTerm) -> Self {
        let mut import = KernelTermImport::default();
        if let Some(term) = import.machine_arithmetic(ty, &value) {
            let shared = Self::from_shared(ty, term).expect("admitted index operand");
            if !import.machine_input_requires_export
                && let MachineIntegerOperand::Shared { structural, .. } = &shared.0.operand
            {
                // Retain the explicit input; reconstructing it would export
                // an operand that the producer already supplied.
                let _ = structural.set(value.clone());
            }
            return shared;
        }
        let identity = Self::intern_key(MachineIntegerKey::native(ty, value.clone()));
        Self(Arc::new(SharedMachineIntegerNode {
            id: identity.id(),
            ty,
            operand: MachineIntegerOperand::ExactLegacy {
                value,
                _identity: identity,
            },
            reading: OnceLock::new(),
        }))
    }

    /// Retain an unchanged index after a native mapper. Numeric syntax without
    /// reads/conversions has exact native equality; opaque payloads do not.
    /// A direct read compares arena identity before any native address data.
    pub(crate) fn with_mapped_index(&self, mapped: MachineTerm) -> Self {
        if let Some(root) = self.shared_operand() {
            let unchanged = if let Some(MachineTerm::MemoryLoad(memory, address, kind)) =
                root.machine_read_leaf()
            {
                matches!(&mapped, MachineTerm::MemoryLoad(other, pointer, other_kind)
                    if memory.arena_id() == other.arena_id() && address == pointer && kind == other_kind)
            } else {
                !root.has_machine_reads()
                    && !root.has_machine_conversions()
                    && self.structural_value() == &mapped
            };
            if unchanged {
                return self.clone();
            }
        }
        Self::index(self.ty(), mapped)
    }

    pub fn intern(ty: MachineIntegerType, value: MachineTerm) -> Self {
        // Legacy callers already supply a boxed tree. Reuse its existing
        // interned observation before importing, and retain that explicit tree
        // instead of exporting it again on the first checker read.
        let key = MachineIntegerKey::native(ty, value);
        if let MachineIntegerKey::Application { application, .. } = &key {
            // Calls compare their typed argument values, independently of
            // whether a producer supplied a native or retained reading.
            // Keep this producer's exact payload outside that identity key.
            let value = MachineTerm::ClickFunctionApplication {
                name: application.name().to_owned(),
                arguments: application.arguments().to_vec(),
            };
            // A retained opaque call is observed as a shared leaf whose
            // payload key owns the typed application identity. Use that same
            // observation here rather than exposing the intermediate payload
            // ID as a second numeric identity for the native carrier.
            let payload_identity = Self::intern_key(key);
            let observation =
                KernelTerm::machine_observation_leaf(ty, value.clone(), payload_identity);
            let identity = Self::from_shared(ty, observation).expect("opaque call observation");
            return Self(Arc::new(SharedMachineIntegerNode {
                id: identity.id(),
                ty,
                operand: MachineIntegerOperand::ExactLegacy {
                    value,
                    _identity: identity,
                },
                reading: OnceLock::new(),
            }));
        }
        let interner =
            MACHINE_INTEGER_INTERNER.get_or_init(|| Mutex::new(MachineIntegerInterner::default()));
        if let Some(found) = interner
            .lock()
            .expect("machine Integer interner lock poisoned")
            .find(&key)
            && (found.shared_operand().is_none()
                || MACHINE_OBSERVATION_IMPORTS.with(|seen| seen.borrow().contains_key(&found.id())))
        {
            // A graph lookup may have memoized only the shared identity.
            // This constructor receives an explicit boxed input, so retain
            // that input rather than exporting the shared DAG on a later read.
            if let MachineIntegerOperand::Shared { boxed, .. } = &found.0.operand
                && boxed.get().is_none()
                && let MachineIntegerKey::Legacy { value, .. } = &key
            {
                let _ = boxed.set(value.clone());
            }
            return found;
        }
        let MachineIntegerKey::Legacy { value, .. } = &key else {
            unreachable!()
        };
        if let Some(term) = KernelTermImport::default().machine_arithmetic(ty, value) {
            let shared =
                if term.has_opaque_observation_boundary() && term.has_machine_control_terms() {
                    Self::observe_shared(ty, term)
                } else {
                    Self::from_shared(ty, term)
                }
                .expect("arithmetic storage fragment");
            let MachineIntegerOperand::Shared { boxed, .. } = &shared.0.operand else {
                unreachable!()
            };
            let _ = boxed.set(value.clone());
            shared.remember_explicit_import(key);
            return shared;
        }
        let view = MachineOperandView::Legacy(value);
        if view.binary().is_some()
            || view.unary().is_some()
            || view.cast().is_some()
            || matches!(value, MachineTerm::If { .. })
        {
            let root = KernelTerm::retained_machine_operand(ty, view);
            let shared = Self::observe_shared(ty, root).expect("retained machine observation");
            if let MachineIntegerOperand::Shared { boxed, .. } = &shared.0.operand {
                let _ = boxed.set(value.clone());
            }
            shared.remember_explicit_import(key);
            return shared;
        }
        Self::intern_key(key)
    }

    /// Import an explicitly supplied native arithmetic operand once per
    /// verification. Unlike `intern`, a non-arithmetic payload is refused
    /// without placing its memory states in the global interner.
    pub(crate) fn import_arithmetic(ty: MachineIntegerType, value: &MachineTerm) -> Option<Self> {
        if let Some(found) = Self::retained_import(ty, value) {
            return Some(found);
        }
        // Signed and unsigned observations retain the same word syntax.
        // Admission may already have imported the opposite reading; retag its
        // root instead of walking the explicitly supplied tree a second time.
        let alternate = match ty {
            MachineIntegerType::Int8 => MachineIntegerType::UInt8,
            MachineIntegerType::UInt8 => MachineIntegerType::Int8,
            MachineIntegerType::Int16 => MachineIntegerType::UInt16,
            MachineIntegerType::UInt16 => MachineIntegerType::Int16,
            MachineIntegerType::Int32 => MachineIntegerType::UInt32,
            MachineIntegerType::UInt32 => MachineIntegerType::Int32,
            MachineIntegerType::Int64 => MachineIntegerType::UInt64,
            MachineIntegerType::UInt64 => MachineIntegerType::Int64,
            MachineIntegerType::Int128 => MachineIntegerType::UInt128,
            MachineIntegerType::UInt128 => MachineIntegerType::Int128,
        };
        let root = Self::retained_import(alternate, value)
            .and_then(|retained| {
                retained
                    .shared_operand()
                    .map(|root| root.with_machine_observation_type(ty))
            })
            .or_else(|| KernelTermImport::default().machine_arithmetic(ty, value))?;
        // Scoped machine forms can retain opaque calls in their bodies.
        // Use the same numeric observation as `intern`, while preserving
        // the exact imported root at its producer boundary.
        let shared = if root.has_opaque_observation_boundary() && root.has_machine_control_terms() {
            Self::observe_shared(ty, root)
        } else {
            Self::from_shared(ty, root)
        }?;
        shared.remember_explicit_import(MachineIntegerKey::native(ty, value.clone()));
        Some(shared)
    }

    fn remember_explicit_import(&self, key: MachineIntegerKey) {
        MACHINE_INTEGER_INTERNER
            .get()
            .expect("shared machine interner")
            .lock()
            .expect("machine Integer interner lock poisoned")
            .remember(key, self);
        MACHINE_OBSERVATION_IMPORTS.with(|seen| seen.borrow_mut().insert(self.id(), self.clone()));
    }

    /// Observe retained arithmetic without exporting prefixes. Opaque producer
    /// identities are mapped once to their existing numeric observation keys.
    pub(crate) fn observe_shared(ty: MachineIntegerType, term: KernelTerm) -> Option<Self> {
        Self::from_shared(ty, observation_identity::normalize(&term))
    }

    /// Retain exact operand identity, including producer and read metadata.
    pub(crate) fn from_shared(ty: MachineIntegerType, term: KernelTerm) -> Option<Self> {
        if term.ty() != &KernelType::Program(ty.program_type()) || !term.is_shared_machine_operand()
        {
            return None;
        }
        crate::instrumentation::record_deterministic_work(1);
        Some(Self::intern_key(MachineIntegerKey::Shared { ty, term }))
    }

    fn intern_key(key: MachineIntegerKey) -> Self {
        MACHINE_INTEGER_INTERNER
            .get_or_init(|| Mutex::new(MachineIntegerInterner::default()))
            .lock()
            .expect("machine Integer interner lock poisoned")
            .intern(key)
    }

    pub(crate) fn shared_operand(&self) -> Option<&KernelTerm> {
        match &self.0.operand {
            MachineIntegerOperand::Shared { term, .. } => Some(term),
            MachineIntegerOperand::Legacy(_) | MachineIntegerOperand::ExactLegacy { .. } => None,
        }
    }
    /// The explicit legacy input, if one was already retained. Unlike
    /// `value`, this never exports a shared operand or fills its cache.
    pub(crate) fn retained_written_operand(&self) -> Option<&MachineTerm> {
        match &self.0.operand {
            MachineIntegerOperand::Shared {
                boxed, structural, ..
            } => boxed.get().or_else(|| structural.get()),
            MachineIntegerOperand::Legacy(value)
            | MachineIntegerOperand::ExactLegacy { value, .. } => Some(value),
        }
    }

    #[cfg(test)]
    pub(crate) fn has_boxed_operand(&self) -> bool {
        match &self.0.operand {
            MachineIntegerOperand::Shared {
                boxed, structural, ..
            } => boxed.get().is_some() || structural.get().is_some(),
            MachineIntegerOperand::Legacy(_) | MachineIntegerOperand::ExactLegacy { .. } => true,
        }
    }

    pub fn id(&self) -> u64 {
        self.0.id
    }
    pub fn ty(&self) -> MachineIntegerType {
        self.0.ty
    }
    /// Explicit legacy structural output. May expand shared arithmetic; checked
    /// consumers must use `operand_view` instead. The
    /// separate written-input cache can contain a registered read name.
    pub(crate) fn structural_value(&self) -> &MachineTerm {
        match &self.0.operand {
            MachineIntegerOperand::Shared {
                term, structural, ..
            } => structural
                .get_or_init(|| KernelTermExport::machine(term).expect("shared machine operand")),
            MachineIntegerOperand::Legacy(value)
            | MachineIntegerOperand::ExactLegacy { value, .. } => value,
        }
    }

    pub fn value(&self) -> &MachineTerm {
        match &self.0.operand {
            MachineIntegerOperand::Shared {
                term,
                boxed,
                structural,
            } => boxed.get_or_init(|| {
                structural.get().cloned().unwrap_or_else(|| {
                    KernelTermExport::machine(term).expect("shared machine operand")
                })
            }),
            MachineIntegerOperand::Legacy(value)
            | MachineIntegerOperand::ExactLegacy { value, .. } => value,
        }
    }

    /// The Integer term this observation equals by the value relations of
    /// conversions (rule W): `to_integer(widen(v))` is `to_integer(v)`, an
    /// observation of σ(x) at either 32-bit format is `x` read at that
    /// format, and a conversion into a type the observation's type contains
    /// is read at that type. `None` when no relation applies: the
    /// observation is its own reading. [`IntegerTerm::from_machine`] builds
    /// the observation as written; reasoning that identifies values (the
    /// Integer engines' atoms, certificate premise matching) reads it
    /// through this. Computed once per interned observation: a bounded walk
    /// through at most three conversions, one interning of the operand.
    pub fn value_reading(&self) -> Option<&IntegerTerm> {
        // Reading work is session-local even when the interned observation's
        // OnceLock survives an earlier verification. Warm global nodes must
        // not change the work charged for otherwise identical input.
        let shared_reading = self.shared_operand().map(|root| {
            let reading = if matches!(
                root.node(),
                KernelTermNode::MachineCast { .. } | KernelTermNode::MachineLiteral(_)
            ) {
                machine_view::shared_value_reading(self.ty(), root)
            } else {
                Some((self.ty(), root.clone()))
            };
            (root, reading)
        });
        self.0
            .reading
            .get_or_init(|| {
                if let Some((root, reading)) = shared_reading {
                    let (ty, read) = reading?;
                    if let KernelTermNode::MachineLiteral(value) = read.node() {
                        return Some(IntegerTerm::constant(
                            ty.constant_from_term(&value.legacy_term())?.to_integer(),
                        ));
                    }
                    if ty == self.ty() && read.id() == root.id() {
                        return None;
                    }
                    let read = SharedMachineIntegerTerm::from_shared(
                        ty,
                        read.with_machine_observation_type(ty),
                    )?;
                    let _ = read.0.reading.set(None);
                    return Some(IntegerTerm::Machine(read));
                }
                let reading = machine_value_reading(self.ty(), self.value())?;
                match &reading {
                    ValueReading::Observation(ty, value)
                        if *ty == self.ty() && std::ptr::eq(*value, self.value()) =>
                    {
                        None
                    }
                    ValueReading::Observation(ty, value) => {
                        let read = SharedMachineIntegerTerm::intern(*ty, (*value).clone());
                        // The walk reads through every relation, so the
                        // reading is its own.
                        let _ = read.0.reading.set(None);
                        Some(IntegerTerm::Machine(read))
                    }
                    ValueReading::Constant(value) => Some(IntegerTerm::constant(value.clone())),
                }
            })
            .as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum MachineIntegerKey {
    Shared {
        ty: MachineIntegerType,
        term: KernelTerm,
    },
    Legacy {
        // Compare the scope before the native payload: its states have
        // content equality across arenas, which can walk unrelated memory.
        arena: u32,
        ty: MachineIntegerType,
        value: MachineTerm,
    },
    Application {
        arena: u32,
        ty: MachineIntegerType,
        application: SharedPureApplication,
    },
}
impl MachineIntegerKey {
    fn native(ty: MachineIntegerType, value: MachineTerm) -> Self {
        if let MachineTerm::ClickFunctionApplication { name, arguments } = value {
            return Self::Application {
                arena: super::memory_arena_token(),
                ty,
                application: SharedPureApplication::intern(name, arguments),
            };
        }
        Self::Legacy {
            arena: super::memory_arena_token(),
            ty,
            value,
        }
    }
}

#[derive(Default)]
struct MachineIntegerInterner {
    next_id: u64,
    values: crate::id_hash::U64Map<Vec<(MachineIntegerKey, Weak<SharedMachineIntegerNode>)>>,
    cleanup_queue: VecDeque<(u64, usize)>,
}

static MACHINE_INTEGER_INTERNER: OnceLock<Mutex<MachineIntegerInterner>> = OnceLock::new();

impl MachineIntegerInterner {
    fn find(&self, key: &MachineIntegerKey) -> Option<SharedMachineIntegerTerm> {
        let mut hasher = crate::id_hash::FingerprintHasher::default();
        key.hash(&mut hasher);
        self.values
            .get(&hasher.finish())?
            .iter()
            .find_map(|(candidate, node)| {
                (candidate == key)
                    .then(|| node.upgrade().map(SharedMachineIntegerTerm))
                    .flatten()
            })
    }

    fn remember(&mut self, key: MachineIntegerKey, node: &SharedMachineIntegerTerm) {
        if self.find(&key).is_some() {
            return;
        }
        let mut hasher = crate::id_hash::FingerprintHasher::default();
        key.hash(&mut hasher);
        let fingerprint = hasher.finish();
        self.values
            .entry(fingerprint)
            .or_default()
            .push((key, Arc::downgrade(&node.0)));
        self.cleanup_queue
            .push_back((fingerprint, Arc::as_ptr(&node.0) as usize));
    }

    fn intern(&mut self, key: MachineIntegerKey) -> SharedMachineIntegerTerm {
        for _ in 0..8 {
            let Some((fingerprint, pointer)) = self.cleanup_queue.pop_front() else {
                break;
            };
            if let Some(bucket) = self.values.get_mut(&fingerprint) {
                if bucket
                    .iter()
                    .any(|(_, node)| node.as_ptr() as usize == pointer && node.strong_count() != 0)
                {
                    self.cleanup_queue.push_back((fingerprint, pointer));
                }
                bucket.retain(|(_, node)| {
                    node.as_ptr() as usize != pointer || node.strong_count() != 0
                });
                if bucket.is_empty() {
                    self.values.remove(&fingerprint);
                }
            }
        }
        let mut hasher = crate::id_hash::FingerprintHasher::default();
        key.hash(&mut hasher);
        let fingerprint = hasher.finish();
        if let Some(bucket) = self.values.get(&fingerprint) {
            for (candidate, node) in bucket {
                if candidate == &key
                    && let Some(node) = node.upgrade()
                {
                    return SharedMachineIntegerTerm(node);
                }
            }
        }
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .expect("machine Integer identity exhausted");
        let (ty, operand) = match &key {
            MachineIntegerKey::Shared { ty, term } => (
                *ty,
                MachineIntegerOperand::Shared {
                    term: term.clone(),
                    boxed: OnceLock::new(),
                    structural: OnceLock::new(),
                },
            ),
            MachineIntegerKey::Legacy { ty, value, .. } => {
                (*ty, MachineIntegerOperand::Legacy(value.clone()))
            }
            MachineIntegerKey::Application {
                ty, application, ..
            } => (
                *ty,
                MachineIntegerOperand::Legacy(MachineTerm::ClickFunctionApplication {
                    name: application.name().to_owned(),
                    arguments: application.arguments().to_vec(),
                }),
            ),
        };
        let node = Arc::new(SharedMachineIntegerNode {
            id,
            ty,
            operand,
            reading: OnceLock::new(),
        });
        self.values
            .entry(fingerprint)
            .or_default()
            .push((key, Arc::downgrade(&node)));
        self.cleanup_queue
            .push_back((fingerprint, Arc::as_ptr(&node) as usize));
        SharedMachineIntegerTerm(node)
    }
}

/// An immutable Integer node.  Children are interned by shallow identity, so
/// cloning a shared child never clones its transitive DAG.
pub struct SharedIntegerTerm(Arc<SharedIntegerNode>);

struct SharedIntegerNode {
    id: u64,
    term: IntegerTerm,
    literal_arithmetic: bool,
    kernel_term: OnceLock<KernelTerm>,
    /// [`SharedIntegerTerm::read_through`], computed once on first use;
    /// `None` when the node is its own reading.
    read_through: OnceLock<Option<SharedIntegerTerm>>,
}

/// Weak reverse migration link: the common tree must not keep its source
/// alive when that source already owns the converted tree.
#[derive(Clone, Default)]
pub(crate) struct WeakIntegerTerm(Weak<SharedIntegerNode>);
impl WeakIntegerTerm {
    pub(crate) fn upgrade(&self) -> Option<SharedIntegerTerm> {
        self.0.upgrade().map(SharedIntegerTerm)
    }
}

impl SharedIntegerTerm {
    pub(crate) fn kernel_term(&self) -> Option<&KernelTerm> {
        self.0.kernel_term.get()
    }
    pub(crate) fn remember_kernel_term(&self, term: KernelTerm) {
        let _ = self.0.kernel_term.set(term);
    }
    pub(crate) fn downgrade(&self) -> WeakIntegerTerm {
        WeakIntegerTerm(Arc::downgrade(&self.0))
    }

    /// Cached from immediate children when the node is introduced. Numeric
    /// checking can leave symbolic nonlinear operands opaque without a walk.
    pub(crate) fn is_literal_arithmetic(&self) -> bool {
        self.0.literal_arithmetic
    }

    pub(crate) fn id(&self) -> u64 {
        self.0.id
    }

    pub(crate) fn as_ref(&self) -> &IntegerTerm {
        &self.0.term
    }

    /// This term with every machine observation among its arithmetic
    /// (negation, `+`, `-`, `*`, truncating quotient and remainder) read through its value
    /// relations (rule W, [`SharedMachineIntegerTerm::value_reading`]):
    /// `to_integer(a as int128) * to_integer(b as int128)` reads as
    /// `to_integer(a) * to_integer(b)`. Reasoning keys an opaque product by
    /// this reading, so the two spellings are one atom; the term itself is
    /// unchanged. Each node's reading is computed once, when the node is
    /// interned, from its children's readings, and cached on the node, which
    /// keeps the rebuilt node alive and its identity stable: O(1) per node,
    /// and reading it is a lookup. Other nodes (applications, conditionals,
    /// folds) are their own reading.
    pub(crate) fn read_through(&self) -> SharedIntegerTerm {
        self.read_through_ref().clone()
    }

    /// [`Self::read_through`] by reference to the cached reading.
    pub(crate) fn read_through_ref(&self) -> &SharedIntegerTerm {
        if self.0.read_through.get().is_none() {
            self.compute_read_through();
        }
        self.0
            .read_through
            .get()
            .and_then(Option::as_ref)
            .unwrap_or(self)
    }

    fn compute_read_through(&self) {
        let children = |node: &SharedIntegerTerm| -> Vec<SharedIntegerTerm> {
            match node.as_ref() {
                IntegerTerm::Negate(child) => vec![child.clone()],
                crate::kernel::binary_integer_term!(left, right) => {
                    vec![left.clone(), right.clone()]
                }
                _ => Vec::new(),
            }
        };
        let mut stack = vec![(self.clone(), false)];
        while let Some((node, expanded)) = stack.pop() {
            if node.0.read_through.get().is_some() {
                continue;
            }
            if !expanded {
                stack.push((node.clone(), true));
                stack.extend(
                    children(&node)
                        .into_iter()
                        .filter(|child| child.0.read_through.get().is_none())
                        .map(|child| (child, false)),
                );
                continue;
            }
            let read = |child: &SharedIntegerTerm| -> SharedIntegerTerm {
                child
                    .0
                    .read_through
                    .get()
                    .and_then(Option::clone)
                    .unwrap_or_else(|| child.clone())
            };
            let rebuilt = match node.as_ref() {
                IntegerTerm::Machine(machine) => machine
                    .value_reading()
                    .map(|reading| SharedIntegerTerm::intern(reading.clone())),
                IntegerTerm::Negate(child) => {
                    let child_read = read(child);
                    (child_read.id() != child.id())
                        .then(|| SharedIntegerTerm::intern(IntegerTerm::Negate(child_read)))
                }
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right)
                | IntegerTerm::TruncatingQuotient(left, right)
                | IntegerTerm::TruncatingRemainder(left, right) => {
                    let (left_read, right_read) = (read(left), read(right));
                    (left_read.id() != left.id() || right_read.id() != right.id()).then(|| {
                        SharedIntegerTerm::intern(match node.as_ref() {
                            IntegerTerm::Add(..) => IntegerTerm::Add(left_read, right_read),
                            IntegerTerm::Subtract(..) => {
                                IntegerTerm::Subtract(left_read, right_read)
                            }
                            IntegerTerm::Multiply(..) => {
                                IntegerTerm::Multiply(left_read, right_read)
                            }
                            IntegerTerm::TruncatingQuotient(..) => {
                                IntegerTerm::TruncatingQuotient(left_read, right_read)
                            }
                            _ => IntegerTerm::TruncatingRemainder(left_read, right_read),
                        })
                    })
                }
                _ => None,
            };
            // A reading is its own reading: its children are readings and a
            // read observation has no further relation to read through.
            if let Some(rebuilt) = &rebuilt {
                let _ = rebuilt.0.read_through.set(None);
            }
            let _ = node.0.read_through.set(rebuilt);
        }
    }

    /// Interns `term` and computes its reading ([`Self::read_through`])
    /// from its children's, which interning computed before: O(1) per new
    /// node, so no later reader walks a term's DAG.
    pub(crate) fn intern(term: IntegerTerm) -> Self {
        let node = integer_interner()
            .lock()
            .expect("Integer interner lock poisoned")
            .intern(term);
        if node.0.read_through.get().is_none() {
            node.compute_read_through();
        }
        node
    }
}

impl From<IntegerTerm> for SharedIntegerTerm {
    fn from(term: IntegerTerm) -> Self {
        Self::intern(term)
    }
}

impl std::ops::Deref for SharedIntegerTerm {
    type Target = IntegerTerm;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl Clone for SharedIntegerTerm {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl PartialEq for SharedIntegerTerm {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for SharedIntegerTerm {}

impl Hash for SharedIntegerTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

impl PartialOrd for SharedIntegerTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SharedIntegerTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}

impl fmt::Debug for SharedIntegerTerm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SharedIntegerTerm")
            .field("id", &self.id())
            .finish()
    }
}

impl PartialEq for IntegerTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for IntegerTerm {}

impl Hash for IntegerTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.shallow_key().hash(state);
    }
}

impl PartialOrd for IntegerTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IntegerTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.shallow_key().cmp(&other.shallow_key())
    }
}

impl fmt::Debug for IntegerTerm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(value) => formatter.debug_tuple("Constant").field(value).finish(),
            Self::Variable(variable) => formatter.debug_tuple("Variable").field(variable).finish(),
            Self::Machine(value) => formatter.debug_tuple("Machine").field(&value.id()).finish(),
            Self::Negate(value) => formatter.debug_tuple("Negate").field(&value.id()).finish(),
            Self::Add(left, right) => formatter
                .debug_tuple("Add")
                .field(&left.id())
                .field(&right.id())
                .finish(),
            Self::Subtract(left, right) => formatter
                .debug_tuple("Subtract")
                .field(&left.id())
                .field(&right.id())
                .finish(),
            Self::Multiply(left, right) => formatter
                .debug_tuple("Multiply")
                .field(&left.id())
                .field(&right.id())
                .finish(),
            Self::TruncatingQuotient(left, right) => formatter
                .debug_tuple("TruncatingQuotient")
                .field(&left.id())
                .field(&right.id())
                .finish(),
            Self::TruncatingRemainder(left, right) => formatter
                .debug_tuple("TruncatingRemainder")
                .field(&left.id())
                .field(&right.id())
                .finish(),
            Self::PureFunctionApplication(application) => formatter
                .debug_struct("PureFunctionApplication")
                .field("id", &application.id())
                .finish(),
            Self::AlgebraicMatch { scrutinee, arms } => formatter
                .debug_struct("AlgebraicMatch")
                .field("scrutinee", scrutinee)
                .field("arms", arms)
                .finish(),
            Self::If {
                condition,
                then_term,
                else_term,
            } => formatter
                .debug_struct("If")
                .field("condition", condition)
                .field("then_term", &then_term.id())
                .field("else_term", &else_term.id())
                .finish(),
            Self::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => formatter
                .debug_struct("RangeFold")
                .field("index", index)
                .field("initial", &initial.id())
                .field("accumulator", accumulator)
                .field("item", item)
                .field("body", &body.id())
                .finish(),
        }
    }
}

impl fmt::Display for SharedIntegerTerm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut seen = std::collections::BTreeSet::new();
        fmt_integer_shared(self, formatter, &mut seen)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum IntegerShallowKey {
    Constant(BigInt),
    Variable(Variable),
    Machine(u64),
    Negate(u64),
    Add(u64, u64),
    Subtract(u64, u64),
    Multiply(u64, u64),
    TruncatingQuotient(u64, u64),
    TruncatingRemainder(u64, u64),
    PureFunctionApplication(u64),
    AlgebraicMatch {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicIntegerMatchArm>,
    },
    If(Box<ConditionTerm>, u64, u64),
    RangeFold(IntegerRangeFoldIndex, u64, Variable, Variable, u64),
}

impl IntegerTerm {
    pub fn max_variable(&self) -> Option<Variable> {
        let mut variables = BTreeSet::new();
        fn visit(term: &IntegerTerm, variables: &mut BTreeSet<Variable>, seen: &mut BTreeSet<u64>) {
            match term {
                IntegerTerm::Constant(_) => {}
                IntegerTerm::Variable(variable) => {
                    variables.insert(*variable);
                }
                IntegerTerm::Machine(value) => {
                    crate::kernel::reasoning::variable_collection::collect_bitvector_variables(
                        value.value(),
                        variables,
                    )
                }
                IntegerTerm::PureFunctionApplication(_application) => {
                    crate::kernel::reasoning::variable_collection::collect_integer_variables(
                        term, variables,
                    );
                }
                IntegerTerm::AlgebraicMatch { .. } | IntegerTerm::If { .. } => {
                    crate::kernel::reasoning::variable_collection::collect_integer_variables(
                        term, variables,
                    );
                }
                IntegerTerm::RangeFold {
                    index,
                    initial,
                    accumulator,
                    item,
                    body,
                } => {
                    variables.insert(*accumulator);
                    variables.insert(*item);
                    visit_shared(initial, variables, seen);
                    visit_shared(body, variables, seen);
                    if let IntegerRangeFoldIndex::Int32 { start, end } = index {
                        crate::kernel::reasoning::variable_collection::collect_bitvector_variables(
                            start.value(),
                            variables,
                        );
                        crate::kernel::reasoning::variable_collection::collect_bitvector_variables(
                            end.value(),
                            variables,
                        );
                    }
                }
                IntegerTerm::Negate(value) => visit_shared(value, variables, seen),
                crate::kernel::binary_integer_term!(left, right) => {
                    visit_shared(left, variables, seen);
                    visit_shared(right, variables, seen);
                }
            }
        }
        fn visit_shared(
            term: &SharedIntegerTerm,
            variables: &mut BTreeSet<Variable>,
            seen: &mut BTreeSet<u64>,
        ) {
            if seen.insert(term.id()) {
                visit(term.as_ref(), variables, seen);
            }
        }
        visit(self, &mut variables, &mut BTreeSet::new());
        variables.into_iter().next_back()
    }
    /// This term read through its root observation's value relations
    /// (rule W, [`SharedMachineIntegerTerm::value_reading`]): the reading of
    /// a machine observation that has one, and the term itself otherwise.
    /// O(1) after the observation's first reading.
    pub fn value_read(&self) -> &IntegerTerm {
        match self {
            Self::Machine(machine) => machine.value_reading().unwrap_or(self),
            _ => self,
        }
    }

    #[track_caller]
    pub fn from_machine(ty: MachineIntegerType, value: MachineTerm) -> Option<Self> {
        if ty.format().bits() == 128 && !ty.accepts_wide_term(&value) {
            return None;
        }
        {
            use crate::kernel::machine_integer::format_audit as audit;
            if audit::is_sign_free_word_operator(&value) {
                if ty == MachineIntegerType::UInt32 {
                    audit::record(
                        audit::WordIdentity::UInt32OperatorAtInt32,
                        std::panic::Location::caller(),
                    );
                } else if ty.format().bits() < 32 {
                    audit::record(
                        audit::WordIdentity::NarrowValueAsWord,
                        std::panic::Location::caller(),
                    );
                }
            }
        }
        // A constant's observation is its value (kept: a literal has no
        // structure an Integer constant loses).
        if let Some(constant) = ty.constant_from_term(&value) {
            return Some(Self::constant(constant.to_integer()));
        }
        if is_machine_constant(&value) {
            return None;
        }
        // The observation is built as written (lowering is structural):
        // `to_integer(x as int32)` keeps its widening and an observation of
        // σ keeps σ. The value relations between such an observation and
        // its operand's (rule W) are read by reasoning through
        // `SharedMachineIntegerTerm::value_reading`, not folded here. The
        // reading also decides which observations are well-formed, so an
        // observation is built exactly when its reading exists.
        if let ValueReading::Constant(constant) = machine_value_reading(ty, &value)? {
            return Some(Self::constant(constant));
        }
        // A conversion into a type `ty` contains, observed at `ty`, is
        // observed at its own type: the value is that type's, and the
        // observation names it at its own format (kept: an observation type
        // wider than the value's format is the caller's, not structure the
        // source wrote, and the conversion itself is retained).
        match &value {
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                to: destination,
                ..
            } if *destination != ty
                && ty.format().bits() <= 32
                && ty.format().contains(destination.format()) =>
            {
                Self::from_machine(*destination, value)
            }
            _ => Some(Self::Machine(SharedMachineIntegerTerm::intern(ty, value))),
        }
    }

    fn shallow_key(&self) -> IntegerShallowKey {
        match self {
            Self::Constant(value) => IntegerShallowKey::Constant(value.clone()),
            Self::Variable(variable) => IntegerShallowKey::Variable(*variable),
            Self::Machine(value) => IntegerShallowKey::Machine(value.id()),
            Self::Negate(value) => IntegerShallowKey::Negate(value.id()),
            Self::Add(left, right) => IntegerShallowKey::Add(left.id(), right.id()),
            Self::Subtract(left, right) => IntegerShallowKey::Subtract(left.id(), right.id()),
            Self::Multiply(left, right) => IntegerShallowKey::Multiply(left.id(), right.id()),
            Self::TruncatingQuotient(left, right) => {
                IntegerShallowKey::TruncatingQuotient(left.id(), right.id())
            }
            Self::TruncatingRemainder(left, right) => {
                IntegerShallowKey::TruncatingRemainder(left.id(), right.id())
            }
            Self::PureFunctionApplication(application) => {
                IntegerShallowKey::PureFunctionApplication(application.id())
            }
            Self::AlgebraicMatch { scrutinee, arms } => IntegerShallowKey::AlgebraicMatch {
                scrutinee: scrutinee.clone(),
                arms: arms.clone(),
            },
            Self::If {
                condition,
                then_term,
                else_term,
            } => IntegerShallowKey::If(condition.clone(), then_term.id(), else_term.id()),
            Self::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => IntegerShallowKey::RangeFold(
                index.clone(),
                initial.id(),
                *accumulator,
                *item,
                body.id(),
            ),
        }
    }
}

/// A value reading of a machine observation: an Integer constant, or the
/// observation at `.0` of the operand `.1`, borrowed from the observed term.
pub(crate) enum ValueReading<'a> {
    Constant(BigInt),
    Observation(MachineIntegerType, &'a MachineTerm),
}

fn is_machine_constant(value: &MachineTerm) -> bool {
    matches!(value, MachineTerm::Constant { .. })
}

/// The value relations of an Integer observation of a conversion (rule W),
/// read through at most a σ, a retyping and a widening chain, each strictly
/// narrowing or removing one conversion, so the walk is bounded by the
/// closed set of machine widths:
/// - an `int32` or `uint32` observation reads its operand's 32 bits, which
///   σ keeps: `to_integer` of σ(x) at either format is `x` read there;
/// - a conversion's result is a value of its destination type, and a wider
///   type that contains that type observes the same value in it;
/// - a widening preserves its operand's value: `to_integer(widen(v))` is
///   `to_integer(v)`.
///
/// `None` for an observation no reading supports (a conversion's result
/// observed at a type that does not contain its destination).
pub(crate) fn machine_value_reading(
    ty: MachineIntegerType,
    value: &MachineTerm,
) -> Option<ValueReading<'_>> {
    let mut value = value;
    if matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32) {
        // Rule W: σ keeps its operand's 32 bits, so σ(x) observed at
        // either 32-bit format is `x` read there. σ of σ is kept as
        // written, so each σ is read through in turn: the walk is the
        // written chain.
        while let Some((_, operand)) = value.sign_cast32_operand() {
            value = operand;
        }
    }
    match value {
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            to: destination,
            ..
        } if *destination != ty
            && ty.format().bits() <= 32
            && ty.format().contains(destination.format()) =>
        {
            return machine_value_reading(*destination, value);
        }
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            to: destination,
            ..
        } if *destination != ty => {
            return None;
        }
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: source,
            value: operand,
            ..
        } if ty.format().bits() > source.format().bits()
            && ty.format().contains(source.format()) =>
        {
            return machine_value_reading(*source, operand);
        }
        // A value-preserving 32-to-64-bit extension node, the spelling C
        // lowering builds, is read as its operand like the generic widening.
        cast_term!(Int64From32, operand) if ty == MachineIntegerType::Int64 => {
            return machine_value_reading(MachineIntegerType::Int32, operand);
        }
        cast_term!(Int64FromUInt32, operand) if ty == MachineIntegerType::Int64 => {
            return machine_value_reading(MachineIntegerType::UInt32, operand);
        }
        cast_term!(UInt64From32, operand) if ty == MachineIntegerType::UInt64 => {
            return machine_value_reading(MachineIntegerType::UInt32, operand);
        }
        _ => {}
    }
    if is_machine_constant(value) {
        ty.constant_from_term(value)
            .map(|constant| ValueReading::Constant(constant.to_integer()))
    } else {
        Some(ValueReading::Observation(ty, value))
    }
}

struct IntegerInterner {
    next_id: u64,
    nodes: crate::id_hash::U64Map<Vec<(IntegerShallowKey, Weak<SharedIntegerNode>)>>,
    cleanup_queue: VecDeque<(u64, usize)>,
}

static INTEGER_INTERNER: OnceLock<Mutex<IntegerInterner>> = OnceLock::new();

fn integer_interner() -> &'static Mutex<IntegerInterner> {
    INTEGER_INTERNER.get_or_init(|| {
        Mutex::new(IntegerInterner {
            next_id: 0,
            nodes: Default::default(),
            cleanup_queue: VecDeque::new(),
        })
    })
}

impl IntegerInterner {
    fn intern(&mut self, term: IntegerTerm) -> SharedIntegerTerm {
        for _ in 0..8 {
            let Some((fingerprint, pointer)) = self.cleanup_queue.pop_front() else {
                break;
            };
            if let Some(bucket) = self.nodes.get_mut(&fingerprint) {
                if bucket
                    .iter()
                    .any(|(_, node)| node.as_ptr() as usize == pointer && node.strong_count() != 0)
                {
                    self.cleanup_queue.push_back((fingerprint, pointer));
                }
                bucket.retain(|(_, node)| {
                    node.as_ptr() as usize != pointer || node.strong_count() != 0
                });
                if bucket.is_empty() {
                    self.nodes.remove(&fingerprint);
                }
            }
        }
        let key = term.shallow_key();
        let fingerprint = integer_key_fingerprint(&key);
        if let Some(bucket) = self.nodes.get(&fingerprint) {
            for (candidate, node) in bucket {
                if candidate == &key
                    && let Some(node) = node.upgrade()
                {
                    return SharedIntegerTerm(node);
                }
            }
        }
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .expect("mathematical Integer node identity exhausted");
        let literal_arithmetic = match &term {
            IntegerTerm::Constant(_) => true,
            IntegerTerm::Negate(child) => child.is_literal_arithmetic(),
            IntegerTerm::Add(left, right)
            | IntegerTerm::Subtract(left, right)
            | IntegerTerm::Multiply(left, right)
            | IntegerTerm::TruncatingQuotient(left, right)
            | IntegerTerm::TruncatingRemainder(left, right) => {
                left.is_literal_arithmetic() && right.is_literal_arithmetic()
            }
            _ => false,
        };
        let node = Arc::new(SharedIntegerNode {
            id,
            term,
            literal_arithmetic,
            kernel_term: OnceLock::new(),
            read_through: OnceLock::new(),
        });
        self.nodes
            .entry(fingerprint)
            .or_default()
            .push((key, Arc::downgrade(&node)));
        self.cleanup_queue
            .push_back((fingerprint, Arc::as_ptr(&node) as usize));
        SharedIntegerTerm(node)
    }
}

fn integer_key_fingerprint(key: &IntegerShallowKey) -> u64 {
    let mut hasher = crate::id_hash::FingerprintHasher::default();
    key.hash(&mut hasher);
    hasher.finish()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum IntegerComparisonOperator {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Equal,
    NotEqual,
}

impl IntegerTerm {
    pub fn var(variable: Variable) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self::Variable(variable)
    }

    pub fn constant(value: BigInt) -> Self {
        charge_integer_bits(&value);
        Self::Constant(value)
    }

    pub fn constant_i64(value: i64) -> Self {
        Self::Constant(BigInt::from(value))
    }

    pub fn parse_constant(value: &str) -> Option<Self> {
        BigInt::from_str(value).ok().map(Self::constant)
    }

    pub(crate) fn algebraic_match(
        scrutinee: AlgebraicTerm,
        arms: Vec<AlgebraicIntegerMatchArm>,
    ) -> Self {
        let native = Self::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms,
        };
        let matched =
            crate::kernel::KernelMatch::import_integer(&mut KernelTermImport::default(), &native)
                .expect("Integer match producer");
        // The path result still has a shallow native Integer reading. Arm
        // bodies retain their common handles across this explicit boundary.
        KernelTermExport::default()
            .integer(&matched.into_term())
            .expect("Integer match result reading")
            .as_ref()
            .clone()
    }

    pub fn range_fold(
        index: IntegerRangeFoldIndex,
        initial: Self,
        accumulator: Variable,
        item: Variable,
        body: Self,
    ) -> Self {
        let native = Self::RangeFold {
            index,
            initial: SharedIntegerTerm::intern(initial),
            accumulator,
            item,
            body: SharedIntegerTerm::intern(body),
        };
        let fold = KernelFold::import_integer(&mut KernelTermImport::default(), &native)
            .expect("Integer fold producer");
        let root = fold.into_term();
        // SpecIntegerPath still returns the native Integer carrier. This is
        // one shallow root reading; its children retain their common handles.
        KernelTermExport::default()
            .integer(&root)
            .expect("Integer fold result reading")
            .as_ref()
            .clone()
    }

    /// Apply the checked empty-range or one-element fold law when both
    /// endpoints are concrete. Symbolic and reversed ranges remain opaque;
    /// this helper never enumerates a range.
    #[cfg(test)]
    pub(crate) fn range_fold_empty_or_step(
        index: &IntegerRangeFoldIndex,
        initial: &Self,
        accumulator: Variable,
        item: Variable,
        body: &Self,
    ) -> Result<Option<Self>, crate::kernel::reasoning::IntegerPureSubstitutionError> {
        if matches!(index, IntegerRangeFoldIndex::Integer { .. }) && accumulator == item {
            return Err(crate::kernel::reasoning::IntegerPureSubstitutionError::UnsupportedCarrier);
        }
        let (start, end) = match index {
            IntegerRangeFoldIndex::Int32 { start, end } => (
                match start.value() {
                    bits32_constant!(value) => Some(i64::from(constant_u32(*value) as i32)),
                    _ => None,
                },
                match end.value() {
                    bits32_constant!(value) => Some(i64::from(constant_u32(*value) as i32)),
                    _ => None,
                },
            ),
            IntegerRangeFoldIndex::UInt64 { start, end } => {
                let constant = |endpoint: &SharedIntegerRangeEndpoint| {
                    endpoint
                        .value()
                        .uint64_as_const()
                        .and_then(|value| i64::try_from(value).ok())
                };
                (constant(start), constant(end))
            }
            IntegerRangeFoldIndex::Integer { start, end } => (
                start.as_const().and_then(|value| value.to_i64()),
                end.as_const().and_then(|value| value.to_i64()),
            ),
        };
        let (Some(start), Some(end)) = (start, end) else {
            return Ok(None);
        };
        if start >= end {
            return Ok(Some(initial.clone()));
        }
        if end == start + 1 {
            return Ok(Some(
                crate::kernel::reasoning::instantiate_integer_range_fold_step(
                    body,
                    accumulator,
                    initial,
                    item,
                    &Self::constant_i64(start),
                    index.machine_item_type(),
                )?,
            ));
        }
        Ok(None)
    }

    /// `if condition { then_term } else { else_term }`: one branch when the
    /// condition is a constant or both branches are the same term, as
    /// `AlgebraicTerm::if_then_else` builds an algebraic conditional.
    pub(crate) fn if_then_else(condition: ConditionTerm, then_term: Self, else_term: Self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match condition {
            ConditionTerm::Constant(true) => then_term,
            ConditionTerm::Constant(false) => else_term,
            condition => {
                let then_term = SharedIntegerTerm::intern(then_term);
                let else_term = SharedIntegerTerm::intern(else_term);
                if then_term == else_term {
                    return then_term.as_ref().clone();
                }
                Self::If {
                    condition: Box::new(condition),
                    then_term,
                    else_term,
                }
            }
        }
    }

    pub fn as_const(&self) -> Option<&BigInt> {
        match self {
            Self::Constant(value) => Some(value),
            _ => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn negate(value: Self) -> Self {
        match value {
            Self::Constant(value) => {
                charge_integer_bits(&value);
                Self::Constant(-value)
            }
            Self::Negate(inner) => inner.as_ref().clone(),
            value => Self::Negate(SharedIntegerTerm::intern(value)),
        }
    }

    pub(crate) fn add(left: Self, right: Self) -> Self {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            charge_binary_bits(left, right);
            return Self::Constant(left + right);
        }
        if left.as_const().is_some_and(Zero::is_zero) {
            return right;
        }
        if right.as_const().is_some_and(Zero::is_zero) {
            return left;
        }
        Self::Add(
            SharedIntegerTerm::intern(left),
            SharedIntegerTerm::intern(right),
        )
    }

    pub(crate) fn subtract(left: Self, right: Self) -> Self {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            charge_binary_bits(left, right);
            return Self::Constant(left - right);
        }
        if right.as_const().is_some_and(Zero::is_zero) {
            return left;
        }
        Self::Subtract(
            SharedIntegerTerm::intern(left),
            SharedIntegerTerm::intern(right),
        )
    }

    pub(crate) fn truncating_quotient(left: Self, right: Self) -> Self {
        Self::truncating_division(left, right, false)
    }

    pub(crate) fn truncating_remainder(left: Self, right: Self) -> Self {
        Self::truncating_division(left, right, true)
    }

    fn truncating_division(left: Self, right: Self, remainder: bool) -> Self {
        if let (Self::Constant(a), Self::Constant(b)) = (&left, &right)
            && !b.is_zero()
        {
            // Charge before arbitrary precision division. Native wide inputs
            // are bounded, but these shared representation nodes are not.
            charge_multiply_bits(a, b);
            return Self::Constant(if remainder { a % b } else { a / b });
        }
        // Do not cancel x/x or simplify 0/x before execution's zero guard.
        let left = SharedIntegerTerm::intern(left);
        let right = SharedIntegerTerm::intern(right);
        if remainder {
            Self::TruncatingRemainder(left, right)
        } else {
            Self::TruncatingQuotient(left, right)
        }
    }

    pub(crate) fn multiply(left: Self, right: Self) -> Self {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            charge_multiply_bits(left, right);
            return Self::Constant(left * right);
        }
        if left.as_const().is_some_and(Zero::is_zero) || right.as_const().is_some_and(Zero::is_zero)
        {
            return Self::Constant(BigInt::zero());
        }
        if left.as_const().is_some_and(One::is_one) {
            return right;
        }
        if right.as_const().is_some_and(One::is_one) {
            return left;
        }
        Self::Multiply(
            SharedIntegerTerm::intern(left),
            SharedIntegerTerm::intern(right),
        )
    }
}

impl From<i64> for IntegerTerm {
    fn from(value: i64) -> Self {
        Self::constant_i64(value)
    }
}

impl fmt::Display for IntegerTerm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut seen = std::collections::BTreeSet::new();
        fmt_integer_term(self, formatter, &mut seen)
    }
}

fn fmt_integer_term(
    term: &IntegerTerm,
    formatter: &mut fmt::Formatter<'_>,
    seen: &mut std::collections::BTreeSet<u64>,
) -> fmt::Result {
    match term {
        IntegerTerm::Constant(value) => write!(formatter, "{value}"),
        IntegerTerm::Variable(variable) => write!(formatter, "i{}", variable.0),
        IntegerTerm::Machine(value) => write!(formatter, "machine_integer#{}", value.id()),
        IntegerTerm::Negate(value) => {
            write!(formatter, "(-")?;
            fmt_integer_shared(value, formatter, seen)?;
            write!(formatter, ")")
        }
        IntegerTerm::Add(left, right) => {
            write!(formatter, "(")?;
            fmt_integer_shared(left, formatter, seen)?;
            write!(formatter, " + ")?;
            fmt_integer_shared(right, formatter, seen)?;
            write!(formatter, ")")
        }
        IntegerTerm::Subtract(left, right) => {
            write!(formatter, "(")?;
            fmt_integer_shared(left, formatter, seen)?;
            write!(formatter, " - ")?;
            fmt_integer_shared(right, formatter, seen)?;
            write!(formatter, ")")
        }
        IntegerTerm::Multiply(left, right) => {
            write!(formatter, "(")?;
            fmt_integer_shared(left, formatter, seen)?;
            write!(formatter, " * ")?;
            fmt_integer_shared(right, formatter, seen)?;
            write!(formatter, ")")
        }
        IntegerTerm::TruncatingQuotient(left, right)
        | IntegerTerm::TruncatingRemainder(left, right) => {
            let name = if matches!(term, IntegerTerm::TruncatingQuotient(_, _)) {
                "truncating_quotient"
            } else {
                "truncating_remainder"
            };
            write!(formatter, "{name}(")?;
            fmt_integer_shared(left, formatter, seen)?;
            write!(formatter, ", ")?;
            fmt_integer_shared(right, formatter, seen)?;
            write!(formatter, ")")
        }
        IntegerTerm::PureFunctionApplication(application) => {
            let name = application.name();
            let arguments = application.arguments();
            write!(formatter, "{name}(")?;
            for (index, argument) in arguments.iter().enumerate() {
                if index != 0 {
                    write!(formatter, ", ")?;
                }
                write!(formatter, "{argument:?}")?;
            }
            write!(formatter, ")")
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            write!(formatter, "match {:?} {{", scrutinee)?;
            for arm in arms {
                write!(formatter, " {} => ", arm.variant)?;
                fmt_integer_shared(&arm.body, formatter, seen)?;
                write!(formatter, ",")?;
            }
            write!(formatter, " }}")
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            write!(formatter, "if {condition:?} {{ ")?;
            fmt_integer_shared(then_term, formatter, seen)?;
            write!(formatter, " }} else {{ ")?;
            fmt_integer_shared(else_term, formatter, seen)?;
            write!(formatter, " }}")
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            write!(formatter, "fold({index:?}; ")?;
            fmt_integer_shared(initial, formatter, seen)?;
            write!(formatter, ", i{} / i{} => ", accumulator.0, item.0)?;
            fmt_integer_shared(body, formatter, seen)?;
            write!(formatter, ")")
        }
    }
}

fn fmt_integer_shared(
    term: &SharedIntegerTerm,
    formatter: &mut fmt::Formatter<'_>,
    seen: &mut std::collections::BTreeSet<u64>,
) -> fmt::Result {
    if !seen.insert(term.id()) {
        return write!(formatter, "#{}", term.id());
    }
    fmt_integer_term(term.as_ref(), formatter, seen)
}

impl ConditionTerm {
    pub(crate) fn integer_less_than(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left < right)
            }
            _ => Self::IntegerLessThan(left.into(), right.into()),
        }
    }

    pub(crate) fn integer_less_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left <= right)
            }
            _ => Self::IntegerLessEqual(left.into(), right.into()),
        }
    }

    pub(crate) fn integer_greater_than(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left > right)
            }
            _ => Self::IntegerGreaterThan(left.into(), right.into()),
        }
    }

    pub(crate) fn integer_greater_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left >= right)
            }
            _ => Self::IntegerGreaterEqual(left.into(), right.into()),
        }
    }

    pub(crate) fn integer_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left == right)
            }
            _ => Self::IntegerEqual(left.into(), right.into()),
        }
    }

    pub(crate) fn integer_not_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left != right)
            }
            _ => Self::IntegerNotEqual(left.into(), right.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn boxed_observation_imports_are_session_local_and_released_on_reset() {
        let value = MachineTerm::Binary {
            format: MachineIntegerType::Int64,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(Variable(953000))),
            right: Box::new(MachineTerm::int64_constant(1)),
        };
        let mut costs = Vec::new();
        let mut previous = Weak::<SharedMachineIntegerNode>::new();
        for _ in 0..3 {
            let _session = crate::kernel::VerificationSession::enter();
            assert!(previous.upgrade().is_none());
            let (observation, work) = crate::instrumentation::measure_deterministic_work(|| {
                SharedMachineIntegerTerm::intern(MachineIntegerType::Int64, value.clone())
            });
            assert_eq!(observation.value(), &value);
            let id = observation.id();
            previous = Arc::downgrade(&observation.0);
            drop(observation);
            // Dropping a caller must not make later imports in this session
            // depend on the weak interner's cleanup order.
            assert!(previous.upgrade().is_some());
            assert_eq!(
                SharedMachineIntegerTerm::intern(MachineIntegerType::Int64, value.clone()).id(),
                id
            );
            costs.push(work);
        }
        assert!(costs[0] > 0);
        assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
        clear_machine_observation_memo();
        assert!(previous.upgrade().is_none());
    }

    fn shared_node_count(root: &SharedIntegerTerm) -> usize {
        let mut pending = vec![root.clone()];
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node.id()) {
                continue;
            }
            match node.as_ref() {
                IntegerTerm::Constant(_)
                | IntegerTerm::Variable(_)
                | IntegerTerm::Machine(_)
                | IntegerTerm::PureFunctionApplication { .. }
                | IntegerTerm::AlgebraicMatch { .. } => {}
                IntegerTerm::If {
                    then_term,
                    else_term,
                    ..
                } => {
                    pending.push(then_term.clone());
                    pending.push(else_term.clone());
                }
                IntegerTerm::Negate(value) => pending.push(value.clone()),
                crate::kernel::binary_integer_term!(left, right) => {
                    pending.push(left.clone());
                    pending.push(right.clone());
                }
                IntegerTerm::RangeFold {
                    index,
                    initial,
                    body,
                    ..
                } => {
                    if let IntegerRangeFoldIndex::Integer { start, end } = index {
                        pending.push(start.clone());
                        pending.push(end.clone());
                    }
                    pending.push(initial.clone());
                    pending.push(body.clone());
                }
            }
        }
        seen.len()
    }

    #[test]
    fn opaque_application_alias_chain_stays_shallow() {
        for depth in [8usize, 16, 32, 64] {
            let mut value = IntegerTerm::var(Variable(1));
            for _ in 0..depth {
                let argument = PureFunctionArgument::Integer(value.clone().into());
                value = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "successor".to_string(),
                    vec![argument],
                ));
            }
            assert!(shared_node_count(&value.into()) <= depth + 1);
        }
    }

    #[test]
    fn application_cleanup_revisits_live_entries_and_releases_dead_arguments() {
        let mut interner = PureApplicationInterner {
            buckets: HashMap::new(),
            cleanup: VecDeque::new(),
            next_id: 0,
        };
        let child: SharedIntegerTerm = IntegerTerm::var(Variable(790_100)).into();
        let weak_child = Arc::downgrade(&child.0);
        let parent = interner.intern("parent".into(), vec![PureFunctionArgument::Integer(child)]);
        let parent_id = parent.id();
        for _ in 0..16 {
            interner.intern("noise".into(), vec![]);
        }
        assert_eq!(
            interner
                .intern("parent".into(), parent.arguments().to_vec())
                .id(),
            parent_id
        );
        assert!(weak_child.upgrade().is_some());
        drop(parent);
        for _ in 0..16 {
            interner.intern("noise".into(), vec![]);
        }
        assert!(
            weak_child.upgrade().is_none(),
            "dead application key retained its argument DAG"
        );
        assert!(interner.intern("later".into(), vec![]).id() > parent_id);
    }

    #[test]
    fn integer_function_aliases_keep_shallow_application_identity() {
        for depth in [8usize, 16, 32, 64] {
            let mut value: SharedIntegerTerm = IntegerTerm::var(Variable(71_000)).into();
            for _ in 0..depth {
                let application = SharedPureApplication::intern(
                    "successor".to_string(),
                    vec![PureFunctionArgument::Integer(value.clone())],
                );
                value = IntegerTerm::PureFunctionApplication(application).into();
            }
            let duplicate = SharedPureApplication::intern(
                "successor".to_string(),
                vec![PureFunctionArgument::Integer(value.clone())],
            );
            let duplicate_again = SharedPureApplication::intern(
                "successor".to_string(),
                vec![PureFunctionArgument::Integer(value)],
            );
            assert_eq!(duplicate.id(), duplicate_again.id(), "depth {depth}");
        }
    }

    #[test]
    fn doubling_chain_interns_each_logical_level_once() {
        for depth in [8, 16, 32, 64] {
            let mut term = IntegerTerm::var(Variable(20_000));
            for _ in 0..depth {
                term = IntegerTerm::add(term.clone(), term.clone());
            }
            let shared = SharedIntegerTerm::from(term);
            assert_eq!(shared_node_count(&shared), depth + 1);
            assert_eq!(
                shared.id(),
                SharedIntegerTerm::from(shared.as_ref().clone()).id()
            );
        }
    }

    #[test]
    fn range_fold_checked_empty_and_step_laws_do_not_unroll_ranges() {
        let accumulator = Variable(30_000);
        let item = Variable(30_001);
        let body = IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item));
        let initial = IntegerTerm::constant_i64(4);
        for index in [
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(3)),
                end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(3)),
            },
            IntegerRangeFoldIndex::Integer {
                start: SharedIntegerTerm::from(IntegerTerm::constant_i64(3)),
                end: SharedIntegerTerm::from(IntegerTerm::constant_i64(3)),
            },
        ] {
            assert_eq!(
                IntegerTerm::range_fold_empty_or_step(&index, &initial, accumulator, item, &body,)
                    .unwrap(),
                Some(initial.clone())
            );
        }
        let next = IntegerRangeFoldIndex::Integer {
            start: SharedIntegerTerm::from(IntegerTerm::constant_i64(3)),
            end: SharedIntegerTerm::from(IntegerTerm::constant_i64(4)),
        };
        assert_eq!(
            IntegerTerm::range_fold_empty_or_step(&next, &initial, accumulator, item, &body)
                .unwrap(),
            Some(IntegerTerm::Add(
                IntegerTerm::constant_i64(4).into(),
                IntegerTerm::constant_i64(3).into(),
            ))
        );
        let reversed = IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(4)),
            end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(3)),
        };
        assert_eq!(
            IntegerTerm::range_fold_empty_or_step(&reversed, &initial, accumulator, item, &body,)
                .unwrap(),
            Some(initial)
        );
    }

    #[test]
    fn range_fold_rejects_duplicate_integer_binders_for_checked_steps() {
        let binder = Variable(30_010);
        let index = IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(1).into(),
        };
        let initial = IntegerTerm::constant_i64(0);
        let body = IntegerTerm::var(binder);
        assert_eq!(
            IntegerTerm::range_fold_empty_or_step(&index, &initial, binder, binder, &body),
            Err(crate::kernel::reasoning::IntegerPureSubstitutionError::UnsupportedCarrier)
        );
        assert!(
            crate::kernel::prove_integer_range_fold_append(index, initial, binder, binder, body,)
                .is_none()
        );
    }

    #[test]
    fn range_fold_theorem_laws_keep_exact_guards_and_fold_shapes() {
        let index = IntegerRangeFoldIndex::Integer {
            start: SharedIntegerTerm::from(IntegerTerm::constant_i64(-1)),
            end: SharedIntegerTerm::from(IntegerTerm::constant_i64(7)),
        };
        let body = IntegerTerm::var(Variable(31_000));
        let empty = crate::kernel::prove_integer_range_fold_empty(
            index.clone(),
            IntegerTerm::constant_i64(9),
            Variable(31_000),
            Variable(31_001),
            body.clone(),
        );
        let Proposition::Implies(_, conclusion) = empty.proposition() else {
            unreachable!()
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
            conclusion.as_ref()
        else {
            unreachable!()
        };
        assert!(matches!(left.as_ref(), IntegerTerm::RangeFold { .. }));
        assert!(right.as_const().is_some_and(|value| value == &9.into()));
        let append = crate::kernel::prove_integer_range_fold_append(
            index,
            IntegerTerm::constant_i64(9),
            Variable(31_000),
            Variable(31_001),
            body,
        )
        .expect("well-formed Integer append law");
        let Proposition::Implies(guard, conclusion) = append.proposition() else {
            unreachable!()
        };
        assert!(matches!(guard.as_ref(), Proposition::ConditionIs(_, true)));
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true) =
            conclusion.as_ref()
        else {
            unreachable!()
        };
        let IntegerTerm::RangeFold { initial, .. } = left.as_ref() else {
            unreachable!()
        };
        assert!(initial.as_const().is_some_and(|value| value == &9.into()));
    }

    #[test]
    fn range_fold_over_equal_terms_carries_the_defining_equations_as_premises() {
        let accumulator = Variable(31_100);
        let item = Variable(31_101);
        let start = Variable(31_102);
        let end = Variable(31_103);
        let index = IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(start)),
            end: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(end)),
        };
        let initial = IntegerTerm::constant_i64(0);
        let body = IntegerTerm::var(accumulator);
        let whole = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "counted".to_string(),
            vec![
                crate::kernel::PureFunctionArgument::Value(ProgramValue::Int32(
                    MachineTerm::Variable(start),
                )),
                crate::kernel::PureFunctionArgument::Value(ProgramValue::Int32(
                    MachineTerm::Variable(end),
                )),
            ],
        ));

        // The empty form carries `whole == fold` beside the ordering guard,
        // and concludes over `whole`, not over the fold.
        let empty = crate::kernel::prove_integer_range_fold_over_equal_terms(
            index.clone(),
            initial.clone(),
            accumulator,
            item,
            body.clone(),
            whole.clone(),
            None,
        )
        .expect("the empty form is always statable");
        let Proposition::Implies(guard, conclusion) = empty.proposition() else {
            unreachable!()
        };
        let Proposition::And(defining, ordering) = guard.as_ref() else {
            unreachable!("the empty form carries the defining equation beside its guard")
        };
        assert!(matches!(
            defining.as_ref(),
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(_, _), true)
        ));
        assert!(matches!(
            ordering.as_ref(),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: _,
                    right: _
                },
                true
            )
        ));
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
            conclusion.as_ref()
        else {
            unreachable!()
        };
        assert_eq!(left.as_ref(), &whole);
        assert!(right.as_const().is_some_and(|value| value == &0.into()));

        // The append form is stated at the predecessor endpoint and restates
        // the shorter fold as the same application one endpoint lower.
        let prior = crate::kernel::integer_range_fold_predecessor_application(&whole, 1)
            .expect("the end argument is an int32 value");
        let append = crate::kernel::prove_integer_range_fold_over_equal_terms(
            index,
            initial,
            accumulator,
            item,
            body,
            whole.clone(),
            Some(prior.clone()),
        )
        .expect("the append form is statable at a symbolic endpoint");
        let Proposition::Implies(guard, conclusion) = append.proposition() else {
            unreachable!()
        };
        let mut premises = Vec::new();
        fn flatten<'a>(proposition: &'a Proposition, into: &mut Vec<&'a Proposition>) {
            match proposition {
                Proposition::And(left, right) => {
                    flatten(left, into);
                    flatten(right, into);
                }
                proposition => into.push(proposition),
            }
        }
        flatten(guard, &mut premises);
        let defining = premises
            .iter()
            .filter(|premise| {
                matches!(
                    premise,
                    Proposition::ConditionIs(ConditionTerm::IntegerEqual(_, _), true)
                )
            })
            .count();
        assert_eq!(defining, 2, "both defining equations must be premises");
        assert!(premises.iter().any(|premise| matches!(
            premise,
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true)
                if left.as_ref() == &prior
        )));
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
            conclusion.as_ref()
        else {
            unreachable!()
        };
        assert_eq!(left.as_ref(), &whole);
        // The right-hand side is the body stepped over the predecessor
        // application, so it mentions `prior` and never the shorter fold.
        assert_eq!(right.as_ref(), &prior);
    }

    #[test]
    fn integer_term_substitution_reaches_the_arithmetic_spine_only() {
        let application = SharedIntegerTerm::from(IntegerTerm::PureFunctionApplication(
            SharedPureApplication::intern("counted".to_string(), Vec::new()),
        ));
        let replacement = SharedIntegerTerm::from(IntegerTerm::constant_i64(7));
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
                SharedIntegerTerm::from(IntegerTerm::Add(
                    application.clone(),
                    SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
                )),
            ),
            true,
        );
        let rewritten = crate::kernel::substitute_integer_term_in_proposition(
            &goal,
            &application,
            &replacement,
        )
        .expect("the application occurs on the arithmetic spine");
        let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(_, right), true) = &rewritten
        else {
            unreachable!()
        };
        let IntegerTerm::Add(left, _) = right.as_ref() else {
            unreachable!()
        };
        assert_eq!(left, &replacement);
        // A term the walk never reaches leaves the proposition unchanged, and
        // an absent term reports no rewrite rather than a silent copy.
        let absent = SharedIntegerTerm::from(IntegerTerm::constant_i64(42));
        assert!(
            crate::kernel::substitute_integer_term_in_proposition(&goal, &absent, &replacement)
                .is_none()
        );
    }

    #[test]
    fn range_fold_append_theorem_evaluates_both_sides_for_both_carriers() {
        fn eval_bits(term: &MachineTerm, bits: &BTreeMap<Variable, i64>) -> i64 {
            match term {
                bits32_constant!(value) => constant_u32(*value) as i32 as i64,
                MachineTerm::Variable(variable) => bits[variable],
                binary_term!(Int32, Add, left, right) => {
                    eval_bits(left, bits) + eval_bits(right, bits)
                }
                _ => panic!("test evaluator only needs signed constants, variables, and add"),
            }
        }
        fn eval_integer(
            term: &IntegerTerm,
            integers: &mut BTreeMap<Variable, BigInt>,
            bits: &mut BTreeMap<Variable, i64>,
        ) -> BigInt {
            match term {
                IntegerTerm::Constant(value) => value.clone(),
                IntegerTerm::Variable(variable) => integers[variable].clone(),
                IntegerTerm::Machine(machine) => BigInt::from(eval_bits(machine.value(), bits)),
                IntegerTerm::Add(left, right) => {
                    eval_integer(left, integers, bits) + eval_integer(right, integers, bits)
                }
                IntegerTerm::Subtract(left, right) => {
                    eval_integer(left, integers, bits) - eval_integer(right, integers, bits)
                }
                IntegerTerm::Multiply(left, right) => {
                    eval_integer(left, integers, bits) * eval_integer(right, integers, bits)
                }
                IntegerTerm::TruncatingQuotient(left, right) => {
                    eval_integer(left, integers, bits) / eval_integer(right, integers, bits)
                }
                IntegerTerm::TruncatingRemainder(left, right) => {
                    eval_integer(left, integers, bits) % eval_integer(right, integers, bits)
                }
                IntegerTerm::Negate(value) => -eval_integer(value, integers, bits),
                IntegerTerm::PureFunctionApplication(_) => {
                    unreachable!("the range-fold law test evaluator has no pure-function model")
                }
                IntegerTerm::AlgebraicMatch { .. } => {
                    unreachable!("the range-fold law test evaluator has no match model")
                }
                IntegerTerm::If { .. } => {
                    unreachable!("the range-fold law test evaluator has no condition model")
                }
                IntegerTerm::RangeFold {
                    index,
                    initial,
                    accumulator,
                    item,
                    body,
                } => {
                    let (start, end) = match index {
                        IntegerRangeFoldIndex::Int32 { start, end } => (
                            BigInt::from(eval_bits(start.value(), bits)),
                            BigInt::from(eval_bits(end.value(), bits)),
                        ),
                        IntegerRangeFoldIndex::UInt64 { .. } => {
                            unreachable!("the range-fold law test evaluator has no uint64 model")
                        }
                        IntegerRangeFoldIndex::Integer { start, end } => (
                            eval_integer(start, integers, bits),
                            eval_integer(end, integers, bits),
                        ),
                    };
                    let mut value = eval_integer(initial, integers, bits);
                    let mut current = start;
                    while current < end {
                        let old_accumulator = integers.insert(*accumulator, value.clone());
                        let old_integer_item =
                            if matches!(index, IntegerRangeFoldIndex::Integer { .. }) {
                                Some(integers.insert(*item, current.clone()))
                            } else {
                                None
                            };
                        let old_bit_item = if matches!(index, IntegerRangeFoldIndex::Int32 { .. }) {
                            Some(bits.insert(*item, current.to_i64().unwrap()))
                        } else {
                            None
                        };
                        let next = eval_integer(body, integers, bits);
                        value = next;
                        if let Some(previous) = old_accumulator {
                            integers.insert(*accumulator, previous);
                        } else {
                            integers.remove(accumulator);
                        }
                        if let Some(previous) = old_integer_item {
                            if let Some(previous) = previous {
                                integers.insert(*item, previous);
                            } else {
                                integers.remove(item);
                            }
                        }
                        if let Some(previous) = old_bit_item.flatten() {
                            bits.insert(*item, previous);
                        } else if old_bit_item.is_some() {
                            bits.remove(item);
                        }
                        current += 1;
                    }
                    value
                }
            }
        }
        let accumulator = Variable(32_000);
        let item = Variable(32_001);
        for start in [-2_i64, 0, 2] {
            let end = start + 2;
            let index = IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(
                    start as i32 as u32,
                )),
                end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(end as i32 as u32)),
            };
            let body = IntegerTerm::add(
                IntegerTerm::var(accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(item),
                )),
            );
            let theorem = crate::kernel::prove_integer_range_fold_append(
                index,
                IntegerTerm::constant_i64(7),
                accumulator,
                item,
                body,
            )
            .unwrap();
            let Proposition::Implies(_, conclusion) = theorem.proposition() else {
                unreachable!()
            };
            let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
                conclusion.as_ref()
            else {
                unreachable!()
            };
            assert_eq!(
                eval_integer(left, &mut BTreeMap::new(), &mut BTreeMap::new()),
                eval_integer(right, &mut BTreeMap::new(), &mut BTreeMap::new())
            );
        }
        let huge: BigInt = BigInt::from(1_u64) << 100;
        let index = IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant(huge.clone()).into(),
            end: IntegerTerm::constant(huge + 2).into(),
        };
        let body = IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item));
        let theorem = crate::kernel::prove_integer_range_fold_append(
            index,
            IntegerTerm::constant_i64(7),
            accumulator,
            item,
            body,
        )
        .unwrap();
        let Proposition::Implies(_, conclusion) = theorem.proposition() else {
            unreachable!()
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
            conclusion.as_ref()
        else {
            unreachable!()
        };
        assert_eq!(
            eval_integer(left, &mut BTreeMap::new(), &mut BTreeMap::new()),
            eval_integer(right, &mut BTreeMap::new(), &mut BTreeMap::new())
        );
    }

    #[test]
    fn range_fold_append_keeps_outer_initial_when_item_identity_is_shared() {
        let item = Variable(41_001);
        let accumulator = Variable(41_002);
        let index = IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(2).into(),
        };
        let body = IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item));
        let theorem = crate::kernel::prove_integer_range_fold_append(
            index,
            IntegerTerm::var(item),
            accumulator,
            item,
            body,
        )
        .expect("the concrete two-step range has an append theorem");
        let Proposition::Implies(_, conclusion) = theorem.proposition() else {
            unreachable!()
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true) =
            conclusion.as_ref()
        else {
            unreachable!()
        };
        let IntegerTerm::RangeFold { initial, .. } = left.as_ref() else {
            unreachable!()
        };
        assert_eq!(initial.as_ref(), &IntegerTerm::var(item));
    }

    #[test]
    fn range_fold_keeps_shared_bodies_across_nested_depths() {
        for depth in [8, 16, 32, 64] {
            let shared_body = IntegerTerm::add(
                IntegerTerm::var(Variable(9)),
                IntegerTerm::var(Variable(10)),
            );
            let mut term = IntegerTerm::range_fold(
                IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::var(Variable(8)).into(),
                },
                IntegerTerm::constant_i64(0),
                Variable(9),
                Variable(10),
                shared_body,
            );
            for _ in 1..depth {
                term = IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Integer {
                        start: IntegerTerm::constant_i64(0).into(),
                        end: IntegerTerm::var(Variable(8)).into(),
                    },
                    term.clone(),
                    Variable(9),
                    Variable(10),
                    term,
                );
            }
            let shared = SharedIntegerTerm::from(term);
            assert_eq!(
                shared.id(),
                SharedIntegerTerm::from(shared.as_ref().clone()).id()
            );
        }
    }

    #[test]
    fn typed_machine_observations_are_canonical_but_signedness_is_distinct() {
        let value = MachineTerm::Variable(Variable(77));
        let signed = SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, value.clone());
        let signed_again =
            SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, value.clone());
        let unsigned = SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, value);
        assert_eq!(signed.id(), signed_again.id());
        assert_ne!(signed.id(), unsigned.id());
        assert_eq!(signed.ty(), MachineIntegerType::Int32);
        assert_eq!(signed.value(), signed_again.value());
    }

    #[test]
    fn range_endpoints_retain_machine_interner_identity_while_live() {
        let first = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(17));
        let first_id = first.id();
        for value in 0..32 {
            let _ = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(value));
        }
        let second = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(17));
        assert_eq!(first_id, second.id());
        assert_eq!(first.value(), second.value());
    }

    #[test]
    fn machine_conversion_preserves_width_and_signedness_for_constants() {
        assert_eq!(
            IntegerTerm::from_machine(MachineIntegerType::Int32, MachineTerm::constant(u32::MAX))
                .and_then(|v| v.as_const().cloned()),
            Some(BigInt::from(-1))
        );
        assert_eq!(
            IntegerTerm::from_machine(MachineIntegerType::UInt32, MachineTerm::constant(u32::MAX))
                .and_then(|v| v.as_const().cloned()),
            Some(BigInt::from(u32::MAX))
        );
        assert_eq!(
            IntegerTerm::from_machine(
                MachineIntegerType::UInt64,
                MachineTerm::uint64_constant(u64::MAX)
            )
            .and_then(|v| v.as_const().cloned()),
            Some(BigInt::from(u64::MAX))
        );
        assert!(
            IntegerTerm::from_machine(MachineIntegerType::UInt8, MachineTerm::constant(256))
                .is_none()
        );
        assert!(
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                MachineTerm::int64_constant(i64::MAX)
            )
            .is_none()
        );
    }

    #[test]
    fn arbitrary_precision_constants_and_exact_operations() {
        let wide = BigInt::one() << 256usize;
        let term = IntegerTerm::add(
            IntegerTerm::constant(wide.clone()),
            IntegerTerm::constant_i64(7),
        );
        assert_eq!(term.as_const(), Some(&(wide + 7)));
        assert_eq!(
            IntegerTerm::negate(IntegerTerm::constant_i64(-3)).as_const(),
            Some(&BigInt::from(3))
        );
        assert_eq!(
            IntegerTerm::multiply(IntegerTerm::constant_i64(-6), IntegerTerm::constant_i64(7))
                .as_const(),
            Some(&BigInt::from(-42))
        );
    }

    #[test]
    fn comparison_constructors_fold_only_root_constants() {
        assert_eq!(
            ConditionTerm::integer_less_than(
                IntegerTerm::constant_i64(2),
                IntegerTerm::constant_i64(3)
            ),
            ConditionTerm::Constant(true)
        );
        let x = IntegerTerm::var(Variable(17));
        assert!(matches!(
            ConditionTerm::integer_equal(x.clone(), x),
            ConditionTerm::IntegerEqual(_, _)
        ));
    }

    #[test]
    fn arithmetic_work_scales_with_numeric_bit_length() {
        let (_, small_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::add(IntegerTerm::constant_i64(1), IntegerTerm::constant_i64(2))
        });
        let wide = BigInt::one() << 1024usize;
        let (_, wide_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::add(
                IntegerTerm::constant(wide.clone()),
                IntegerTerm::constant(wide),
            )
        });
        assert!(wide_work > small_work * 100);
    }

    #[test]
    fn truncating_integer_nodes_fold_exactly_with_signed_remainders() {
        use num_traits::Signed;
        let values = [
            BigInt::from(i128::MIN),
            BigInt::from(i128::MAX),
            BigInt::from(u128::MAX),
            BigInt::from(-7),
            BigInt::from(7),
            BigInt::zero(),
        ];
        for a in &values {
            for b in values.iter().filter(|b| !b.is_zero()) {
                let q = IntegerTerm::truncating_quotient(
                    IntegerTerm::constant(a.clone()),
                    IntegerTerm::constant(b.clone()),
                );
                let r = IntegerTerm::truncating_remainder(
                    IntegerTerm::constant(a.clone()),
                    IntegerTerm::constant(b.clone()),
                );
                let q = q.as_const().unwrap();
                let r = r.as_const().unwrap();
                assert_eq!(a, &(q * b + r));
                assert!(r.abs() < b.abs());
                assert!(r.is_zero() || r.sign() == a.sign());
            }
        }
        assert_eq!(
            IntegerTerm::truncating_quotient(
                IntegerTerm::constant_i64(-7),
                IntegerTerm::constant_i64(3)
            )
            .as_const(),
            Some(&BigInt::from(-2))
        );
        assert_eq!(
            IntegerTerm::truncating_remainder(
                IntegerTerm::constant_i64(-7),
                IntegerTerm::constant_i64(3)
            )
            .as_const(),
            Some(&BigInt::from(-1))
        );
        // Representation arithmetic is unbounded: native MIN/-1 overflow is
        // an execution guard, not a property of the mathematical quotient.
        assert_eq!(
            IntegerTerm::truncating_quotient(
                IntegerTerm::constant(BigInt::from(i128::MIN)),
                IntegerTerm::constant_i64(-1)
            )
            .as_const(),
            Some(&(BigInt::one() << 127usize))
        );
    }

    #[test]
    fn truncating_integer_nodes_do_not_cancel_unguarded_divisors() {
        let x = IntegerTerm::var(Variable(81));
        for (a, b) in [
            (x.clone(), x.clone()),
            (IntegerTerm::constant_i64(0), x),
            (IntegerTerm::constant_i64(7), IntegerTerm::constant_i64(0)),
            (IntegerTerm::constant_i64(0), IntegerTerm::constant_i64(0)),
        ] {
            assert!(matches!(
                IntegerTerm::truncating_quotient(a.clone(), b.clone()),
                IntegerTerm::TruncatingQuotient(_, _)
            ));
            assert!(matches!(
                IntegerTerm::truncating_remainder(a, b),
                IntegerTerm::TruncatingRemainder(_, _)
            ));
        }
    }

    #[test]
    fn truncating_integer_congruence_rewrites_both_operands() {
        let x: SharedIntegerTerm = IntegerTerm::var(Variable(82)).into();
        let y: SharedIntegerTerm = IntegerTerm::var(Variable(83)).into();
        for remainder in [false, true] {
            let term = if remainder {
                IntegerTerm::TruncatingRemainder(x.clone(), y.clone())
            } else {
                IntegerTerm::TruncatingQuotient(x.clone(), y.clone())
            };
            let proposition = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(term.into(), IntegerTerm::constant_i64(99).into()),
                true,
            );
            let first = crate::kernel::substitute_integer_term_in_proposition(
                &proposition,
                &x,
                &IntegerTerm::constant_i64(-7).into(),
            )
            .unwrap();
            let rewritten = crate::kernel::substitute_integer_term_in_proposition(
                &first,
                &y,
                &IntegerTerm::constant_i64(3).into(),
            )
            .unwrap();
            let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true) = rewritten
            else {
                unreachable!()
            };
            assert_eq!(
                left.as_const(),
                Some(&BigInt::from(if remainder { -1 } else { -2 }))
            );
            let zero = crate::kernel::substitute_integer_term_in_proposition(
                &first,
                &y,
                &IntegerTerm::constant_i64(0).into(),
            )
            .unwrap();
            let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true) = zero else {
                unreachable!()
            };
            assert!(left.as_const().is_none(), "zero substitution stays opaque");
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/integer/tests.rs");
    }
}

#[cfg(test)]
mod explicit_input_after_lookup_tests {
    use super::*;

    #[test]
    fn native_lookup_keeps_shared_storage_until_a_boxed_input_is_supplied() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let native = MachineTerm::Binary {
            format: ty,
            op: MachineBinaryOp::Multiply,
            left: Box::new(MachineTerm::Variable(Variable(993271))),
            right: Box::new(MachineTerm::Variable(Variable(993272))),
        };
        let root = KernelTermImport::default()
            .machine_arithmetic(ty, &native)
            .unwrap();
        let observation = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        let lookup = SharedMachineIntegerTerm::import_arithmetic(ty, &native).unwrap();
        assert!(lookup == observation);
        assert!(!observation.has_boxed_operand());
        let supplied = SharedMachineIntegerTerm::intern(ty, native.clone());
        assert!(supplied == observation);
        assert!(supplied.has_boxed_operand());
        assert_eq!(supplied.value(), &native);
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }
}
