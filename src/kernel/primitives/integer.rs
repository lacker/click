//! Exact mathematical integer terms.
//!
//! `IntegerTerm` is deliberately separate from `Bitvector32Term`: the latter
//! is also the arena for C machine values and therefore carries machine-width
//! and overflow semantics.  Mathematical integers have no C representation.

use super::*;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::hash_map::DefaultHasher;
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
    /// An opaque pure specification function application.  The body is
    /// exposed only by the checked `unfold` rule.
    PureFunctionApplication(SharedIntegerApplication),
    /// Exhaustive elimination of an algebraic value. Unknown scrutinees stay
    /// symbolic until a checked constructor value permits iota reduction.
    AlgebraicMatch {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicIntegerMatchArm>,
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
}

/// Canonical shallow node for an opaque Integer function application.
#[derive(Clone)]
pub struct SharedIntegerApplication(Arc<SharedIntegerApplicationNode>);

struct SharedIntegerApplicationNode {
    id: u64,
    name: String,
    arguments: Vec<PureFunctionArgument>,
}

struct IntegerApplicationInterner {
    buckets: HashMap<
        u64,
        Vec<(
            String,
            Vec<PureFunctionArgument>,
            Weak<SharedIntegerApplicationNode>,
        )>,
    >,
    cleanup: VecDeque<(u64, usize)>,
    next_id: u64,
}

impl IntegerApplicationInterner {
    fn intern(
        &mut self,
        name: String,
        arguments: Vec<PureFunctionArgument>,
    ) -> SharedIntegerApplication {
        crate::instrumentation::record_deterministic_work(arguments.len().saturating_add(1));
        let mut hasher = DefaultHasher::new();
        name.hash(&mut hasher);
        arguments.hash(&mut hasher);
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
        if let Some(bucket) = self.buckets.get(&key) {
            for (old_name, old_arguments, node) in bucket {
                if old_name == &name
                    && old_arguments == &arguments
                    && let Some(node) = node.upgrade()
                {
                    return SharedIntegerApplication(node);
                }
            }
        }
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .expect("Integer application interner ID exhausted");
        let node = Arc::new(SharedIntegerApplicationNode {
            id,
            name: name.clone(),
            arguments: arguments.clone(),
        });
        self.buckets
            .entry(key)
            .or_default()
            .push((name, arguments, Arc::downgrade(&node)));
        self.cleanup.push_back((key, Arc::as_ptr(&node) as usize));
        SharedIntegerApplication(node)
    }
}

impl SharedIntegerApplication {
    pub(crate) fn intern(name: String, arguments: Vec<PureFunctionArgument>) -> Self {
        static INTERNER: OnceLock<Mutex<IntegerApplicationInterner>> = OnceLock::new();
        INTERNER
            .get_or_init(|| {
                Mutex::new(IntegerApplicationInterner {
                    buckets: HashMap::new(),
                    cleanup: VecDeque::new(),
                    next_id: 0,
                })
            })
            .lock()
            .expect("Integer application interner lock poisoned")
            .intern(name, arguments)
    }
    pub(crate) fn id(&self) -> u64 {
        self.0.id
    }
    pub(crate) fn name(&self) -> &str {
        &self.0.name
    }
    pub(crate) fn arguments(&self) -> &[PureFunctionArgument] {
        &self.0.arguments
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum IntegerRangeFoldIndex {
    Int32 {
        start: SharedIntegerRangeEndpoint,
        end: SharedIntegerRangeEndpoint,
    },
    Integer {
        start: SharedIntegerTerm,
        end: SharedIntegerTerm,
    },
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
    pub fn intern(value: Bitvector32Term) -> Self {
        Self {
            node: SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, value),
        }
    }
    pub fn id(&self) -> u64 {
        self.node.id()
    }
    pub fn value(&self) -> &Bitvector32Term {
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
            Self::PureFunctionApplication(application) => {
                Self::PureFunctionApplication(application.clone())
            }
            Self::AlgebraicMatch { scrutinee, arms } => Self::AlgebraicMatch {
                scrutinee: scrutinee.clone(),
                arms: arms.clone(),
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
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int64,
    UInt64,
}

impl MachineIntegerType {
    pub fn from_c_type(c_type: CType) -> Option<Self> {
        Some(match c_type {
            CType::Int16 => Self::Int16,
            CType::Int32 => Self::Int32,
            CType::UInt8 => Self::UInt8,
            CType::UInt16 => Self::UInt16,
            CType::UInt32 => Self::UInt32,
            CType::Int64 => Self::Int64,
            CType::UInt64 => Self::UInt64,
            _ => return None,
        })
    }

    pub fn c_type(self) -> CType {
        match self {
            Self::Int16 => CType::Int16,
            Self::Int32 => CType::Int32,
            Self::UInt8 => CType::UInt8,
            Self::UInt16 => CType::UInt16,
            Self::UInt32 => CType::UInt32,
            Self::Int64 => CType::Int64,
            Self::UInt64 => CType::UInt64,
        }
    }
}

pub struct SharedMachineIntegerTerm(Arc<SharedMachineIntegerNode>);

struct SharedMachineIntegerNode {
    id: u64,
    ty: MachineIntegerType,
    value: Bitvector32Term,
}

impl Clone for SharedMachineIntegerTerm {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl SharedMachineIntegerTerm {
    pub fn intern(ty: MachineIntegerType, value: Bitvector32Term) -> Self {
        MACHINE_INTEGER_INTERNER
            .get_or_init(|| Mutex::new(MachineIntegerInterner::default()))
            .lock()
            .expect("machine Integer interner lock poisoned")
            .intern(ty, value)
    }
    pub fn id(&self) -> u64 {
        self.0.id
    }
    pub fn ty(&self) -> MachineIntegerType {
        self.0.ty
    }
    pub fn value(&self) -> &Bitvector32Term {
        &self.0.value
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct MachineIntegerKey {
    ty: MachineIntegerType,
    value: Bitvector32Term,
}

#[derive(Default)]
struct MachineIntegerInterner {
    next_id: u64,
    values: HashMap<u64, Vec<(MachineIntegerKey, Weak<SharedMachineIntegerNode>)>>,
    cleanup_queue: VecDeque<(u64, usize)>,
}

static MACHINE_INTEGER_INTERNER: OnceLock<Mutex<MachineIntegerInterner>> = OnceLock::new();

impl MachineIntegerInterner {
    fn intern(
        &mut self,
        ty: MachineIntegerType,
        value: Bitvector32Term,
    ) -> SharedMachineIntegerTerm {
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
        let key = MachineIntegerKey {
            ty,
            value: value.clone(),
        };
        let mut hasher = DefaultHasher::new();
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
        let node = Arc::new(SharedMachineIntegerNode { id, ty, value });
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
}

impl SharedIntegerTerm {
    pub(crate) fn id(&self) -> u64 {
        self.0.id
    }

    pub(crate) fn as_ref(&self) -> &IntegerTerm {
        &self.0.term
    }

    pub(crate) fn intern(term: IntegerTerm) -> Self {
        integer_interner()
            .lock()
            .expect("Integer interner lock poisoned")
            .intern(term)
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
            Self::PureFunctionApplication(application) => formatter
                .debug_struct("PureFunctionApplication")
                .field("id", &application.id())
                .finish(),
            Self::AlgebraicMatch { scrutinee, arms } => formatter
                .debug_struct("AlgebraicMatch")
                .field("scrutinee", scrutinee)
                .field("arms", arms)
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
    PureFunctionApplication(u64),
    AlgebraicMatch {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicIntegerMatchArm>,
    },
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
                IntegerTerm::AlgebraicMatch { .. } => {
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
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right) => {
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
    pub fn from_machine(ty: MachineIntegerType, value: Bitvector32Term) -> Option<Self> {
        let constant = match (&ty, &value) {
            (MachineIntegerType::Int16, Bitvector32Term::Constant(v)) => {
                i16::try_from(*v as i32).ok().map(BigInt::from)
            }
            (MachineIntegerType::Int32, Bitvector32Term::Constant(v)) => {
                Some(BigInt::from(*v as i32))
            }
            (MachineIntegerType::Int64, Bitvector32Term::Int64Constant(v)) => {
                Some(BigInt::from(*v))
            }
            (MachineIntegerType::UInt32, Bitvector32Term::Constant(v)) => Some(BigInt::from(*v)),
            (MachineIntegerType::UInt64, Bitvector32Term::UInt64Constant(v)) => {
                Some(BigInt::from(*v))
            }
            (MachineIntegerType::UInt8, Bitvector32Term::Constant(v))
                if *v <= u32::from(u8::MAX) =>
            {
                Some(BigInt::from(*v))
            }
            (MachineIntegerType::UInt16, Bitvector32Term::Constant(v))
                if *v <= u32::from(u16::MAX) =>
            {
                Some(BigInt::from(*v))
            }
            _ if matches!(
                value,
                Bitvector32Term::Constant(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
            ) =>
            {
                return None;
            }
            _ => return Some(Self::Machine(SharedMachineIntegerTerm::intern(ty, value))),
        };
        constant.map(Self::constant)
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
            Self::PureFunctionApplication(application) => {
                IntegerShallowKey::PureFunctionApplication(application.id())
            }
            Self::AlgebraicMatch { scrutinee, arms } => IntegerShallowKey::AlgebraicMatch {
                scrutinee: scrutinee.clone(),
                arms: arms.clone(),
            },
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

struct IntegerInterner {
    next_id: u64,
    nodes: HashMap<u64, Vec<(IntegerShallowKey, Weak<SharedIntegerNode>)>>,
    cleanup_queue: VecDeque<(u64, usize)>,
}

static INTEGER_INTERNER: OnceLock<Mutex<IntegerInterner>> = OnceLock::new();

fn integer_interner() -> &'static Mutex<IntegerInterner> {
    INTEGER_INTERNER.get_or_init(|| {
        Mutex::new(IntegerInterner {
            next_id: 0,
            nodes: HashMap::new(),
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
        let node = Arc::new(SharedIntegerNode { id, term });
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
    let mut hasher = DefaultHasher::new();
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

    pub fn range_fold(
        index: IntegerRangeFoldIndex,
        initial: Self,
        accumulator: Variable,
        item: Variable,
        body: Self,
    ) -> Self {
        Self::RangeFold {
            index,
            initial: SharedIntegerTerm::intern(initial),
            accumulator,
            item,
            body: SharedIntegerTerm::intern(body),
        }
    }

    /// Apply the checked empty-range or one-element fold law when both
    /// endpoints are concrete. Symbolic and reversed ranges remain opaque;
    /// this helper never enumerates a range.
    #[allow(dead_code)]
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
                    Bitvector32Term::Constant(value) => Some(i64::from(*value as i32)),
                    _ => None,
                },
                match end.value() {
                    Bitvector32Term::Constant(value) => Some(i64::from(*value as i32)),
                    _ => None,
                },
            ),
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
                    matches!(index, IntegerRangeFoldIndex::Int32 { .. }),
                )?,
            ));
        }
        Ok(None)
    }

    pub fn as_const(&self) -> Option<&BigInt> {
        match self {
            Self::Constant(value) => Some(value),
            _ => None,
        }
    }

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
                IntegerTerm::Negate(value) => pending.push(value.clone()),
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right) => {
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
                value = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    "successor".to_string(),
                    vec![argument],
                ));
            }
            assert!(shared_node_count(&value.into()) <= depth + 1);
        }
    }

    #[test]
    fn application_cleanup_revisits_live_entries_and_releases_dead_arguments() {
        let mut interner = IntegerApplicationInterner {
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
                let application = SharedIntegerApplication::intern(
                    "successor".to_string(),
                    vec![PureFunctionArgument::Integer(value.clone())],
                );
                value = IntegerTerm::PureFunctionApplication(application).into();
            }
            let duplicate = SharedIntegerApplication::intern(
                "successor".to_string(),
                vec![PureFunctionArgument::Integer(value.clone())],
            );
            let duplicate_again = SharedIntegerApplication::intern(
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
                start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(3)),
                end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(3)),
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
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(4)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(3)),
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
    fn range_fold_append_theorem_evaluates_both_sides_for_both_carriers() {
        fn eval_bits(term: &Bitvector32Term, bits: &BTreeMap<Variable, i64>) -> i64 {
            match term {
                Bitvector32Term::Constant(value) => *value as i32 as i64,
                Bitvector32Term::Variable(variable) => bits[variable],
                Bitvector32Term::Add(left, right) => eval_bits(left, bits) + eval_bits(right, bits),
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
                IntegerTerm::Negate(value) => -eval_integer(value, integers, bits),
                IntegerTerm::PureFunctionApplication(_) => {
                    unreachable!("the range-fold law test evaluator has no pure-function model")
                }
                IntegerTerm::AlgebraicMatch { .. } => {
                    unreachable!("the range-fold law test evaluator has no match model")
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
                start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    start as i32 as u32,
                )),
                end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    end as i32 as u32,
                )),
            };
            let body = IntegerTerm::add(
                IntegerTerm::var(accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(item),
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
        let value = Bitvector32Term::Variable(Variable(77));
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
        let first = SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(17));
        let first_id = first.id();
        for value in 0..32 {
            let _ = SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(value));
        }
        let second = SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(17));
        assert_eq!(first_id, second.id());
        assert_eq!(first.value(), second.value());
    }

    #[test]
    fn machine_conversion_preserves_width_and_signedness_for_constants() {
        assert_eq!(
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Constant(u32::MAX)
            )
            .and_then(|v| v.as_const().cloned()),
            Some(BigInt::from(-1))
        );
        assert_eq!(
            IntegerTerm::from_machine(
                MachineIntegerType::UInt32,
                Bitvector32Term::Constant(u32::MAX)
            )
            .and_then(|v| v.as_const().cloned()),
            Some(BigInt::from(u32::MAX))
        );
        assert_eq!(
            IntegerTerm::from_machine(
                MachineIntegerType::UInt64,
                Bitvector32Term::UInt64Constant(u64::MAX)
            )
            .and_then(|v| v.as_const().cloned()),
            Some(BigInt::from(u64::MAX))
        );
        assert!(
            IntegerTerm::from_machine(MachineIntegerType::UInt8, Bitvector32Term::Constant(256))
                .is_none()
        );
        assert!(
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Int64Constant(i64::MAX)
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
    fn exact_integer_numeric_work_has_explicit_size_scaling() {
        let mut additions = Vec::new();
        let mut products = Vec::new();
        for bits in [64usize, 128, 256, 512] {
            let magnitude = BigInt::one() << bits;
            let (sum, add_work) = crate::instrumentation::measure_deterministic_work(|| {
                IntegerTerm::add(
                    IntegerTerm::constant(magnitude.clone()),
                    IntegerTerm::constant(-&magnitude - 7),
                )
            });
            assert_eq!(sum.as_const(), Some(&BigInt::from(-7)));
            let (product, product_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    IntegerTerm::multiply(
                        IntegerTerm::constant(magnitude.clone()),
                        IntegerTerm::constant(-&magnitude),
                    )
                });
            assert_eq!(product.as_const(), Some(&-(BigInt::one() << (2 * bits))));
            additions.push(add_work);
            products.push(product_work);
        }
        for pair in additions.windows(2) {
            assert!(pair[1] > pair[0]);
            assert!(
                pair[1] <= 2 * pair[0] + 8,
                "addition charges linear numeric work"
            );
        }
        for pair in products.windows(2) {
            assert!(
                pair[1] > 3 * pair[0],
                "multiplication must not charge only operand lengths"
            );
            assert!(
                pair[1] <= 4 * pair[0] + 8,
                "the conservative product allowance scales by bit products"
            );
        }
    }
}
