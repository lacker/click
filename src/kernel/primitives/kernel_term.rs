//! Shared typed expression nodes. Arithmetic and calls migrate first; the
//! explicitly named Legacy leaf is a lossless boundary for unmigrated sorts.
//! No constructor consults facts, evaluates arithmetic, or unfolds a call.
use super::*;
use crate::kernel::MachineCastSpelling;
mod boolean;
pub(crate) use boolean::BooleanOperandView;
pub use boolean::{KernelBooleanRead, KernelPointerEquality};
// Scoped payloads shared by evaluation, checking, and Surface synthesis.
#[allow(dead_code)]
mod folds;
pub use folds::KernelFold;
pub(crate) use folds::KernelFoldIndex;
mod algebraic;
mod algebraic_call;
mod algebraic_if;
mod algebraic_read;
pub(crate) use algebraic_call::KernelAlgebraicCall;
mod algebraic_equality;
mod float;
mod machine;
pub(crate) use float::FloatOperandView;
pub use float::{KernelFloatCall, KernelFloatType};
#[allow(dead_code)]
mod matches;
pub(crate) use matches::KernelMatchArm;
pub(crate) use matches::{KernelConstructor, KernelMatch};
mod pointer_observations;
mod reads;
pub use reads::KernelMemoryRead;
// Prepared pointer payloads; producer activation follows scoped consumers and spelling.
#[allow(dead_code)]
mod addresses;
#[allow(dead_code)]
mod offsets;
#[allow(dead_code)]
mod pointers;
pub(crate) use addresses::{SharedAddress, SharedAddressBase};
pub use machine::KernelMachineLiteral;
use num_bigint::BigInt;
pub(crate) use offsets::{KernelAddressOffset, SharedAddressOffset};
pub(crate) use pointers::{PointerRewrite, PointerRewriteError, SharedPointer};
use std::collections::{HashMap, VecDeque};
use std::sync::{Mutex, Weak};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum KernelType {
    Bool,
    Integer,
    Program(ProgramType),
    Algebraic(AlgebraicType),
    ArrayRef(ProgramType),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum KernelIntegerOperator {
    Negate,
    Add,
    Subtract,
    Multiply,
    TruncatingQuotient,
    TruncatingRemainder,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum KernelTermNode {
    ThreadHandle(ThreadHandleId),
    /// Scoped range iteration. Only the body is under its two binders.
    Fold(KernelFold),
    Match(KernelMatch),
    Constructor(KernelConstructor),
    AlgebraicCall(KernelAlgebraicCall),
    FloatCall(KernelFloatCall),
    AlgebraicIf {
        arguments: [KernelTerm; 3],
    },
    BoolLiteral(bool),
    BoolRead(KernelBooleanRead),
    AlgebraicRead(KernelMemoryRead),
    FloatRead(KernelMemoryRead),
    FloatCompare {
        format: KernelFloatType,
        operator: ComparisonOperator,
        arguments: [KernelTerm; 2],
    },
    FloatClassify {
        format: KernelFloatType,
        classification: FloatClassification,
        operand: KernelTerm,
    },
    BoolCast {
        destination: MachineIntegerType,
        operand: KernelTerm,
    },
    BoolOverflow {
        format: MachineIntegerType,
        operation: OverflowOperation,
        arguments: [KernelTerm; 2],
    },
    BoolCompare {
        format: MachineIntegerType,
        relation: CompareRelation,
        arguments: [KernelTerm; 2],
    },
    PointerEqual(KernelPointerEquality),
    AddressEqual {
        arguments: [SharedAddress; 2],
    },
    AddressOffsetEqual {
        arguments: [SharedAddressOffset; 2],
    },
    IntegerCompare {
        operator: IntegerComparisonOperator,
        arguments: [KernelTerm; 2],
    },
    AlgebraicEqual {
        arguments: [KernelTerm; 2],
    },
    BoolEqual {
        arguments: [KernelTerm; 2],
    },
    BoolIf {
        arguments: [KernelTerm; 3],
    },
    /// A mathematical conditional with its condition and both branches retained.
    /// Construction is structural; definedness and branch assumptions stay outside.
    IntegerIf {
        arguments: [KernelTerm; 3],
    },
    /// A word selection with a retained Bool guard and two retained word arms.
    /// Branch definedness remains in the evaluator's guarded obligations.
    MachineIf {
        arguments: [KernelTerm; 3],
    },
    /// Explicit native Boolean observation identity; condition imports are structural.
    LegacyBool(KernelLegacyTerm),
    IntegerLiteral(BigInt),
    MachineLiteral(KernelMachineLiteral),
    /// A program-carried abstract value, distinct from a logical algebraic argument.
    ProgramParameter {
        operand: KernelTerm,
    },
    FloatConvert {
        source: ProgramType,
        destination: ProgramType,
        operand: KernelTerm,
    },
    FloatNegate {
        operand: KernelTerm,
    },
    FloatBinary {
        operator: FloatBinaryOperator,
        arguments: [KernelTerm; 2],
    },
    FloatLiteral {
        carrier: MachineIntegerType,
        bits: u128,
    },
    IntegerToMachine {
        destination: MachineIntegerType,
        operand: KernelTerm,
    },
    /// Exact scalar read descriptor. The read is made at `point`;
    /// observation origins and access evidence are not part of this node.
    /// Native addresses remain an explicit input boundary during migration.
    MemoryLoad {
        point: ProgramPoint,
        address: SharedAddress,
        kind: LoadKind,
    },
    /// Complete formed pointer value with prepared address and metadata children.
    Pointer(SharedPointer),
    /// A pointer argument with the point its array is read at.
    ArrayReference {
        point: ProgramPoint,
        pointer: KernelTerm,
        element_type: ProgramType,
    },
    /// Generic call structure plus the complete checked pointer result.
    PointerCall {
        call: KernelTerm,
        value: SharedPointer,
    },
    /// Pointer arithmetic keeps its exact input roots beside the complete
    /// checked result payload. Formation evidence stays on the execution path.
    PointerArithmetic {
        operation: MachineBinaryOp,
        byte_width: u32,
        operands: [KernelTerm; 2],
        value: SharedPointer,
    },
    /// Complete pointer read result and its producer-retained definition.
    /// Access authority and read-over-write evidence remain outside the term.
    PointerRead {
        value: SharedPointer,
        point: ProgramPoint,
        address: SharedAddress,
    },
    /// Address observation retains its exact prepared address and object annotation.
    IntegerAddress {
        address: SharedAddress,
        object_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    MachineObservation {
        format: MachineIntegerType,
        operand: KernelTerm,
    },
    MachineBinary {
        format: MachineIntegerType,
        operator: MachineBinaryOp,
        arguments: [KernelTerm; 2],
    },
    MachineUnary {
        format: MachineIntegerType,
        operator: MachineUnaryOp,
        operand: KernelTerm,
    },
    MachineCast {
        encoding: MachineCastSpelling,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        operand: KernelTerm,
    },
    Variable(Variable),
    IntegerOperation {
        operator: KernelIntegerOperator,
        arguments: Vec<KernelTerm>,
    },
    Call {
        name: String,
        arguments: Vec<KernelTerm>,
    },
    /// Temporary adapter, not a second spelling or equality interpretation.
    Legacy(KernelLegacyTerm),
}

/// An exact unmigrated payload, with identity supplied by its producer.
/// C pointer equality intentionally omits auxiliary qualifiers/evidence, so
/// it cannot be used to select which legacy payload a bridge returns.
#[derive(Clone, Debug)]
pub struct KernelLegacyTerm {
    identity: LegacyIdentity,
    value: PureFunctionArgument,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum LegacyIdentity {
    Machine(u64),
    MachineObservation(SharedMachineIntegerTerm),
    NativeObservation(Box<PureFunctionArgument>),
    ApplicationArgument(SharedPureApplication, usize),
    ExactApplicationArgument {
        application: SharedPureApplication,
        payload: usize,
        index: usize,
    },
    Fresh(u64),
}
impl PartialEq for KernelLegacyTerm {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for KernelLegacyTerm {}
impl Hash for KernelLegacyTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if matches!(self.identity, LegacyIdentity::NativeObservation(_)) {
            // Charge the existing native descriptor boundary, rather than
            // hiding its structural work behind a constant-cost common ID.
            struct Charged<'a, H>(&'a mut H);
            impl<H: Hasher> Hasher for Charged<'_, H> {
                fn finish(&self) -> u64 {
                    self.0.finish()
                }
                fn write(&mut self, bytes: &[u8]) {
                    crate::instrumentation::record_deterministic_work(bytes.len().div_ceil(8));
                    self.0.write(bytes);
                }
            }
            self.identity.hash(&mut Charged(state));
        } else {
            self.identity.hash(state);
        }
    }
}
impl KernelLegacyTerm {
    pub fn value(&self) -> &PureFunctionArgument {
        &self.value
    }
}

/// A produced call already owns its native argument descriptors. Borrow that
/// payload through its application handle instead of constructing a second
/// native call tree when an unmigrated consumer requests the root reading.
#[derive(Default)]
struct MachineLeafCache(std::sync::OnceLock<MachineLeaf>);
enum MachineLeaf {
    Native(MachineTerm),
    Application(SharedPureApplication),
}
impl MachineLeafCache {
    fn get_or_init(&self, build: impl FnOnce() -> MachineTerm) -> &MachineTerm {
        match self.0.get_or_init(|| MachineLeaf::Native(build())) {
            MachineLeaf::Native(value) => value,
            MachineLeaf::Application(application) => application.native_call(),
        }
    }
    fn retain_application(&self, application: &SharedPureApplication) {
        crate::instrumentation::record_deterministic_work(1);
        self.0
            .get_or_init(|| MachineLeaf::Application(application.clone()));
    }
}

struct TermData {
    id: u64,
    key: NodeKey,
    // Temporary reverse bridge. Weak because the old node caches this term.
    integer: Mutex<WeakIntegerTerm>,
    machine_leaf: MachineLeafCache,
    argument_leaf: std::sync::OnceLock<Box<PureFunctionArgument>>,
    word_storage_key:
        std::sync::OnceLock<Option<crate::kernel::execution_value::storage_keys::WordKey>>,
}

struct NodeKeyData {
    fingerprint: u64,
    ty: KernelType,
    node: KernelTermNode,
    shared_machine_operand: bool,
    opaque_observation_boundary: bool,
    machine_conversions: bool,
    machine_reads: bool,
    conditional_machine_rewrites: bool,
    machine_conditionals: bool,
    machine_folds: bool,
    machine_matches: bool,
    machine_constant: Option<KernelMachineLiteral>,
}
#[derive(Clone)]
struct NodeKey(Arc<NodeKeyData>);
impl PartialEq for NodeKey {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.ty == other.0.ty
                && match (&self.0.node, &other.0.node) {
                    (
                        KernelTermNode::MemoryLoad {
                            point: a,
                            address: p,
                            kind: k,
                        },
                        KernelTermNode::MemoryLoad {
                            point: b,
                            address: q,
                            kind: l,
                        },
                    ) => {
                        // The interner is process-wide; states belong to arenas.
                        // Comparing their contents across arenas would walk unrelated
                        // memory while registering one selected read.
                        a.shared_memory().arena_id() == b.shared_memory().arena_id()
                            && p == q
                            && k == l
                    }
                    (
                        KernelTermNode::PointerRead {
                            value: a,
                            point: m,
                            address: p,
                        },
                        KernelTermNode::PointerRead {
                            value: b,
                            point: n,
                            address: q,
                        },
                    ) => {
                        m.shared_memory().arena_id() == n.shared_memory().arena_id()
                            && a == b
                            && p == q
                    }
                    (a, b) => a == b,
                })
    }
}
impl Eq for NodeKey {}
impl Hash for NodeKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl NodeKey {
    fn new(ty: KernelType, node: KernelTermNode) -> Self {
        let mut hash = crate::id_hash::FingerprintHasher::default();
        ty.hash(&mut hash);
        if let KernelTermNode::MemoryLoad { point, .. }
        | KernelTermNode::PointerRead { point, .. } = &node
        {
            point.shared_memory().arena_id().hash(&mut hash);
        }
        node.hash(&mut hash);
        // A fresh legacy identity belongs to its producer. Read observations
        // still have native consumers. Keep conversion payloads containing them
        // outside shared observations until their scoped consumers migrate.
        // Inspect immediate children only; retain the result across growing DAGs.
        let opaque_observation_boundary = match &node {
            KernelTermNode::Constructor(constructor) => constructor
                .fields
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::Match(matched)
                if matches!(ty, KernelType::Program(_) | KernelType::Algebraic(_)) =>
            {
                matched
                    .arguments
                    .iter()
                    .chain(matched.arms.iter().flat_map(|arm| &arm.bindings))
                    .any(KernelTerm::has_opaque_observation_boundary)
            }
            KernelTermNode::Fold(fold) if matches!(ty, KernelType::Program(_)) => fold
                .arguments
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::Pointer(_)
            | KernelTermNode::PointerRead { .. }
            | KernelTermNode::PointerArithmetic { .. }
            | KernelTermNode::PointerCall { .. }
            | KernelTermNode::ArrayReference { .. }
            | KernelTermNode::MemoryLoad { .. }
            | KernelTermNode::IntegerAddress { .. }
            | KernelTermNode::AddressOffsetEqual { .. }
            | KernelTermNode::AddressEqual { .. }
            | KernelTermNode::PointerEqual(_)
            | KernelTermNode::BoolRead(_)
            | KernelTermNode::AlgebraicRead(_)
            | KernelTermNode::FloatRead(_) => true,
            KernelTermNode::Legacy(value) | KernelTermNode::LegacyBool(value) => {
                matches!(
                    value.identity,
                    LegacyIdentity::Fresh(_)
                        | LegacyIdentity::Machine(_)
                        | LegacyIdentity::ExactApplicationArgument { .. }
                )
            }
            KernelTermNode::Call { .. } if matches!(ty, KernelType::Program(ty) if MachineIntegerType::from_program_type(ty).is_some()) => {
                true
            }
            KernelTermNode::FloatCall(call) => call
                .arguments
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::AlgebraicCall(call) => call
                .arguments
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::Call { arguments, .. }
            | KernelTermNode::IntegerOperation { arguments, .. } => arguments
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::MachineBinary { arguments, .. }
            | KernelTermNode::FloatBinary { arguments, .. }
            | KernelTermNode::FloatCompare { arguments, .. }
            | KernelTermNode::BoolOverflow { arguments, .. }
            | KernelTermNode::BoolCompare { arguments, .. }
            | KernelTermNode::IntegerCompare { arguments, .. }
            | KernelTermNode::AlgebraicEqual { arguments }
            | KernelTermNode::BoolEqual { arguments } => arguments
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::BoolIf { arguments } | KernelTermNode::MachineIf { arguments } => {
                arguments
                    .iter()
                    .any(KernelTerm::has_opaque_observation_boundary)
            }
            // Integer conditionals already had retained Integer identity before
            // becoming common nodes. Conversion consumers visit their branches
            // with the source width and current state; keep that boundary.
            KernelTermNode::AlgebraicIf { arguments } => arguments
                .iter()
                .any(KernelTerm::has_opaque_observation_boundary),
            KernelTermNode::IntegerIf { .. } => false,
            KernelTermNode::BoolCast { operand, .. }
            | KernelTermNode::ProgramParameter { operand }
            | KernelTermNode::FloatConvert { operand, .. }
            | KernelTermNode::FloatNegate { operand }
            | KernelTermNode::FloatClassify { operand, .. }
            | KernelTermNode::IntegerToMachine { operand, .. }
            | KernelTermNode::MachineObservation { operand, .. }
            | KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => {
                operand.has_opaque_observation_boundary()
            }
            _ => false,
        };
        // This migration fragment has exact structural identities all the way
        // to its leaves, including explicit conversion roots. Opaque payloads
        // keep their old storage; inspect immediate children only.
        let shared_machine_operand = match &node {
            KernelTermNode::Match(matched) => {
                matches!(&ty, KernelType::Program(c) if MachineIntegerType::from_program_type(*c).is_some())
                    && matched.arguments[1..]
                        .iter()
                        .all(KernelTerm::is_shared_machine_operand)
            }
            KernelTermNode::Fold(fold) => {
                matches!(ty, KernelType::Program(_))
                    && fold
                        .arguments
                        .iter()
                        .all(KernelTerm::is_shared_machine_operand)
            }
            KernelTermNode::Call { .. } => {
                matches!(&ty, KernelType::Program(c) if MachineIntegerType::from_program_type(*c).is_some())
            }
            KernelTermNode::MachineLiteral(_)
            | KernelTermNode::ThreadHandle(_)
            | KernelTermNode::MemoryLoad { .. }
            | KernelTermNode::IntegerAddress { .. } => true,
            KernelTermNode::FloatConvert { destination, .. } => {
                MachineIntegerType::from_program_type(*destination).is_some()
            }
            KernelTermNode::BoolCast { .. } => true,
            KernelTermNode::IntegerToMachine { .. } => !opaque_observation_boundary,
            KernelTermNode::Legacy(value) => matches!(
                value.identity,
                LegacyIdentity::Machine(_) | LegacyIdentity::MachineObservation(_)
            ),
            KernelTermNode::Variable(_) => {
                matches!(&ty, KernelType::Program(c) if MachineIntegerType::from_program_type(*c).is_some())
            }
            KernelTermNode::MachineBinary { arguments, .. } => {
                arguments.iter().all(KernelTerm::is_shared_machine_operand)
            }
            KernelTermNode::MachineIf { arguments } => arguments[1..]
                .iter()
                .all(KernelTerm::is_shared_machine_operand),
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => operand.is_shared_machine_operand(),
            _ => false,
        };
        let machine_conversions = match &node {
            KernelTermNode::IntegerAddress { .. } => true,
            KernelTermNode::Fold(_) | KernelTermNode::Match(_) => shared_machine_operand,
            KernelTermNode::Call { .. } => shared_machine_operand,
            KernelTermNode::MachineIf { .. } => true,
            KernelTermNode::FloatConvert { .. } => shared_machine_operand,
            KernelTermNode::IntegerToMachine { .. } | KernelTermNode::BoolCast { .. } => true,
            KernelTermNode::Legacy(value) => matches!(
                value.identity,
                LegacyIdentity::Machine(_) | LegacyIdentity::MachineObservation(_)
            ),
            KernelTermNode::MachineBinary { arguments, .. } => {
                arguments.iter().any(KernelTerm::has_machine_conversions)
            }
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => operand.has_machine_conversions(),
            _ => false,
        };
        let machine_reads = match &node {
            KernelTermNode::MachineIf { .. } => true,
            KernelTermNode::MemoryLoad { .. } => true,
            KernelTermNode::MachineBinary { arguments, .. } => {
                arguments.iter().any(KernelTerm::has_machine_reads)
            }
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => operand.has_machine_reads(),
            _ => false,
        };
        // Conditional rewriting leaves ordinary arithmetic untouched. Retain
        // this syntax summary so each query skips unchanged shared prefixes.
        let conditional_machine_rewrites = match &node {
            KernelTermNode::Fold(_) | KernelTermNode::Match(_) => shared_machine_operand,
            KernelTermNode::Call { .. } | KernelTermNode::FloatConvert { .. } => {
                shared_machine_operand
            }
            KernelTermNode::MachineIf { .. } => true,
            KernelTermNode::IntegerToMachine { .. }
            | KernelTermNode::MachineCast { .. }
            | KernelTermNode::BoolCast { .. } => true,
            KernelTermNode::MachineBinary {
                operator,
                arguments,
                ..
            } => {
                *operator == MachineBinaryOp::Remainder
                    || arguments
                        .iter()
                        .any(KernelTerm::has_conditional_machine_rewrites)
            }
            KernelTermNode::MachineUnary { operand, .. } => {
                operand.has_conditional_machine_rewrites()
            }
            // Opaque domain leaves can contain conditions (If, folds, calls).
            // Their native walker owns those payloads; do not skip it merely
            // because the surrounding arithmetic now has shared parents.
            KernelTermNode::Legacy(value) => value.machine_operand().is_some(),
            _ => false,
        };
        let machine_conditionals = match &node {
            KernelTermNode::MachineIf { .. } => true,
            KernelTermNode::MachineBinary { arguments, .. } => {
                arguments.iter().any(KernelTerm::has_machine_conditionals)
            }
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => operand.has_machine_conditionals(),
            _ => false,
        };
        let machine_folds = match &node {
            KernelTermNode::Match(matched) => matched.arguments[1..]
                .iter()
                .any(KernelTerm::has_machine_folds),
            KernelTermNode::Fold(_) => shared_machine_operand,
            KernelTermNode::MachineBinary { arguments, .. } => {
                arguments.iter().any(KernelTerm::has_machine_folds)
            }
            KernelTermNode::MachineIf { arguments } => {
                arguments[1..].iter().any(KernelTerm::has_machine_folds)
            }
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => operand.has_machine_folds(),
            _ => false,
        };
        let machine_matches = match &node {
            KernelTermNode::Match(_) => shared_machine_operand,
            KernelTermNode::Fold(fold) => {
                fold.arguments.iter().any(KernelTerm::has_machine_matches)
            }
            KernelTermNode::MachineBinary { arguments, .. } => {
                arguments.iter().any(KernelTerm::has_machine_matches)
            }
            KernelTermNode::MachineIf { arguments } => {
                arguments[1..].iter().any(KernelTerm::has_machine_matches)
            }
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => operand.has_machine_matches(),
            _ => false,
        };
        let machine_constant = machine::constant_reading(&node);
        Self(Arc::new(NodeKeyData {
            machine_constant,
            fingerprint: hash.finish(),
            shared_machine_operand,
            opaque_observation_boundary,
            machine_conversions,
            machine_reads,
            conditional_machine_rewrites,
            machine_conditionals,
            machine_folds,
            machine_matches,
            ty,
            node,
        }))
    }
}

/// Immutable typed term. Identity is structural, never an equality-class id.
/// Migrated children are handles, so hashing and comparing an arithmetic or
/// call node do not walk its DAG. Legacy payload costs remain explicit input.
#[derive(Clone)]
pub struct KernelTerm(Arc<TermData>);

impl std::fmt::Debug for KernelTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KernelTerm")
            .field("id", &self.0.id)
            .field("type", &self.0.key.0.ty)
            .finish()
    }
}
impl PartialEq for KernelTerm {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for KernelTerm {}
impl Hash for KernelTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}

#[derive(Default)]
struct Interner {
    // A `NodeKey` hashes as its precomputed fingerprint.
    terms: HashMap<NodeKey, Weak<TermData>, crate::id_hash::U64BuildHasher>,
    cleanup: VecDeque<NodeKey>,
    next_id: u64,
}
impl Interner {
    fn intern(&mut self, key: NodeKey) -> KernelTerm {
        // Bounded upkeep. A dead parent's key may retain child handles until
        // this queue reaches it, but no whole interner scan is performed.
        for _ in 0..self.cleanup.len().min(8) {
            let key = self.cleanup.pop_front().unwrap();
            if self
                .terms
                .get(&key)
                .is_some_and(|value| value.strong_count() == 0)
            {
                self.terms.remove(&key);
            } else {
                self.cleanup.push_back(key);
            }
        }
        if let Some(existing) = self.terms.get(&key).and_then(Weak::upgrade) {
            return KernelTerm(existing);
        }
        let id = self.next_id;
        self.next_id = id.checked_add(1).expect("kernel term identity exhausted");
        let value = Arc::new(TermData {
            id,
            key: key.clone(),
            integer: Mutex::default(),
            machine_leaf: Default::default(),
            argument_leaf: Default::default(),
            word_storage_key: Default::default(),
        });
        self.terms.insert(key.clone(), Arc::downgrade(&value));
        self.cleanup.push_back(key);
        KernelTerm(value)
    }
}
thread_local! {
    // The bridge links preserve structural identity across sessions, but their
    // use as a shortcut must not depend on an earlier verification's cache.
    static SESSION_INTEGER_BRIDGES: std::cell::RefCell<std::collections::HashSet<u64>> = Default::default();
}

pub(crate) fn clear_integer_bridge_memo() {
    super::integer::clear_machine_observation_memo();
    SESSION_INTEGER_BRIDGES.with(|memo| memo.borrow_mut().clear());
}

impl KernelTerm {
    pub(in crate::kernel) fn word_storage_key(
        &self,
    ) -> Option<&crate::kernel::execution_value::storage_keys::WordKey> {
        self.0
            .word_storage_key
            .get_or_init(|| crate::kernel::execution_value::storage_keys::WordKey::shared(self))
            .as_ref()
    }

    pub(in crate::kernel) fn float_storage_key(
        &self,
    ) -> crate::kernel::execution_value::storage_keys::FloatStorageKey {
        crate::kernel::execution_value::storage_keys::float_for_root(self)
    }
    pub(in crate::kernel) fn condition_storage_key(
        &self,
    ) -> crate::kernel::execution_value::storage_keys::ConditionStorageKey {
        crate::kernel::execution_value::storage_keys::condition_for_root(self)
    }
    /// Selected native program-value output for stored argument/state readers.
    /// Reuse the existing root-owned compatibility slot; cloning or retaining
    /// the stored value never requests this reading.
    pub(crate) fn program_value_native_compat(&self) -> Option<&ProgramValue> {
        if let KernelTermNode::Legacy(legacy) = self.node()
            && let PureFunctionArgument::Value(value) = legacy.value()
        {
            return Some(value);
        }
        if let Some(value) = self
            .pointer_native()
            .or_else(|| self.boolean_native())
            .or_else(|| self.algebraic_native_value())
            .or_else(|| self.float_native_value())
        {
            return Some(value);
        }
        if !matches!(self.ty(), KernelType::Program(_)) {
            return None;
        }
        let PureFunctionArgument::Value(value) = self
            .0
            .argument_leaf
            .get_or_init(|| {
                Box::new(PureFunctionArgument::Value(
                    crate::kernel::ExecutionValue::Shared(self.clone()).into_native(),
                ))
            })
            .as_ref()
        else {
            unreachable!("program value output cache")
        };
        Some(value)
    }

    /// Borrow the selected native Integer output from the existing root slot.
    /// Storage and producer handoffs never request this compatibility reading.
    pub(crate) fn integer_native_compat(&self) -> Option<&IntegerTerm> {
        if self.ty() != &KernelType::Integer {
            return None;
        }
        if let KernelTermNode::Legacy(legacy) = self.node()
            && let PureFunctionArgument::Integer(value) = legacy.value()
        {
            return Some(value);
        }
        let PureFunctionArgument::Integer(value) = self
            .0
            .argument_leaf
            .get_or_init(|| {
                Box::new(PureFunctionArgument::Integer(
                    KernelTermExport::default()
                        .integer(self)
                        .expect("Integer field output"),
                ))
            })
            .as_ref()
        else {
            unreachable!("Integer output cache")
        };
        Some(value)
    }

    #[cfg(test)]
    pub(crate) fn has_cached_native_argument(&self) -> bool {
        self.0.argument_leaf.get().is_some()
    }

    pub(crate) fn id(&self) -> u64 {
        self.0.id
    }

    pub(crate) fn machine_constant_reading(&self) -> Option<&KernelMachineLiteral> {
        self.0.key.0.machine_constant.as_ref()
    }

    pub(crate) fn has_opaque_observation_boundary(&self) -> bool {
        self.0.key.0.opaque_observation_boundary
    }

    /// Reads in the machine arithmetic fragment. Integer conversion payloads
    /// are separate carrier leaves and retain their own scoped traversal.
    pub(crate) fn has_machine_reads(&self) -> bool {
        self.0.key.0.machine_reads
    }

    pub(crate) fn has_machine_conversions(&self) -> bool {
        self.0.key.0.machine_conversions
    }

    pub(crate) fn has_conditional_machine_rewrites(&self) -> bool {
        self.0.key.0.conditional_machine_rewrites
    }

    pub(crate) fn has_machine_conditionals(&self) -> bool {
        self.0.key.0.machine_conditionals
    }

    /// Intrinsic syntax summary, independent of facts and registry state.
    pub(crate) fn has_machine_folds(&self) -> bool {
        self.0.key.0.machine_folds
    }

    pub(crate) fn has_machine_matches(&self) -> bool {
        self.0.key.0.machine_matches
    }

    pub(crate) fn has_machine_control_terms(&self) -> bool {
        self.has_machine_conditionals() || self.has_machine_folds() || self.has_machine_matches()
    }

    pub(crate) fn is_shared_machine_operand(&self) -> bool {
        self.0.key.0.shared_machine_operand
    }

    fn legacy_integer(&self) -> Option<SharedIntegerTerm> {
        self.0
            .integer
            .lock()
            .expect("term bridge poisoned")
            .upgrade()
            .filter(|integer| {
                SESSION_INTEGER_BRIDGES.with(|memo| memo.borrow().contains(&integer.id()))
            })
    }
    fn remember_integer(&self, integer: &SharedIntegerTerm) {
        SESSION_INTEGER_BRIDGES.with(|memo| memo.borrow_mut().insert(integer.id()));
        *self.0.integer.lock().expect("term bridge poisoned") = integer.downgrade();
        // A legacy leaf owns its old value. Caching it on that same value
        // would create a cycle; only genuinely migrated nodes cache both ways.
        if !matches!(self.node(), KernelTermNode::Legacy(_)) {
            integer.remember_kernel_term(self.clone());
        }
    }

    pub(in crate::kernel::primitives) fn intern(ty: KernelType, node: KernelTermNode) -> Self {
        static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
        crate::instrumentation::record_deterministic_work(match &node {
            KernelTermNode::IntegerOperation { arguments, .. } => arguments.len() + 1,
            KernelTermNode::Call { name, arguments } => name.len() + arguments.len() + 1,
            KernelTermNode::IntegerLiteral(value) => value.bits() as usize + 1,
            _ => 1,
        });
        let key = NodeKey::new(ty, node);
        INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("kernel term interner poisoned")
            .intern(key)
    }
    pub fn ty(&self) -> &KernelType {
        &self.0.key.0.ty
    }
    pub fn node(&self) -> &KernelTermNode {
        &self.0.key.0.node
    }
    /// Immediate expression operands; unmigrated leaves remain opaque.
    pub fn children(&self) -> &[Self] {
        match self.node() {
            KernelTermNode::Fold(fold) => &fold.arguments,
            KernelTermNode::Match(matched) => &matched.arguments,
            KernelTermNode::Constructor(constructor) => &constructor.fields,
            KernelTermNode::AlgebraicCall(call) => &call.arguments,
            KernelTermNode::FloatCall(call) => &call.arguments,
            KernelTermNode::IntegerOperation { arguments, .. }
            | KernelTermNode::Call { arguments, .. } => arguments,
            KernelTermNode::MachineBinary { arguments, .. }
            | KernelTermNode::FloatBinary { arguments, .. }
            | KernelTermNode::FloatCompare { arguments, .. }
            | KernelTermNode::BoolOverflow { arguments, .. }
            | KernelTermNode::BoolCompare { arguments, .. }
            | KernelTermNode::IntegerCompare { arguments, .. }
            | KernelTermNode::AlgebraicEqual { arguments }
            | KernelTermNode::BoolEqual { arguments } => arguments,
            KernelTermNode::BoolIf { arguments }
            | KernelTermNode::AlgebraicIf { arguments }
            | KernelTermNode::IntegerIf { arguments }
            | KernelTermNode::MachineIf { arguments } => arguments,
            KernelTermNode::BoolCast { operand, .. }
            | KernelTermNode::ProgramParameter { operand }
            | KernelTermNode::FloatConvert { operand, .. }
            | KernelTermNode::FloatNegate { operand }
            | KernelTermNode::FloatClassify { operand, .. }
            | KernelTermNode::IntegerToMachine { operand, .. }
            | KernelTermNode::MachineObservation { operand, .. }
            | KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => std::slice::from_ref(operand),
            _ => &[],
        }
    }

    pub(crate) fn bool_cast(
        destination: MachineIntegerType,
        operand: KernelTerm,
    ) -> Result<Self, &'static str> {
        if operand.ty() != &KernelType::Bool {
            return Err("Boolean conversion requires a Bool operand");
        }
        Ok(Self::intern(
            KernelType::Program(destination.program_type()),
            KernelTermNode::BoolCast {
                destination,
                operand,
            },
        ))
    }

    pub(crate) fn integer_to_machine(
        destination: MachineIntegerType,
        operand: KernelTerm,
    ) -> Result<Self, &'static str> {
        if operand.ty() != &KernelType::Integer {
            return Err("machine conversion requires an Integer operand");
        }
        Ok(Self::intern(
            KernelType::Program(destination.program_type()),
            KernelTermNode::IntegerToMachine {
                destination,
                operand,
            },
        ))
    }

    pub fn integer_literal(value: BigInt) -> Self {
        Self::intern(KernelType::Integer, KernelTermNode::IntegerLiteral(value))
    }
    pub fn variable(ty: KernelType, variable: Variable) -> Self {
        Self::intern(ty, KernelTermNode::Variable(variable))
    }
    pub(crate) fn integer_if_raw(arguments: [Self; 3]) -> Self {
        Self::intern(KernelType::Integer, KernelTermNode::IntegerIf { arguments })
    }
    pub fn integer_operation(
        operator: KernelIntegerOperator,
        arguments: Vec<Self>,
    ) -> Result<Self, &'static str> {
        let arity = if operator == KernelIntegerOperator::Negate {
            1
        } else {
            2
        };
        if arguments.len() != arity || arguments.iter().any(|arg| arg.ty() != &KernelType::Integer)
        {
            return Err("Integer operation requires Integer operands of the declared arity");
        }
        Ok(Self::intern(
            KernelType::Integer,
            KernelTermNode::IntegerOperation {
                operator,
                arguments,
            },
        ))
    }
    /// Called after the existing declaration checker resolves the signature.
    pub(crate) fn checked_call(ty: KernelType, name: String, arguments: Vec<Self>) -> Self {
        Self::intern(ty, KernelTermNode::Call { name, arguments })
    }
    fn legacy(argument: PureFunctionArgument) -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let identity = LegacyIdentity::Fresh(
            NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                .expect("legacy term identity exhausted"),
        );
        Self::legacy_at(argument, identity)
    }
    /// Retain an already-native opaque machine operand at a shared parent.
    /// The identity belongs to its explicit typed input, never to an export of
    /// a shared tree. This temporary payload uses the existing legacy boundary.
    pub(crate) fn retained_machine_operand(
        format: MachineIntegerType,
        operand: MachineOperandView<'_>,
    ) -> Self {
        if let MachineOperandView::Legacy(value) = operand
            && let Some(root) = KernelTermImport::default().float_to_machine(format, value)
        {
            return root;
        }
        match operand {
            MachineOperandView::Shared(root) => root.with_machine_observation_type(format),
            MachineOperandView::Legacy(_) if operand.binary().is_some() => {
                let (operation_format, op, children) = operand.binary().unwrap();
                Self::machine_binary_shared_as(
                    format,
                    operation_format,
                    op,
                    children.map(|child| Self::retained_machine_operand(operation_format, child)),
                )
            }
            MachineOperandView::Legacy(_) if operand.unary().is_some() => {
                let (operation_format, op, child) = operand.unary().unwrap();
                Self::machine_unary_shared(
                    operation_format,
                    op,
                    Self::retained_machine_operand(operation_format, child),
                )
                .with_machine_observation_type(format)
            }
            MachineOperandView::Legacy(_) if operand.cast().is_some() => {
                let (encoding, source, destination, child) = operand.cast().unwrap();
                Self::machine_cast_shared(
                    encoding,
                    source,
                    destination,
                    Self::retained_machine_operand(source, child),
                )
                .with_machine_observation_type(format)
            }
            MachineOperandView::Legacy(MachineTerm::If {
                condition,
                then_term,
                else_term,
            }) => Self::machine_if_shared(
                format,
                [
                    KernelTermImport::default().condition(condition),
                    Self::retained_machine_operand(format, MachineOperandView::Legacy(then_term)),
                    Self::retained_machine_operand(format, MachineOperandView::Legacy(else_term)),
                ],
            ),
            MachineOperandView::Legacy(value) => {
                Self::retained_native_machine_operand(format, value)
            }
        }
    }

    /// Import one explicit native operand without splitting an opaque
    /// composite. Its native observation identity must survive when a checker
    /// puts it beside a shared operand in a new operation.
    pub(crate) fn retained_native_machine_operand(
        format: MachineIntegerType,
        value: &MachineTerm,
    ) -> Self {
        KernelTermImport::default()
            .machine_arithmetic(format, value)
            .unwrap_or_else(|| {
                // Native equality can ignore object-class evidence and
                // state authority. Preserve this exact producer payload;
                // checking may relate it to another leaf separately.
                use std::sync::atomic::{AtomicU64, Ordering};
                static NEXT: AtomicU64 = AtomicU64::new(0);
                let id = NEXT
                    .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                    .expect("retained machine leaf identity exhausted");
                Self::legacy_at(
                    PureFunctionArgument::Value(machine::wrap_exact(format, value.clone())),
                    LegacyIdentity::Machine(id),
                )
            })
    }

    /// Rebuild a selected native leaf while preserving a common call producer.
    /// No-op rewrites keep exact payload metadata, as on the native path.
    pub(crate) fn rewritten_machine_leaf(
        &self,
        format: MachineIntegerType,
        original: &MachineTerm,
        rewritten: &MachineTerm,
    ) -> Self {
        if matches!(
            self.node(),
            KernelTermNode::Legacy(_)
                | KernelTermNode::Call { .. }
                | KernelTermNode::IntegerAddress { .. }
        ) && rewritten == original
        {
            return self.clone();
        }
        if matches!(self.node(), KernelTermNode::Call { .. })
            && let MachineTerm::ClickFunctionApplication { name, arguments } = rewritten
        {
            return KernelTermImport::default().machine_call(
                format,
                &SharedPureApplication::intern(name.clone(), arguments.clone()),
            );
        }
        Self::retained_native_machine_operand(format, rewritten)
    }

    /// Numeric observation identity is distinct from a producer's exact payload
    /// identity. Only observation construction uses this leaf; address indices
    /// and stored results retain their original producer metadata.
    pub(crate) fn machine_observation_leaf(
        format: MachineIntegerType,
        value: MachineTerm,
        identity: SharedMachineIntegerTerm,
    ) -> Self {
        Self::legacy_at(
            PureFunctionArgument::Value(machine::wrap_exact(format, value)),
            LegacyIdentity::MachineObservation(identity),
        )
    }

    pub(crate) fn bool_observation_leaf(
        condition: ConditionTerm,
        identity: SharedMachineIntegerTerm,
    ) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::LegacyBool(KernelLegacyTerm {
                identity: LegacyIdentity::MachineObservation(identity),
                value: PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
                    to: MachineIntegerType::UInt8,
                    value: Box::new(condition),
                })),
            }),
        )
    }

    /// Numeric observation of a selected opaque descriptor. Producer payloads
    /// remain exact; only this observation uses the native equality contract.
    pub(crate) fn native_observation_leaf(argument: PureFunctionArgument) -> Self {
        Self::legacy_at(
            argument.clone(),
            LegacyIdentity::NativeObservation(Box::new(argument)),
        )
    }

    fn legacy_at(argument: PureFunctionArgument, identity: LegacyIdentity) -> Self {
        let ty = match &argument {
            PureFunctionArgument::Integer(_) => KernelType::Integer,
            PureFunctionArgument::Value(value) => KernelType::Program(value.program_type()),
            PureFunctionArgument::SharedMachine(value) => {
                KernelType::Program(value.ty().program_type())
            }
            PureFunctionArgument::Algebraic(value) => {
                KernelType::Algebraic(value.algebraic_type.clone())
            }
            PureFunctionArgument::ArrayRef { element_type, .. } => {
                KernelType::ArrayRef(*element_type)
            }
        };
        Self::intern(
            ty,
            KernelTermNode::Legacy(KernelLegacyTerm {
                identity,
                value: argument,
            }),
        )
    }
}

/// One conversion per shared source node, including shared call arguments.
/// This bridge is removed as producers construct KernelTerm directly.
#[derive(Default)]
pub(crate) struct KernelTermImport {
    integers: HashMap<SharedIntegerTerm, KernelTerm>,
    // Stored native field inputs preserve argument carrier forms. Numeric
    // checking/producer imports keep their existing common-operand policy.
    exact_field_inputs: bool,
    // Index producers can retain their supplied native tree unless import
    // expanded a registered read.
    pub(super) machine_input_requires_export: bool,
}
impl KernelTermImport {
    pub(crate) fn for_exact_field_inputs() -> Self {
        Self {
            exact_field_inputs: true,
            ..Self::default()
        }
    }

    /// Every argument family is explicit here. Native fallbacks preserve C
    /// carrier records and out-of-domain inputs; migrated expressions expose
    /// their children through the common nodes.
    pub(crate) fn argument(&mut self, argument: &PureFunctionArgument) -> KernelTerm {
        match argument {
            PureFunctionArgument::Algebraic(value) => self.algebraic(value),
            PureFunctionArgument::Integer(value) => self.integer(value),
            PureFunctionArgument::SharedMachine(value) => value
                .shared_operand()
                .cloned()
                .unwrap_or_else(|| self.machine(value.ty(), value.value())),
            PureFunctionArgument::Value(value) => match value {
                integer_c_value!(bits) => self.machine(
                    MachineIntegerType::from_program_type(value.program_type()).unwrap(),
                    bits,
                ),
                ProgramValue::Float32(bits) => self.float(KernelFloatType::Float32, bits),
                ProgramValue::Float64(bits) => self.float(KernelFloatType::Float64, bits),
                ProgramValue::Bool(word) => match word {
                    MachineTerm::Constant {
                        format: MachineIntegerType::UInt8,
                        bits,
                    } if *bits <= 1 => self.condition(&ConditionTerm::Constant(*bits != 0)),
                    MachineTerm::Variable(variable) => {
                        KernelTerm::variable(KernelType::Program(ProgramType::Bool), *variable)
                    }
                    MachineTerm::BoolCast {
                        to: MachineIntegerType::UInt8,
                        value,
                    } if !matches!(value.as_ref(), ConditionTerm::Constant(_)) => {
                        self.condition(value)
                    }
                    // Other C-word carriers retain their original width and
                    // bits. Importing an argument must not normalize its truth.
                    _ => KernelTerm::legacy(argument.clone()),
                },
                ProgramValue::Parameter(value) => {
                    KernelTerm::program_parameter(self.algebraic(value))
                }
                ProgramValue::Pointer(value) => {
                    KernelTerm::shared_pointer_value(SharedPointer::import(value))
                }
                // Void has no expression. A complete pointer/integer record is
                // the package-7 value descriptor, not its numeric projection.
                ProgramValue::Void | ProgramValue::PointerInteger(_) => {
                    KernelTerm::legacy(argument.clone())
                }
            },
            PureFunctionArgument::ArrayRef {
                memory,
                pointer,
                element_type,
            } => match pointer {
                ProgramValue::Pointer(pointer) => KernelTerm::shared_array_reference(
                    ProgramPoint::of_memory(memory),
                    KernelTerm::shared_pointer_value(SharedPointer::import(pointer)),
                    *element_type,
                ),
                // Preserve the existing refusal boundary for a non-pointer
                // descriptor rather than inventing an address for it.
                _ => KernelTerm::legacy(argument.clone()),
            },
        }
    }
    pub(crate) fn integer(&mut self, term: &SharedIntegerTerm) -> KernelTerm {
        if SESSION_INTEGER_BRIDGES.with(|memo| memo.borrow().contains(&term.id()))
            && let Some(value) = term.kernel_term()
        {
            return value.clone();
        }
        if let Some(value) = self.integers.get(term) {
            return value.clone();
        }
        crate::instrumentation::record_deterministic_work(1);
        use KernelIntegerOperator as Op;
        let value = match term.as_ref() {
            IntegerTerm::Constant(value) => KernelTerm::integer_literal(value.clone()),
            IntegerTerm::Variable(variable) => KernelTerm::variable(KernelType::Integer, *variable),
            IntegerTerm::Machine(machine) => KernelTerm::intern(
                KernelType::Integer,
                KernelTermNode::MachineObservation {
                    format: machine.ty(),
                    operand: machine
                        .shared_operand()
                        .cloned()
                        .unwrap_or_else(|| self.machine(machine.ty(), machine.value())),
                },
            ),
            IntegerTerm::Negate(inner) => {
                KernelTerm::integer_operation(Op::Negate, vec![self.integer(inner)]).unwrap()
            }
            IntegerTerm::Add(a, b)
            | IntegerTerm::Subtract(a, b)
            | IntegerTerm::Multiply(a, b)
            | IntegerTerm::TruncatingQuotient(a, b)
            | IntegerTerm::TruncatingRemainder(a, b) => {
                let operator = match term.as_ref() {
                    IntegerTerm::Add(..) => Op::Add,
                    IntegerTerm::Subtract(..) => Op::Subtract,
                    IntegerTerm::Multiply(..) => Op::Multiply,
                    IntegerTerm::TruncatingQuotient(..) => Op::TruncatingQuotient,
                    _ => Op::TruncatingRemainder,
                };
                KernelTerm::integer_operation(operator, vec![self.integer(a), self.integer(b)])
                    .unwrap()
            }
            IntegerTerm::PureFunctionApplication(application) => {
                let arguments = application
                    .arguments()
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        if let Some(root) = application.common_argument(index) {
                            root
                        } else {
                            KernelTerm::legacy_at(
                                arg.clone(),
                                LegacyIdentity::ApplicationArgument(application.clone(), index),
                            )
                        }
                    })
                    .collect();
                KernelTerm::checked_call(KernelType::Integer, application.name().into(), arguments)
            }
            IntegerTerm::If {
                condition,
                then_term,
                else_term,
            } => KernelTerm::intern(
                KernelType::Integer,
                KernelTermNode::IntegerIf {
                    arguments: [
                        self.condition(condition),
                        self.integer(then_term),
                        self.integer(else_term),
                    ],
                },
            ),
            IntegerTerm::RangeFold { .. } => KernelFold::import_integer(self, term)
                .expect("Integer fold payload")
                .into_term(),
            IntegerTerm::AlgebraicMatch { .. } => KernelMatch::import_integer(self, term)
                .expect("Integer match payload")
                .into_term(),
        };
        value.remember_integer(term);
        self.integers.insert(term.clone(), value.clone());
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_integer_bridges_have_session_local_work() {
        use crate::instrumentation::measure_deterministic_work;
        let source: SharedIntegerTerm = IntegerTerm::add(
            IntegerTerm::Variable(Variable(87654329)),
            IntegerTerm::constant(17.into()),
        )
        .into();
        let import = || {
            let _session = crate::kernel::VerificationSession::enter();
            let (term, cold) =
                measure_deterministic_work(|| KernelTermImport::default().integer(&source));
            let (again, warm) =
                measure_deterministic_work(|| KernelTermImport::default().integer(&source));
            assert_eq!(term, again);
            assert!(cold > warm);
            (term, cold)
        };
        let first = import();
        let second = import();
        assert_eq!(
            first, second,
            "retained nodes must not change a later run's work or identity"
        );
        let export = || {
            let _session = crate::kernel::VerificationSession::enter();
            let (value, cold) = measure_deterministic_work(|| {
                KernelTermExport::default().integer(&first.0).unwrap()
            });
            let (again, warm) = measure_deterministic_work(|| {
                KernelTermExport::default().integer(&first.0).unwrap()
            });
            assert_eq!(value, again);
            assert_eq!(value, source);
            assert!(cold > warm);
            cold
        };
        assert_eq!(export(), export());
    }

    #[test]
    fn reverse_bridge_does_not_keep_the_source_node_alive() {
        let source: SharedIntegerTerm = IntegerTerm::Variable(Variable(87654321)).into();
        let weak = source.downgrade();
        let common = KernelTermImport::default().integer(&source);
        drop(source);
        assert!(weak.upgrade().is_none());
        assert_eq!(common.ty(), &KernelType::Integer);
        let reconstructed = KernelTermExport::default().integer(&common).unwrap();
        assert_eq!(reconstructed.kernel_term(), Some(&common));
    }

    #[test]
    fn shared_observation_keeps_identity_across_lazy_boxing_and_source_drop() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let leaf = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(87654325),
            );
            let operand =
                KernelTerm::arithmetic_binary(format, MachineBinaryOp::Add, [leaf.clone(), leaf])
                    .unwrap();
            let observation =
                SharedMachineIntegerTerm::from_shared(format, operand.clone()).unwrap();
            assert!(!observation.has_boxed_operand());
            assert!(observation.value_reading().is_none());
            assert!(!observation.has_boxed_operand());
            let source: SharedIntegerTerm = IntegerTerm::Machine(observation.clone()).into();
            let common = KernelTermImport::default().integer(&source);
            assert_eq!(common.children()[0], operand);
            drop(source);
            clear_integer_bridge_memo();
            let restored = KernelTermExport::default().integer(&common).unwrap();
            let IntegerTerm::Machine(restored) = restored.as_ref() else {
                panic!("machine observation");
            };
            assert_eq!(restored.id(), observation.id());
            assert!(!observation.has_boxed_operand());
            let boxed = KernelTermExport::machine(&operand).unwrap();
            let old_entry = SharedMachineIntegerTerm::intern(format, boxed.clone());
            assert_eq!(old_entry.id(), observation.id());
            assert_eq!(restored.value(), &boxed);
            assert!(observation.has_boxed_operand());
            assert!(
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int8, operand).is_none()
            );
        }
    }

    #[test]
    fn integer_conversion_observations_keep_unmigrated_payloads_outside_the_fragment() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let value = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "opaque_argument".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                MachineTerm::MemoryLoad(
                    ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
                    Box::new(Address::symbolic(Variable(87654328))),
                    LoadKind::Int32,
                ),
            ))],
        ));
        let native = MachineTerm::IntegerToMachine {
            value: value.into(),
            destination: format,
        };
        let mut importer = KernelTermImport::default();
        let root = importer.machine(format, &native);
        assert!(root.has_opaque_observation_boundary());
        assert!(SharedMachineIntegerTerm::from_shared(format, root.clone()).is_none());
        assert!(importer.machine_arithmetic(format, &native).is_none());
        assert_eq!(KernelTermExport::machine(&root).unwrap(), native);
    }

    #[test]
    fn observation_storage_shares_casts_but_keeps_opaque_compatibility_boundaries() {
        let format = MachineIntegerType::Int32;
        let cast = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: MachineIntegerType::Int8,
            to: format,
            value: Box::new(MachineTerm::Variable(Variable(87654326))),
        };
        let term = KernelTermImport::default().machine(format, &cast);
        let shared = SharedMachineIntegerTerm::from_shared(format, term).unwrap();
        assert!(!shared.has_boxed_operand());
        assert!(shared.value_reading().is_some());
        assert!(!shared.has_boxed_operand());
        let observation = SharedMachineIntegerTerm::intern(format, cast.clone());
        assert!(observation.shared_operand().is_some());
        assert_eq!(observation.id(), shared.id());
        assert_eq!(observation.value(), &cast);
        assert!(observation.value_reading().is_some());
        let opaque = KernelTerm::legacy(PureFunctionArgument::Value(ProgramValue::Int32(
            MachineTerm::Variable(Variable(87654327)),
        )));
        let parent =
            KernelTerm::arithmetic_binary(format, MachineBinaryOp::Add, [opaque.clone(), opaque])
                .unwrap();
        assert!(!parent.is_shared_machine_operand());
        assert!(SharedMachineIntegerTerm::from_shared(format, parent).is_none());
    }

    #[test]
    fn machine_observation_retains_its_format_and_reconstructs_after_source_drop() {
        let word = MachineTerm::Variable(Variable(87654322));
        let mut observations = Vec::new();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let machine = SharedMachineIntegerTerm::intern(format, word.clone());
            let source: SharedIntegerTerm = IntegerTerm::Machine(machine.clone()).into();
            let common = KernelTermImport::default().integer(&source);
            assert!(
                matches!(common.node(), KernelTermNode::MachineObservation { format: actual, .. } if *actual == format)
            );
            assert_eq!(common.ty(), &KernelType::Integer);
            assert_eq!(
                common.children()[0].ty(),
                &KernelType::Program(format.program_type())
            );
            drop(source);
            let restored = KernelTermExport::default().integer(&common).unwrap();
            assert!(
                matches!(restored.as_ref(), IntegerTerm::Machine(actual) if actual.id() == machine.id())
            );
            observations.push(common);
        }
        assert_ne!(observations[0], observations[1]);
        assert_ne!(observations[2], observations[3]);
    }

    #[test]
    fn checker_bridge_preserves_calls_and_machine_types() {
        let input =
            PureFunctionArgument::Value(ProgramValue::UInt32(MachineTerm::Variable(Variable(70))));
        let call = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "foo".into(),
            vec![input],
        ));
        let source: SharedIntegerTerm =
            IntegerTerm::Add(IntegerTerm::Variable(Variable(71)).into(), call.into()).into();
        let common = KernelTermImport::default().integer(&source);
        assert_eq!(common.children().len(), 2);
        assert!(matches!(
            common.children()[1].node(),
            KernelTermNode::Call { .. }
        ));
        assert_eq!(
            common.children()[1].children()[0].ty(),
            &KernelType::Program(ProgramType::UInt32)
        );
        assert_eq!(
            KernelTermExport::default().integer(&common).unwrap(),
            source
        );
    }

    #[test]
    fn integer_conditional_has_common_children_after_source_drop() {
        let _session = crate::kernel::VerificationSession::enter();
        let source: SharedIntegerTerm = IntegerTerm::If {
            condition: Box::new(ConditionTerm::Variable(Variable(993402))),
            then_term: IntegerTerm::Variable(Variable(993403)).into(),
            else_term: IntegerTerm::constant_i64(-1).into(),
        }
        .into();
        let weak = source.downgrade();
        let common = KernelTermImport::default().integer(&source);
        assert!(matches!(common.node(), KernelTermNode::IntegerIf { .. }));
        assert_eq!(common.children().len(), 3);
        assert_eq!(common.children()[0].ty(), &KernelType::Bool);
        drop(source);
        assert!(weak.upgrade().is_none());
        let restored = KernelTermExport::default().integer(&common).unwrap();
        assert_eq!(KernelTermImport::default().integer(&restored), common);
    }

    #[test]
    fn legacy_pointer_equality_does_not_discard_auxiliary_qualifiers() {
        let pointer = Pointer::new(Address::symbolic(Variable(76)), ProgramType::Int32Pointer);
        let constant = pointer.clone().with_pointee_constant(true);
        assert_eq!(
            pointer, constant,
            "const is auxiliary, not pointer identity"
        );
        let mut import = KernelTermImport::default();
        let plain = import.argument(&PureFunctionArgument::Value(ProgramValue::Pointer(pointer)));
        let qualified = import.argument(&PureFunctionArgument::Value(ProgramValue::Pointer(
            constant,
        )));
        let PureFunctionArgument::Value(ProgramValue::Pointer(restored)) =
            KernelTermExport::default().argument(&qualified).unwrap()
        else {
            panic!("pointer")
        };
        assert!(restored.pointee_constant());
        let PureFunctionArgument::Value(ProgramValue::Pointer(restored)) =
            KernelTermExport::default().argument(&plain).unwrap()
        else {
            panic!("pointer")
        };
        assert!(!restored.pointee_constant());
    }

    #[test]
    fn legacy_adapter_keeps_complete_pointers_and_scoped_integer_nodes() {
        let base = Address::symbolic(Variable(75));
        let root = Pointer::new(base.clone(), ProgramType::Int32Pointer);
        let member = root.clone().with_bounds(Some(SubobjectBounds {
            start: base,
            width: 4u32.into(),
        }));
        let mut import = KernelTermImport::default();
        let root = PureFunctionArgument::Value(ProgramValue::Pointer(root));
        let member = PureFunctionArgument::Value(ProgramValue::Pointer(member));
        let root_term = import.argument(&root);
        let member_term = import.argument(&member);
        assert_ne!(root_term, member_term);
        let mut export = KernelTermExport::default();
        assert_eq!(export.argument(&root_term).unwrap(), root);
        assert_eq!(export.argument(&member_term).unwrap(), member);
        let conditional: SharedIntegerTerm = IntegerTerm::If {
            condition: Box::new(ConditionTerm::Constant(true)),
            then_term: IntegerTerm::constant_i64(1).into(),
            else_term: IntegerTerm::constant_i64(2).into(),
        }
        .into();
        assert_eq!(
            export.integer(&import.integer(&conditional)).unwrap(),
            conditional
        );
    }

    #[test]
    fn structural_identity_preserves_operations_types_and_call_arguments() {
        let a = KernelTerm::variable(KernelType::Integer, Variable(71));
        let b = KernelTerm::variable(KernelType::Integer, Variable(72));
        let call = KernelTerm::checked_call(KernelType::Integer, "foo".into(), vec![b.clone()]);
        let sum = KernelTerm::integer_operation(
            KernelIntegerOperator::Add,
            vec![a.clone(), call.clone()],
        )
        .unwrap();
        assert_eq!(
            sum,
            KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![a, call]).unwrap()
        );
        assert_ne!(
            b,
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(72))
        );
        let one = KernelTerm::integer_literal(1.into());
        assert_ne!(
            KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![one.clone(), one])
                .unwrap(),
            KernelTerm::integer_literal(2.into())
        );
        assert!(
            KernelTerm::integer_operation(
                KernelIntegerOperator::Negate,
                vec![KernelTerm::variable(
                    KernelType::Program(ProgramType::Int32),
                    Variable(72)
                )]
            )
            .is_err()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/kernel_term.rs");
}

/// Lossless bridge back to the existing checker. No normalizing constructors.
#[derive(Default)]
pub(crate) struct KernelTermExport {
    values: HashMap<KernelTerm, PureFunctionArgument>,
}
impl KernelTermExport {
    pub(crate) fn argument(
        &mut self,
        term: &KernelTerm,
    ) -> Result<PureFunctionArgument, &'static str> {
        if FloatOperandView::from_shared(term).is_some() {
            return Self::float(term).map(PureFunctionArgument::Value);
        }
        if let Some(value) = term.boolean_argument_native() {
            return Ok(value.clone());
        }
        // A typed variable is already a complete native leaf descriptor.
        // Reading it does not invoke an expression-tree exporter.
        if let KernelTermNode::Variable(variable) = term.node() {
            match term.ty() {
                KernelType::Program(ty) => {
                    if let Some(format) = MachineIntegerType::from_program_type(*ty) {
                        crate::instrumentation::record_deterministic_work(1);
                        return Ok(PureFunctionArgument::Value(machine::wrap_exact(
                            format,
                            MachineTerm::Variable(*variable),
                        )));
                    }
                }
                KernelType::Algebraic(ty) => {
                    crate::instrumentation::record_deterministic_work(1);
                    return Ok(PureFunctionArgument::Algebraic(AlgebraicTerm {
                        algebraic_type: ty.clone(),
                        node: AlgebraicTermNode::Variable(*variable),
                    }));
                }
                _ => {}
            }
        }
        if let Some(value) = term.legacy_integer() {
            return Ok(PureFunctionArgument::Integer(value));
        }
        if let KernelType::Program(program_type) = term.ty()
            && let Some(format) = MachineIntegerType::from_program_type(*program_type)
            && !matches!(term.node(), KernelTermNode::Legacy(_))
        {
            // Export the explicit boxed output once. Caching and then cloning
            // every intermediate boxed subtree would make a chain quadratic.
            return Ok(PureFunctionArgument::Value(machine::wrap_exact(
                format,
                Self::machine(term)?,
            )));
        }
        if matches!(term.ty(), KernelType::Algebraic(_))
            && matches!(
                term.node(),
                KernelTermNode::Match(_)
                    | KernelTermNode::AlgebraicCall(_)
                    | KernelTermNode::AlgebraicIf { .. }
                    | KernelTermNode::AlgebraicRead(_)
                    | KernelTermNode::Constructor(_)
                    | KernelTermNode::Variable(_)
            )
        {
            return self.algebraic(term).map(PureFunctionArgument::Algebraic);
        }
        if let Some(value) = self.values.get(term) {
            return Ok(value.clone());
        }
        crate::instrumentation::record_deterministic_work(match term.node() {
            KernelTermNode::IntegerLiteral(value) => value.bits() as usize + 1,
            KernelTermNode::IntegerOperation { arguments, .. } => arguments.len() + 1,
            KernelTermNode::Call { name, arguments } => name.len() + arguments.len() + 1,
            _ => 1,
        });
        let value = match term.node() {
            KernelTermNode::Match(matched) if term.ty() == &KernelType::Integer => {
                PureFunctionArgument::Integer(matched.export_integer(self)?.into())
            }
            KernelTermNode::Fold(fold) if term.ty() == &KernelType::Integer => {
                PureFunctionArgument::Integer(fold.integer_compatibility(self)?.into())
            }
            KernelTermNode::PointerRead { value, .. }
            | KernelTermNode::PointerArithmetic { value, .. }
            | KernelTermNode::PointerCall { value, .. }
            | KernelTermNode::Pointer(value) => {
                PureFunctionArgument::Value(ProgramValue::Pointer(value.export()?))
            }
            KernelTermNode::ArrayReference { .. } => {
                term.pointer_argument_native().unwrap().clone()
            }
            KernelTermNode::ProgramParameter { operand } => PureFunctionArgument::Value(
                ProgramValue::Parameter(Box::new(self.algebraic(operand)?)),
            ),
            KernelTermNode::Legacy(value) => value.value().clone(),
            KernelTermNode::IntegerLiteral(value) => {
                PureFunctionArgument::Integer(IntegerTerm::Constant(value.clone()).into())
            }
            KernelTermNode::Variable(variable) if term.ty() == &KernelType::Integer => {
                PureFunctionArgument::Integer(IntegerTerm::Variable(*variable).into())
            }
            KernelTermNode::MachineObservation { format, operand } => {
                PureFunctionArgument::Integer(
                    IntegerTerm::Machine(
                        match SharedMachineIntegerTerm::from_shared(*format, operand.clone()) {
                            Some(value) => value,
                            None => {
                                SharedMachineIntegerTerm::intern(*format, Self::machine(operand)?)
                            }
                        },
                    )
                    .into(),
                )
            }
            KernelTermNode::IntegerIf { arguments } => PureFunctionArgument::Integer(
                IntegerTerm::If {
                    condition: Box::new(Self::condition(&arguments[0])?),
                    then_term: self.integer(&arguments[1])?,
                    else_term: self.integer(&arguments[2])?,
                }
                .into(),
            ),
            KernelTermNode::IntegerOperation {
                operator,
                arguments,
            } => {
                let mut args = arguments
                    .iter()
                    .map(|arg| self.integer(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter();
                let a = args.next().unwrap();
                use KernelIntegerOperator as Op;
                let value = match operator {
                    Op::Negate => IntegerTerm::Negate(a),
                    Op::Add => IntegerTerm::Add(a, args.next().unwrap()),
                    Op::Subtract => IntegerTerm::Subtract(a, args.next().unwrap()),
                    Op::Multiply => IntegerTerm::Multiply(a, args.next().unwrap()),
                    Op::TruncatingQuotient => {
                        IntegerTerm::TruncatingQuotient(a, args.next().unwrap())
                    }
                    Op::TruncatingRemainder => {
                        IntegerTerm::TruncatingRemainder(a, args.next().unwrap())
                    }
                };
                PureFunctionArgument::Integer(value.into())
            }
            KernelTermNode::Call { name, arguments } if term.ty() == &KernelType::Integer => {
                let arguments = arguments
                    .iter()
                    .map(|arg| self.argument(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                PureFunctionArgument::Integer(
                    IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                        name.clone(),
                        arguments,
                    ))
                    .into(),
                )
            }
            _ => return Err("kernel term sort has not migrated to the checker bridge"),
        };
        if let PureFunctionArgument::Integer(integer) = &value {
            term.remember_integer(integer);
        }
        self.values.insert(term.clone(), value.clone());
        Ok(value)
    }
    pub(crate) fn integer(&mut self, term: &KernelTerm) -> Result<SharedIntegerTerm, &'static str> {
        match self.argument(term)? {
            PureFunctionArgument::Integer(value) => Ok(value),
            _ => Err("expected Integer kernel term"),
        }
    }
}

#[cfg(test)]
mod mixed_arguments;
