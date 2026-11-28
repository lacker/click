//! Shared typed expression nodes. Typed input leaves preserve exact written
//! inputs at the native API boundary.
//! No constructor consults facts, evaluates arithmetic, or unfolds a call.
use super::integer::{IntegerIdentity, IntegerRangeIdentity, IntegerShallowKey};
use super::*;
use crate::kernel::MachineCastSpelling;
mod boolean;
pub(crate) use boolean::BooleanOperandView;
pub use boolean::KernelPointerEquality;
pub use pointer_observations::KernelObservedPointer;
// Scoped payloads shared by evaluation, checking, and Surface synthesis.
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
mod matches;
pub(crate) use matches::KernelMatchArm;
pub(crate) use matches::{KernelConstructor, KernelMatch};
mod pointer_observations;
mod reads;
pub use reads::KernelMemoryRead;
// Pointer descriptors retain address, offset, and producer syntax.
mod addresses;
mod offsets;
mod pointers;
pub use addresses::{Address, AddressParts};
pub(crate) use addresses::{AddressBlock, SharedAddress, SharedAddressBase};
pub use machine::KernelMachineLiteral;
pub(in crate::kernel) use machine::wrap_exact as wrap_exact_machine_value;
use num_bigint::BigInt;
pub use offsets::AddressOffset;
pub(crate) use offsets::{KernelAddressOffset, OffsetTree, OffsetView, SharedAddressOffset};
pub(in crate::kernel) use pointers::ArrayObject;
pub(crate) use pointers::{
    KernelArrayObject, KernelMemberArray, KernelPointerMetadata, KernelSubobjectBounds,
    PointerMetadataKey, PointerRewrite, PointerRewriteError, SharedPointer,
};
pub use pointers::{Pointer, SubobjectBounds};
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
        /// The operands keep their block payloads alive. Observation keys use
        /// the semantic block identities already present in the arguments.
        block_payloads: [Option<std::num::NonZeroUsize>; 2],
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
    /// Semantic observation of a pointer or array argument. The exact
    /// source remains available for raising and explicit output.
    ObservedPointer(KernelObservedPointer),
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
        block_payload: Option<std::num::NonZeroUsize>,
        object_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    MachineObservation {
        format: MachineIntegerType,
        operand: KernelTerm,
    },
    /// An explicitly supplied machine expression outside the structural fragment.
    WrittenMachine(KernelWrittenMachine),
    /// An exact scalar input outside its checked structural fragment.
    ImportedScalar(KernelImportedScalar),
    /// An already retained observation whose written carrier has no shared root.
    /// Numeric arguments use the observation identity directly. An exact
    /// Integer producer keeps its own spelling when read as a machine operand.
    MachineObservationInput {
        format: MachineIntegerType,
        observation: SharedMachineIntegerTerm,
        exact: bool,
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
    /// An exact foreign argument carried by its producer's call descriptor.
    CallArgument(KernelCallArgument),
    /// An exact C record or a descriptor refused by the structural importer.
    NativeDescriptor(KernelNativeDescriptor),
    /// Semantic identity of a selected exact call or descriptor input.
    ObservedArgument(KernelObservedArgument),
}

/// A supplied scalar with its original carrier and producer identity.
#[derive(Clone, Debug)]
pub struct KernelImportedScalar {
    carrier: ProgramType,
    source: ImportedScalarSource,
}

#[derive(Clone, Debug)]
enum ImportedScalarSource {
    Exact(Arc<OldMachineTerm>),
    Observed(Arc<OldMachineTerm>),
    Call {
        argument: KernelCallArgument,
        observed: bool,
    },
}

impl KernelImportedScalar {
    pub(crate) fn carrier(&self) -> ProgramType {
        self.carrier
    }

    pub(crate) fn value(&self) -> &OldMachineTerm {
        match &self.source {
            ImportedScalarSource::Exact(value) | ImportedScalarSource::Observed(value) => value,
            ImportedScalarSource::Call { argument, .. } => {
                Self::call_input(argument).expect("scalar call argument").1
            }
        }
    }

    fn call_input(argument: &KernelCallArgument) -> Option<(ProgramType, &OldMachineTerm)> {
        let PureFunctionArgument::Value(value) = argument.value() else {
            return None;
        };
        let word = match value {
            integer_c_value!(word)
            | ProgramValue::Bool(word)
            | ProgramValue::Float32(word)
            | ProgramValue::Float64(word) => word,
            _ => return None,
        };
        Some((value.program_type(), word))
    }

    fn is_exact(&self) -> bool {
        matches!(
            self.source,
            ImportedScalarSource::Exact(_)
                | ImportedScalarSource::Call {
                    observed: false,
                    ..
                }
        )
    }
}

impl PartialEq for KernelImportedScalar {
    fn eq(&self, other: &Self) -> bool {
        if self.carrier != other.carrier {
            return false;
        }
        match (&self.source, &other.source) {
            (ImportedScalarSource::Exact(a), ImportedScalarSource::Exact(b)) => Arc::ptr_eq(a, b),
            (
                ImportedScalarSource::Call {
                    argument: a,
                    observed: false,
                },
                ImportedScalarSource::Call {
                    argument: b,
                    observed: false,
                },
            ) => a == b,
            _ if !self.is_exact() && !other.is_exact() => self.value() == other.value(),
            _ => false,
        }
    }
}
impl Eq for KernelImportedScalar {}
impl Hash for KernelImportedScalar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.carrier.hash(state);
        self.is_exact().hash(state);
        match &self.source {
            ImportedScalarSource::Exact(value) => Arc::as_ptr(value).hash(state),
            ImportedScalarSource::Call {
                argument,
                observed: false,
            } => argument.hash(state),
            _ => hash_written_observation(self.value(), state),
        }
    }
}

fn hash_written_observation(value: &impl Hash, state: &mut impl Hasher) {
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
    value.hash(&mut Charged(state));
}

/// Exact native input to the typed machine operand API. Retagging and
/// reading the operand can reuse the provided syntax by reference.
#[derive(Clone, Debug)]
pub struct KernelWrittenMachine {
    format: MachineIntegerType,
    source: WrittenMachineSource,
}

#[derive(Clone, Debug)]
enum WrittenMachineSource {
    Expression {
        identity: u64,
        value: Arc<OldMachineTerm>,
    },
    AddressIndex(SharedMachineIntegerTerm),
}

#[derive(Eq, PartialEq, Hash)]
enum WrittenMachineIdentity {
    Expression(u64),
    AddressIndex(usize),
}

impl KernelWrittenMachine {
    fn expression(format: MachineIntegerType, value: &OldMachineTerm) -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let identity = NEXT
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("written machine leaf identity exhausted");
        Self {
            format,
            source: WrittenMachineSource::Expression {
                identity,
                value: Arc::new(value.clone()),
            },
        }
    }

    fn identity(&self) -> WrittenMachineIdentity {
        match &self.source {
            WrittenMachineSource::Expression { identity, .. } => {
                WrittenMachineIdentity::Expression(*identity)
            }
            WrittenMachineSource::AddressIndex(index) => {
                WrittenMachineIdentity::AddressIndex(index.payload_id())
            }
        }
    }

    pub(crate) fn value(&self) -> &OldMachineTerm {
        match &self.source {
            WrittenMachineSource::Expression { value, .. } => value,
            WrittenMachineSource::AddressIndex(index) => index.structural_value(),
        }
    }

    pub(crate) fn format(&self) -> MachineIntegerType {
        self.format
    }
}
impl PartialEq for KernelWrittenMachine {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for KernelWrittenMachine {}
impl Hash for KernelWrittenMachine {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
    }
}

/// Reference to the written slot of a particular call. Pure applications
/// compare by semantic identity, but exact call arguments retain their producer.
#[derive(Clone, Debug)]
pub struct KernelCallArgument {
    application: SharedPureApplication,
    index: usize,
}

impl KernelCallArgument {
    pub fn value(&self) -> &PureFunctionArgument {
        &self.application.arguments()[self.index]
    }
}

impl PartialEq for KernelCallArgument {
    fn eq(&self, other: &Self) -> bool {
        self.application.payload_id() == other.application.payload_id() && self.index == other.index
    }
}

impl Eq for KernelCallArgument {}

impl Hash for KernelCallArgument {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.application.payload_id().hash(state);
        self.index.hash(state);
    }
}

/// Opaque descriptors whose native envelopes carry identity or refusal data.
#[derive(Clone, Debug)]
pub struct KernelNativeDescriptor(Arc<PureFunctionArgument>);

impl PartialEq for KernelNativeDescriptor {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for KernelNativeDescriptor {}
impl Hash for KernelNativeDescriptor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

#[derive(Clone, Debug)]
pub struct KernelObservedArgument(KernelTerm);
impl KernelObservedArgument {
    pub fn value(&self) -> &PureFunctionArgument {
        self.0
            .written_argument()
            .expect("observation of an exact argument")
    }
}
impl PartialEq for KernelObservedArgument {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}
impl Eq for KernelObservedArgument {}
impl Hash for KernelObservedArgument {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_written_observation(self.value(), state);
    }
}

/// A produced call already owns its native argument descriptors. Borrow that
/// payload through its application handle instead of constructing a second
/// native call tree when an unmigrated consumer requests the root reading.
#[derive(Default)]
struct MachineLeafCache(std::sync::OnceLock<MachineLeaf>);
enum MachineLeaf {
    Old(OldMachineTerm),
    Application(SharedPureApplication),
}
impl MachineLeafCache {
    fn get_or_init(&self, build: impl FnOnce() -> OldMachineTerm) -> &OldMachineTerm {
        match self.0.get_or_init(|| MachineLeaf::Old(build())) {
            MachineLeaf::Old(value) => value,
            MachineLeaf::Application(application) => application.native_call(),
        }
    }
    fn retain_application(&self, application: &SharedPureApplication) {
        crate::instrumentation::record_deterministic_work(1);
        self.0
            .get_or_init(|| MachineLeaf::Application(application.clone()));
    }
}

#[cfg(test)]
pub(crate) struct WeakKernelTerm(Weak<TermData>);
#[cfg(test)]
impl WeakKernelTerm {
    pub(crate) fn upgrade(&self) -> Option<KernelTerm> {
        self.0.upgrade().map(KernelTerm)
    }
}

struct TermData {
    id: u64,
    key: NodeKey,
    integer_identity: OnceLock<Arc<IntegerIdentity>>,
    integer_reading: OnceLock<Option<SharedIntegerTerm>>,
    machine_leaf: MachineLeafCache,
    integer_output: OnceLock<Box<IntegerTerm>>,
    argument_leaf: std::sync::OnceLock<Box<PureFunctionArgument>>,
}

struct NodeKeyData {
    fingerprint: u64,
    ty: KernelType,
    node: KernelTermNode,
    shared_machine_operand: bool,
    mathematical_integer: bool,
    integer_observation_arithmetic: bool,
    literal_integer_arithmetic: bool,
    opaque_observation_boundary: bool,
    machine_conversions: bool,
    machine_reads: bool,
    conditional_machine_rewrites: bool,
    machine_conditionals: bool,
    machine_folds: bool,
    machine_matches: bool,
    machine_constant: OnceLock<Option<KernelMachineLiteral>>,
}
#[derive(Clone)]
struct NodeKey(Arc<NodeKeyData>);
impl PartialEq for NodeKey {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.ty == other.0.ty
                // Logical type identity omits the schemas used for constructor checks
                // and declared field classes. A stored root must reproduce both.
                && match (&self.0.ty, &other.0.ty) {
                    (KernelType::Algebraic(a), KernelType::Algebraic(b)) =>
                        Arc::ptr_eq(&a.schemas, &b.schemas) || a.schemas == b.schemas,
                    _ => true,
                }
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
                        a.read_key() == b.read_key() && p == q && k == l
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
                    ) => m.read_key() == n.read_key() && a == b && p == q,
                    (KernelTermNode::Match(a), KernelTermNode::Match(b)) => {
                        a == b && a.arms.iter().zip(&b.arms).all(|(a, b)| {
                            a.binding_names.spellings().eq(b.binding_names.spellings())
                        })
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
            point.read_key().hash(&mut hash);
        }
        if let KernelTermNode::Match(matched) = &node {
            for arm in &matched.arms {
                let names = arm.binding_names.spellings();
                names.len().hash(&mut hash);
                for name in names {
                    name.hash(&mut hash);
                }
            }
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
            KernelTermNode::Match(matched) => {
                matched
                    .arms
                    .iter()
                    .any(|arm| arm.binding_names.spellings().len() != 0)
                    || (matches!(ty, KernelType::Program(_) | KernelType::Algebraic(_))
                        && matched
                            .arguments
                            .iter()
                            .chain(matched.arms.iter().flat_map(|arm| &arm.bindings))
                            .any(KernelTerm::has_opaque_observation_boundary))
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
            | KernelTermNode::AlgebraicRead(_)
            | KernelTermNode::FloatRead(_) => true,
            KernelTermNode::MachineObservationInput { exact, .. } => *exact,
            KernelTermNode::WrittenMachine(_) | KernelTermNode::CallArgument(_) => true,
            KernelTermNode::ImportedScalar(input) => input.is_exact(),
            KernelTermNode::NativeDescriptor(_) => true,
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
            KernelTermNode::MachineObservationInput { .. } | KernelTermNode::WrittenMachine(_) => {
                true
            }
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
            KernelTermNode::MachineObservationInput { .. } | KernelTermNode::WrittenMachine(_) => {
                true
            }
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
            KernelTermNode::MachineObservationInput { .. } | KernelTermNode::WrittenMachine(_) => {
                true
            }
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
        let mathematical_integer = ty == KernelType::Integer
            && match &node {
                KernelTermNode::IntegerLiteral(_) | KernelTermNode::Variable(_) => true,
                KernelTermNode::IntegerOperation { arguments, .. } => {
                    arguments.iter().all(KernelTerm::is_mathematical_integer)
                }
                KernelTermNode::Fold(fold) => {
                    fold.index == KernelFoldIndex::Integer
                        && fold
                            .arguments
                            .iter()
                            .all(KernelTerm::is_mathematical_integer)
                }
                _ => false,
            };
        let integer_observation_arithmetic = ty == KernelType::Integer
            && match &node {
                KernelTermNode::IntegerLiteral(_) | KernelTermNode::Variable(_) => true,
                KernelTermNode::IntegerOperation { arguments, .. } => arguments
                    .iter()
                    .all(KernelTerm::is_integer_observation_arithmetic),
                KernelTermNode::MachineObservation { operand, .. } => {
                    operand.is_shared_machine_operand()
                }
                _ => false,
            };
        let literal_integer_arithmetic = match &node {
            KernelTermNode::IntegerLiteral(_) => true,
            KernelTermNode::MachineObservation { format, operand } => {
                MachineOperandView::Shared(operand)
                    .checked_literal_integer_conversion()
                    .is_some_and(|(destination, _)| destination == *format)
            }
            KernelTermNode::IntegerOperation { arguments, .. } => arguments
                .iter()
                .all(KernelTerm::is_literal_integer_arithmetic),
            _ => false,
        };
        // Generic arguments can own a native tree. Read it only when this
        // descriptor is actually used as a machine operand.
        let machine_constant = match &node {
            KernelTermNode::ImportedScalar(_)
            | KernelTermNode::ObservedArgument(_)
            | KernelTermNode::CallArgument(_) => OnceLock::new(),
            _ => OnceLock::from(machine::constant_reading(&node)),
        };
        Self(Arc::new(NodeKeyData {
            machine_constant,
            mathematical_integer,
            integer_observation_arithmetic,
            literal_integer_arithmetic,
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
/// call node do not walk its DAG. Exact payload costs remain explicit input.
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
            match self.terms.get(&key) {
                Some(value) if value.strong_count() > 0 => self.cleanup.push_back(key),
                Some(_) => {
                    self.terms.remove(&key);
                }
                None => {}
            }
        }
        if let Some(existing) = self.terms.get(&key).and_then(Weak::upgrade) {
            return KernelTerm(existing);
        }
        let id = self.next_id;
        self.next_id = id
            .checked_add(1)
            .filter(|id| *id < (1 << 63))
            .expect("kernel term identity exhausted");
        let value = Arc::new(TermData {
            id,
            key: key.clone(),
            integer_identity: Default::default(),
            integer_reading: Default::default(),
            machine_leaf: Default::default(),
            argument_leaf: Default::default(),
            integer_output: Default::default(),
        });
        // A dead value can be replaced before its key reaches the front of
        // the queue. The existing queue entry will examine the replacement.
        if self
            .terms
            .insert(key.clone(), Arc::downgrade(&value))
            .is_none()
        {
            self.cleanup.push_back(key);
        }
        KernelTerm(value)
    }
}

impl KernelTerm {
    #[cfg(test)]
    pub(crate) fn downgrade(&self) -> WeakKernelTerm {
        WeakKernelTerm(Arc::downgrade(&self.0))
    }

    pub(in crate::kernel) fn scalar_storage_key(
        &self,
    ) -> crate::kernel::execution_value::storage_keys::ScalarStorageKey {
        crate::kernel::execution_value::storage_keys::scalar_for_root(self)
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
        if let Some(PureFunctionArgument::Value(value)) = self.written_argument() {
            return Some(value);
        }
        if let Some(value) = self
            .old_pointer_value()
            .or_else(|| self.old_boolean_value())
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
                let value = match self.node() {
                    KernelTermNode::MachineObservationInput {
                        format,
                        observation,
                        ..
                    } => machine::wrap_exact(*format, observation.value().clone()),
                    KernelTermNode::ImportedScalar(input) => Self::imported_scalar_as_native(input),
                    KernelTermNode::WrittenMachine(input) => {
                        machine::wrap_exact(input.format(), input.value().clone())
                    }
                    _ => crate::kernel::ExecutionValue::Shared(self.clone()).into_native(),
                };
                Box::new(PureFunctionArgument::Value(value))
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
        Some(self.0.integer_output.get_or_init(|| {
            Box::new(
                self.shallow_integer_output()
                    .expect("Integer compatibility output"),
            )
        }))
    }

    fn shallow_integer_output(&self) -> Result<IntegerTerm, &'static str> {
        let child = |root: &KernelTerm| SharedIntegerTerm::from_root(root.clone());
        let mut export = KernelTermExport::default();
        Ok(match self.node() {
            KernelTermNode::IntegerLiteral(value) => IntegerTerm::Constant(value.clone()),
            KernelTermNode::Variable(variable) => IntegerTerm::Variable(*variable),
            KernelTermNode::IntegerOperation {
                operator,
                arguments,
            } => {
                let left = child(&arguments[0]);
                use KernelIntegerOperator as Op;
                match operator {
                    Op::Negate => IntegerTerm::Negate(left),
                    Op::Add => IntegerTerm::Add(left, child(&arguments[1])),
                    Op::Subtract => IntegerTerm::Subtract(left, child(&arguments[1])),
                    Op::Multiply => IntegerTerm::Multiply(left, child(&arguments[1])),
                    Op::TruncatingQuotient => {
                        IntegerTerm::TruncatingQuotient(left, child(&arguments[1]))
                    }
                    Op::TruncatingRemainder => {
                        IntegerTerm::TruncatingRemainder(left, child(&arguments[1]))
                    }
                }
            }
            KernelTermNode::MachineObservation { .. } => IntegerTerm::Machine(
                self.exact_shared_integer_observation()
                    .ok_or("Integer observation operand")?,
            ),
            KernelTermNode::IntegerIf {
                arguments: [guard, yes, no],
            } => IntegerTerm::If {
                condition: Box::new(KernelTermExport::condition(guard)?),
                then_term: child(yes),
                else_term: child(no),
            },
            KernelTermNode::Fold(fold) => fold.integer_compatibility(&mut export)?,
            KernelTermNode::Match(matched) => matched.export_integer(&mut export)?,
            KernelTermNode::Call { .. } => IntegerTerm::PureFunctionApplication(
                self.integer_application()
                    .ok_or("Integer application arguments")?,
            ),
            _ => return Err("expected an Integer term"),
        })
    }

    pub(in crate::kernel) fn integer_application(&self) -> Option<SharedPureApplication> {
        let KernelTermNode::Call { name, arguments } = self.node() else {
            return None;
        };
        if let Some(MachineLeaf::Application(application)) = self.0.machine_leaf.0.get() {
            return Some(application.clone());
        }
        let mut export = KernelTermExport::default();
        let arguments = arguments
            .iter()
            .map(|arg| export.argument(arg))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        let application = SharedPureApplication::intern(name.clone(), arguments);
        self.0.machine_leaf.retain_application(&application);
        Some(application)
    }

    pub(super) fn integer_reading(&self) -> &OnceLock<Option<SharedIntegerTerm>> {
        &self.0.integer_reading
    }

    #[cfg(test)]
    pub(crate) fn has_cached_native_argument(&self) -> bool {
        self.0.argument_leaf.get().is_some() || self.0.integer_output.get().is_some()
    }

    pub(crate) fn id(&self) -> u64 {
        self.0.id
    }

    pub(crate) fn machine_constant_reading(&self) -> Option<&KernelMachineLiteral> {
        self.0
            .key
            .0
            .machine_constant
            .get_or_init(|| machine::native_constant_reading(self.written_machine_input()?))
            .as_ref()
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

    /// This Integer uses only literals, variables, arithmetic, and
    /// mathematical folds. Its exact identity needs no native carrier.
    pub(crate) fn is_mathematical_integer(&self) -> bool {
        self.0.key.0.mathematical_integer
    }

    /// Arithmetic with typed shared machine observations and no internal binders.
    pub(crate) fn is_integer_observation_arithmetic(&self) -> bool {
        self.0.key.0.integer_observation_arithmetic
    }

    pub(super) fn integer_exact_key(&self) -> Option<IntegerShallowKey> {
        if self.is_mathematical_integer() {
            return Some(IntegerShallowKey::mathematical(self));
        }
        if self.ty() != &KernelType::Integer {
            return None;
        }
        Some(self.mixed_integer_identity().key.clone())
    }

    pub(super) fn retained_integer_exact_id(&self) -> Option<u64> {
        if self.is_mathematical_integer() {
            return Some(SharedIntegerTerm::mathematical_id(self));
        }
        if self.ty() != &KernelType::Integer {
            return None;
        }
        Some(self.mixed_integer_identity().id)
    }

    pub(super) fn remember_integer_identity(&self, term: &IntegerTerm) {
        if self.is_mathematical_integer() {
            return;
        }
        self.0.integer_identity.get_or_init(|| {
            let observation = match term {
                IntegerTerm::Machine(observation) => Some(observation.clone()),
                _ => None,
            };
            IntegerIdentity::retained(term.shallow_key(), observation)
        });
    }

    fn mixed_integer_identity(&self) -> &IntegerIdentity {
        if let Some(identity) = self.0.integer_identity.get() {
            return identity;
        }
        let child_id =
            |child: &KernelTerm| child.retained_integer_exact_id().expect("Integer child");
        let mut pending = vec![(self, false)];
        while let Some((root, expanded)) = pending.pop() {
            if root.ty() != &KernelType::Integer
                || root.is_mathematical_integer()
                || root.0.integer_identity.get().is_some()
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if !expanded {
                let children = match root.node() {
                    KernelTermNode::IntegerOperation { arguments, .. } => arguments.as_slice(),
                    KernelTermNode::IntegerIf { arguments } => &arguments[1..],
                    KernelTermNode::Fold(fold) => fold.arguments.as_slice(),
                    KernelTermNode::Match(matched) => &matched.arguments[1..],
                    KernelTermNode::Call { arguments, .. } => arguments.as_slice(),
                    _ => &[],
                };
                if !children.is_empty() {
                    pending.push((root, true));
                    pending.extend(children.iter().rev().map(|child| (child, false)));
                    continue;
                }
            }
            let (key, observation) = match root.node() {
                KernelTermNode::MachineObservation { .. } => {
                    let observation = root
                        .exact_shared_integer_observation()
                        .expect("retained Integer observation");
                    (
                        IntegerShallowKey::Machine(observation.id()),
                        Some(observation),
                    )
                }
                KernelTermNode::IntegerOperation {
                    operator,
                    arguments,
                } => (
                    IntegerShallowKey::operation(
                        *operator,
                        child_id(&arguments[0]),
                        arguments.get(1).map(child_id),
                    ),
                    None,
                ),
                KernelTermNode::IntegerIf {
                    arguments: [condition, yes, no],
                } => {
                    let condition = KernelTermExport::condition(condition).expect("Integer guard");

                    (
                        IntegerShallowKey::If(Box::new(condition), child_id(yes), child_id(no)),
                        None,
                    )
                }
                KernelTermNode::Fold(fold) if fold.index == KernelFoldIndex::Integer => {
                    let [start, end, initial, body] = &fold.arguments;
                    (
                        IntegerShallowKey::RangeFold(
                            IntegerRangeIdentity::Integer(child_id(start), child_id(end)),
                            child_id(initial),
                            fold.accumulator,
                            fold.item,
                            child_id(body),
                        ),
                        None,
                    )
                }
                _ => (
                    root.integer_native_compat()
                        .expect("Integer identity")
                        .shallow_key(),
                    None,
                ),
            };
            root.0
                .integer_identity
                .get_or_init(|| IntegerIdentity::retained(key, observation));
        }
        self.0
            .integer_identity
            .get()
            .expect("registered Integer identity")
    }

    /// Exact observation used by Integer identity and rule W.
    pub(crate) fn exact_shared_integer_observation(&self) -> Option<SharedMachineIntegerTerm> {
        let KernelTermNode::MachineObservation { format, operand } = self.node() else {
            return None;
        };
        if let KernelTermNode::MachineObservationInput {
            observation,
            exact: true,
            ..
        } = operand.node()
        {
            return Some(observation.clone());
        }
        if let Some(observation) = self
            .0
            .integer_identity
            .get()
            .and_then(|identity| identity.observation.as_ref())
            && observation.shared_operand() == Some(operand)
        {
            return Some(observation.clone());
        }
        SharedMachineIntegerTerm::from_shared(*format, operand.clone()).or_else(|| {
            Some(SharedMachineIntegerTerm::intern(
                *format,
                KernelTermExport::machine(operand).ok()?,
            ))
        })
    }

    pub(super) fn retained_range_endpoint(&self) -> Option<SharedMachineIntegerTerm> {
        match self.node() {
            KernelTermNode::MachineObservationInput {
                observation,
                exact: false,
                ..
            } => Some(observation.clone()),
            _ => None,
        }
    }

    pub(in crate::kernel) fn is_literal_integer_arithmetic(&self) -> bool {
        self.0.key.0.literal_integer_arithmetic
    }

    pub(in crate::kernel::primitives) fn intern(ty: KernelType, node: KernelTermNode) -> Self {
        crate::instrumentation::record_deterministic_work(match &node {
            KernelTermNode::IntegerOperation { arguments, .. } => arguments.len() + 1,
            KernelTermNode::Call { name, arguments } => name.len() + arguments.len() + 1,
            KernelTermNode::IntegerLiteral(value) => value.bits() as usize + 1,
            _ => 1,
        });
        Self::intern_node(ty, node)
    }

    // Native Integer interning is a shallow identity lookup. Its callers
    // charge the operation or literal they construct, as before.
    pub(super) fn intern_native_integer(node: KernelTermNode) -> Self {
        Self::intern_node(KernelType::Integer, node)
    }

    fn intern_node(ty: KernelType, node: KernelTermNode) -> Self {
        static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
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
            KernelTermNode::ObservedPointer(value) => std::slice::from_ref(value.source()),
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
    /// Retain an already-native opaque machine operand at a shared parent.
    /// The identity belongs to its explicit typed input, never to an export of
    /// a shared tree.
    pub(crate) fn retained_machine_operand(
        format: MachineIntegerType,
        operand: MachineOperandView<'_>,
    ) -> Self {
        if let MachineOperandView::Old(value) = operand
            && let Some(root) = KernelTermImport::default().float_to_machine(format, value)
        {
            return root;
        }
        match operand {
            MachineOperandView::Shared(root) => root.with_machine_observation_type(format),
            MachineOperandView::Old(_) if operand.binary().is_some() => {
                let (operation_format, op, children) = operand.binary().unwrap();
                Self::machine_binary_shared_as(
                    format,
                    operation_format,
                    op,
                    children.map(|child| Self::retained_machine_operand(operation_format, child)),
                )
            }
            MachineOperandView::Old(_) if operand.unary().is_some() => {
                let (operation_format, op, child) = operand.unary().unwrap();
                Self::machine_unary_shared(
                    operation_format,
                    op,
                    Self::retained_machine_operand(operation_format, child),
                )
                .with_machine_observation_type(format)
            }
            MachineOperandView::Old(_) if operand.cast().is_some() => {
                let (encoding, source, destination, child) = operand.cast().unwrap();
                Self::machine_cast_shared(
                    encoding,
                    source,
                    destination,
                    Self::retained_machine_operand(source, child),
                )
                .with_machine_observation_type(format)
            }
            MachineOperandView::Old(OldMachineTerm::If {
                condition,
                then_term,
                else_term,
            }) => Self::machine_if_shared(
                format,
                [
                    KernelTermImport::default().condition(condition),
                    Self::retained_machine_operand(format, MachineOperandView::Old(then_term)),
                    Self::retained_machine_operand(format, MachineOperandView::Old(else_term)),
                ],
            ),
            MachineOperandView::Old(value) => Self::retained_native_machine_operand(format, value),
        }
    }

    /// Import one explicit native operand without splitting an opaque
    /// composite. Its native observation identity must survive when a checker
    /// puts it beside a shared operand in a new operation.
    pub(crate) fn retained_native_machine_operand(
        format: MachineIntegerType,
        value: &OldMachineTerm,
    ) -> Self {
        KernelTermImport::default()
            .machine_arithmetic(format, value)
            .unwrap_or_else(|| Self::written_machine_operand(format, value))
    }

    /// Preserve the exact native operand for an output that must reproduce
    /// its written syntax. Compound inputs can carry distinct declaration
    /// metadata even when they compare equal.
    pub(in crate::kernel) fn written_machine_operand(
        format: MachineIntegerType,
        value: &OldMachineTerm,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::WrittenMachine(KernelWrittenMachine::expression(format, value)),
        )
    }

    /// An opaque address index already owns its exact producer syntax and
    /// semantic identity. Keep both through offset import and checked reads.
    pub(super) fn retain_address_index(index: &SharedMachineIntegerTerm) -> Self {
        if let Some(root) = index.shared_operand() {
            return root.clone();
        }
        Self::intern(
            KernelType::Program(index.ty().program_type()),
            KernelTermNode::WrittenMachine(KernelWrittenMachine {
                format: index.ty(),
                source: WrittenMachineSource::AddressIndex(index.clone()),
            }),
        )
    }

    pub(super) fn retained_address_index(
        &self,
        format: MachineIntegerType,
    ) -> Option<&SharedMachineIntegerTerm> {
        let KernelTermNode::WrittenMachine(input) = self.node() else {
            return None;
        };
        match &input.source {
            WrittenMachineSource::AddressIndex(index) if index.ty() == format => Some(index),
            _ => None,
        }
    }

    /// Rebuild a selected native leaf while preserving a common call producer.
    /// No-op rewrites keep exact payload metadata, as on the native path.
    pub(crate) fn rewritten_machine_leaf(
        &self,
        format: MachineIntegerType,
        original: &OldMachineTerm,
        rewritten: &OldMachineTerm,
    ) -> Self {
        if matches!(
            self.node(),
            KernelTermNode::MachineObservationInput { .. }
                | KernelTermNode::WrittenMachine(_)
                | KernelTermNode::Call { .. }
                | KernelTermNode::IntegerAddress { .. }
        ) && rewritten == original
        {
            return self.clone();
        }
        if matches!(self.node(), KernelTermNode::Call { .. })
            && let OldMachineTerm::ClickFunctionApplication { name, arguments } = rewritten
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
        observation: SharedMachineIntegerTerm,
    ) -> Self {
        Self::machine_observation_input(format, observation, false)
    }

    fn machine_observation_input(
        format: MachineIntegerType,
        observation: SharedMachineIntegerTerm,
        exact: bool,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::MachineObservationInput {
                format,
                observation,
                exact,
            },
        )
    }

    /// Observe the selected written descriptor through its producer. Identity
    /// follows its native equality contract, and output borrows that same slot.
    pub(super) fn observe_written_argument(source: &Self) -> Self {
        debug_assert!(source.written_argument().is_some());
        Self::intern(
            source.ty().clone(),
            KernelTermNode::ObservedArgument(KernelObservedArgument(source.clone())),
        )
    }

    fn written_call_argument(application: &SharedPureApplication, index: usize) -> Self {
        let slot = KernelCallArgument {
            application: application.clone(),
            index,
        };
        let ty = Self::native_argument_type(slot.value());
        let node = if let Some((carrier, _)) = KernelImportedScalar::call_input(&slot) {
            KernelTermNode::ImportedScalar(KernelImportedScalar {
                carrier,
                source: ImportedScalarSource::Call {
                    argument: slot,
                    observed: false,
                },
            })
        } else {
            KernelTermNode::CallArgument(slot)
        };
        Self::intern(ty, node)
    }

    fn imported_scalar(ty: ProgramType, value: &OldMachineTerm) -> Self {
        Self::intern(
            KernelType::Program(ty),
            KernelTermNode::ImportedScalar(KernelImportedScalar {
                carrier: ty,
                source: ImportedScalarSource::Exact(Arc::new(value.clone())),
            }),
        )
    }

    pub(super) fn observe_imported_scalar(&self, input: &KernelImportedScalar) -> Self {
        let source = match &input.source {
            ImportedScalarSource::Exact(value) => ImportedScalarSource::Observed(value.clone()),
            ImportedScalarSource::Call {
                argument,
                observed: false,
            } => ImportedScalarSource::Call {
                argument: argument.clone(),
                observed: true,
            },
            _ => return self.clone(),
        };
        Self::intern(
            self.ty().clone(),
            KernelTermNode::ImportedScalar(KernelImportedScalar {
                carrier: input.carrier,
                source,
            }),
        )
    }

    fn imported_scalar_as_native(input: &KernelImportedScalar) -> ProgramValue {
        let term = input.value().clone();
        if let Some(format) = MachineIntegerType::from_program_type(input.carrier) {
            machine::wrap_exact(format, term)
        } else if let Some(format) = KernelFloatType::from_program_type(input.carrier) {
            format.value(term)
        } else {
            debug_assert_eq!(input.carrier, ProgramType::Bool);
            ProgramValue::Bool(term)
        }
    }

    pub(crate) fn requires_native_argument_input(&self) -> bool {
        matches!(
            self.node(),
            KernelTermNode::NativeDescriptor(_)
                | KernelTermNode::ObservedArgument(_)
                | KernelTermNode::ImportedScalar(_)
        )
    }

    /// Borrow an explicitly written argument or a still-native input.
    pub(crate) fn written_argument(&self) -> Option<&PureFunctionArgument> {
        match self.node() {
            KernelTermNode::CallArgument(argument) => Some(argument.value()),
            KernelTermNode::ImportedScalar(KernelImportedScalar {
                source: ImportedScalarSource::Call { argument, .. },
                ..
            }) => Some(argument.value()),
            KernelTermNode::ObservedArgument(argument) => Some(argument.value()),
            KernelTermNode::NativeDescriptor(descriptor) => Some(&descriptor.0),
            _ => None,
        }
    }

    fn native_argument_type(argument: &PureFunctionArgument) -> KernelType {
        match argument {
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
        }
    }
}

/// One conversion per shared source node, including shared call arguments.
/// This bridge is removed as producers construct KernelTerm directly.
#[derive(Default)]
pub(crate) struct KernelTermImport {
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

    /// Every supported expression imports through its own shape. Opaque
    /// descriptor input retains the exact C record or the invalid array
    /// descriptor for compatibility with the existing refusal route.
    pub(crate) fn argument(&mut self, argument: &PureFunctionArgument) -> KernelTerm {
        if let Some(root) = self.structural_argument(argument) {
            return root;
        }
        if let PureFunctionArgument::Value(ProgramValue::Bool(word)) = argument {
            return KernelTerm::imported_scalar(ProgramType::Bool, word);
        }
        let descriptor = match argument {
            PureFunctionArgument::Value(ProgramValue::Void | ProgramValue::PointerInteger(_))
            | PureFunctionArgument::ArrayRef { .. } => argument.clone(),
            _ => unreachable!("supported expression did not import"),
        };
        KernelTerm::intern(
            KernelTerm::native_argument_type(argument),
            KernelTermNode::NativeDescriptor(KernelNativeDescriptor(Arc::new(descriptor))),
        )
    }

    pub(super) fn structural_argument(
        &mut self,
        argument: &PureFunctionArgument,
    ) -> Option<KernelTerm> {
        let root = match argument {
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
                    OldMachineTerm::Constant {
                        format: MachineIntegerType::UInt8,
                        bits,
                    } if *bits <= 1 => KernelTerm::boolean_literal(*bits != 0),
                    OldMachineTerm::Variable(variable) => {
                        KernelTerm::variable(KernelType::Program(ProgramType::Bool), *variable)
                    }
                    OldMachineTerm::BoolCast {
                        to: MachineIntegerType::UInt8,
                        value,
                    } if !matches!(value.as_ref(), OldConditionTerm::Constant(_)) => {
                        self.condition(value)
                    }
                    // Other C-word carriers retain their original width and
                    // bits. Importing an argument must not normalize its truth.
                    _ => return None,
                },
                ProgramValue::Parameter(value) => {
                    KernelTerm::program_parameter(self.algebraic(value))
                }
                ProgramValue::Pointer(value) => {
                    KernelTerm::shared_pointer_value(value.shared().clone())
                }
                // Void has no expression. A complete pointer/integer record is
                // the package-7 value descriptor, not its numeric projection.
                ProgramValue::Void | ProgramValue::PointerInteger(_) => return None,
            },
            PureFunctionArgument::ArrayRef {
                point,
                pointer,
                element_type,
            } => match pointer {
                ProgramValue::Pointer(pointer) => KernelTerm::shared_array_reference(
                    point.clone(),
                    KernelTerm::shared_pointer_value(pointer.shared().clone()),
                    *element_type,
                ),
                // Preserve the existing refusal boundary for a non-pointer
                // descriptor rather than inventing an address for it.
                _ => return None,
            },
        };
        Some(root)
    }
    pub(crate) fn integer(&mut self, term: &SharedIntegerTerm) -> KernelTerm {
        term.root().clone()
    }

    pub(super) fn integer_input(&mut self, term: &IntegerTerm) -> KernelTerm {
        use KernelIntegerOperator as Op;
        match term {
            IntegerTerm::Constant(value) => KernelTerm::integer_literal(value.clone()),
            IntegerTerm::Variable(variable) => KernelTerm::variable(KernelType::Integer, *variable),
            IntegerTerm::Machine(machine) => {
                KernelTerm::intern_native_integer(KernelTermNode::MachineObservation {
                    format: machine.ty(),
                    operand: machine.shared_operand().cloned().unwrap_or_else(|| {
                        KernelTerm::machine_observation_input(machine.ty(), machine.clone(), true)
                    }),
                })
            }
            IntegerTerm::Negate(inner) => {
                KernelTerm::intern_native_integer(KernelTermNode::IntegerOperation {
                    operator: Op::Negate,
                    arguments: vec![self.integer(inner)],
                })
            }
            IntegerTerm::Add(a, b)
            | IntegerTerm::Subtract(a, b)
            | IntegerTerm::Multiply(a, b)
            | IntegerTerm::TruncatingQuotient(a, b)
            | IntegerTerm::TruncatingRemainder(a, b) => {
                let operator = match term {
                    IntegerTerm::Add(..) => Op::Add,
                    IntegerTerm::Subtract(..) => Op::Subtract,
                    IntegerTerm::Multiply(..) => Op::Multiply,
                    IntegerTerm::TruncatingQuotient(..) => Op::TruncatingQuotient,
                    _ => Op::TruncatingRemainder,
                };
                KernelTerm::intern_native_integer(KernelTermNode::IntegerOperation {
                    operator,
                    arguments: vec![self.integer(a), self.integer(b)],
                })
            }
            IntegerTerm::PureFunctionApplication(application) => {
                let arguments = application
                    .arguments()
                    .iter()
                    .enumerate()
                    .map(|(index, _)| {
                        application.common_argument(index).unwrap_or_else(|| {
                            KernelTerm::written_call_argument(application, index)
                        })
                    })
                    .collect();
                let root = KernelTerm::intern_native_integer(KernelTermNode::Call {
                    name: application.name().into(),
                    arguments,
                });
                root.0
                    .machine_leaf
                    .0
                    .get_or_init(|| MachineLeaf::Application(application.clone()));
                root
            }
            IntegerTerm::If {
                condition,
                then_term,
                else_term,
            } => KernelTerm::intern_native_integer(KernelTermNode::IntegerIf {
                arguments: [
                    self.condition(condition),
                    self.integer(then_term),
                    self.integer(else_term),
                ],
            }),
            IntegerTerm::RangeFold { .. } => KernelFold::import_integer(self, term)
                .expect("Integer fold payload")
                .into_term(),
            IntegerTerm::AlgebraicMatch { .. } => KernelMatch::import_integer(self, term)
                .expect("Integer match payload")
                .into_term(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_integer_handles_have_constant_work_across_sessions() {
        use crate::instrumentation::measure_deterministic_work;
        let source: SharedIntegerTerm = IntegerTerm::If {
            condition: Box::new(OldConditionTerm::Variable(Variable(87654329))),
            then_term: IntegerTerm::constant_i64(17).into(),
            else_term: IntegerTerm::constant_i64(18).into(),
        }
        .into();
        let import = || {
            let _session = crate::kernel::VerificationSession::enter();
            let (term, cold) =
                measure_deterministic_work(|| KernelTermImport::default().integer(&source));
            let (again, warm) =
                measure_deterministic_work(|| KernelTermImport::default().integer(&source));
            assert_eq!(term, again);
            assert_eq!((cold, warm), (0, 0));
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
            assert_eq!((cold, warm), (0, 0));
            cold
        };
        assert_eq!(export(), export());
    }

    #[test]
    fn integer_handles_share_the_same_root_without_a_native_view() {
        let source: SharedIntegerTerm = IntegerTerm::If {
            condition: Box::new(OldConditionTerm::Variable(Variable(87654321))),
            then_term: IntegerTerm::constant_i64(19).into(),
            else_term: IntegerTerm::constant_i64(20).into(),
        }
        .into();
        let weak = source.downgrade();
        let common = KernelTermImport::default().integer(&source);
        drop(source);
        assert_eq!(weak.upgrade().as_ref(), Some(&common));
        assert_eq!(common.ty(), &KernelType::Integer);
        let reconstructed = KernelTermExport::default().integer(&common).unwrap();
        assert_eq!(reconstructed.root(), &common);
        assert!(!common.has_cached_native_argument());
        drop((reconstructed, common));
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn mathematical_integer_uses_common_identity_across_sessions() {
        use crate::instrumentation::measure_deterministic_work;
        let input = IntegerTerm::Add(
            IntegerTerm::Variable(Variable(87654327)).into(),
            IntegerTerm::constant_i64(21).into(),
        );
        let source = SharedIntegerTerm::intern(input.clone());
        let root = source.mathematical_root().unwrap();
        for _ in 0..2 {
            let _session = crate::kernel::VerificationSession::enter();
            let (imported, import_work) =
                measure_deterministic_work(|| KernelTermImport::default().integer(&source));
            let (exported, export_work) = measure_deterministic_work(|| {
                KernelTermExport::default().integer(&imported).unwrap()
            });
            assert_eq!(&imported, root);
            assert_eq!(exported, source);
            assert_eq!((import_work, export_work), (0, 0));
            assert!(!root.has_cached_native_argument());
        }
        assert_eq!(&input, source.as_ref());
        let weak = Arc::downgrade(&root.0);
        drop(source);
        assert!(weak.upgrade().is_none());
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
            assert_eq!(source.root(), &common);
            assert!(!common.has_cached_native_argument());
            drop(source);
            super::super::integer::clear_machine_observation_memo();
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
    fn atomic_shared_observation_needs_no_forward_integer_link() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let operand = KernelTerm::variable(
            KernelType::Program(format.program_type()),
            Variable(87654326),
        );
        let observation = SharedMachineIntegerTerm::from_shared(format, operand).unwrap();
        let source: SharedIntegerTerm = IntegerTerm::Machine(observation).into();
        let common = KernelTermImport::default().integer(&source);
        let restored = KernelTermExport::default().integer(&common).unwrap();
        assert_eq!(restored, source);
        assert_eq!(source.root(), &common);
        assert!(!common.has_cached_native_argument());
        assert_eq!(KernelTermImport::default().integer(&source), common);
    }

    #[test]
    fn integer_conversion_observations_keep_unmigrated_payloads_outside_the_fragment() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let value = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "opaque_argument".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                OldMachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
                    Box::new(Address::symbolic(Variable(87654328))),
                    LoadKind::Int32,
                ),
            ))],
        ));
        let native = OldMachineTerm::IntegerToMachine {
            value: value.into(),
            destination: format,
        };
        let mut importer = KernelTermImport::default();
        let root = importer.machine(format, &native);
        assert!(root.has_opaque_observation_boundary());
        assert!(SharedMachineIntegerTerm::from_shared(format, root.clone()).is_none());
        assert!(importer.machine_arithmetic(format, &native).is_none());
        assert_eq!(KernelTermExport::machine(&root).unwrap(), native);

        use crate::kernel::machine_integer::definedness::{
            integer_bounds_of_definedness, range_domain_query,
        };
        let condition = OldConditionTerm::Overflows {
            format,
            op: OverflowOperation::Add,
            left: Box::new(native),
            right: Box::new(OldMachineTerm::constant(1)),
        };
        let shared = StoredConditionTerm::from_root(importer.condition(&condition)).unwrap();
        let source = Proposition::condition_is(condition, false);
        let shared = Proposition::condition_is(shared, false);
        let bounds = integer_bounds_of_definedness(&source);
        assert_eq!(bounds.len(), 2);
        assert_eq!(integer_bounds_of_definedness(&shared), bounds);
        assert_eq!(
            range_domain_query(&shared).unwrap().bounds().as_slice(),
            bounds
        );
    }

    #[test]
    fn observation_storage_shares_casts_but_keeps_opaque_compatibility_boundaries() {
        let format = MachineIntegerType::Int32;
        let cast = OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: MachineIntegerType::Int8,
            to: format,
            value: Box::new(OldMachineTerm::Variable(Variable(87654326))),
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
        let opaque = KernelTerm::imported_scalar(
            format.program_type(),
            &OldMachineTerm::Variable(Variable(87654327)),
        );
        let parent =
            KernelTerm::arithmetic_binary(format, MachineBinaryOp::Add, [opaque.clone(), opaque])
                .unwrap();
        assert!(!parent.is_shared_machine_operand());
        assert!(SharedMachineIntegerTerm::from_shared(format, parent).is_none());
    }

    #[test]
    fn closed_comparisons_read_literals_inside_producer_arguments() {
        let word = OldMachineTerm::constant(u32::MAX);
        let application = SharedPureApplication::intern(
            "closed_arguments".into(),
            vec![
                PureFunctionArgument::Value(ProgramValue::Int32(word.clone())),
                PureFunctionArgument::Integer(IntegerTerm::constant(0.into()).into()),
            ],
        );
        let format = MachineIntegerType::Int32;
        let zero = KernelTerm::integer_to_machine(
            format,
            KernelTerm::written_call_argument(&application, 1),
        )
        .unwrap();
        for left in [
            KernelTerm::imported_scalar(ProgramType::Int32, &word),
            KernelTerm::written_call_argument(&application, 0),
        ] {
            let comparison = KernelTerm::boolean_comparison_raw(
                format,
                CompareRelation::LessThan,
                [left, zero.clone()],
            );
            assert_eq!(
                crate::kernel::machine_integer::comparison::closed_condition_value(
                    BooleanOperandView::Shared(&comparison)
                ),
                Some(true)
            );
            assert!(!comparison.has_cached_native_argument());
        }
    }

    #[test]
    fn wide_comparison_reads_wrapped_operands_with_their_written_literal_rules() {
        use MachineIntegerType::{Int32, Int64};
        let literal = OldMachineTerm::constant(2);
        let computed = OldMachineTerm::Binary {
            format: Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(OldMachineTerm::constant(1)),
            right: Box::new(OldMachineTerm::constant(1)),
        };
        let wide_sum = OldMachineTerm::Binary {
            format: Int64,
            op: MachineBinaryOp::Add,
            left: Box::new(OldMachineTerm::int64_constant(1)),
            right: Box::new(OldMachineTerm::int64_constant(1)),
        };
        let wide =
            |n| KernelTermImport::default().machine(Int64, &OldMachineTerm::int64_constant(n));
        for (ty, input, shifted, widened) in [
            (Int32, literal, Some(true), Some(true)),
            (Int32, computed, None, None),
            (Int64, wide_sum, None, Some(true)),
        ] {
            let wrapped = KernelTerm::imported_scalar(ty.program_type(), &input);
            let shift = KernelTerm::machine_binary_shared(
                Int64,
                MachineBinaryOp::ShiftLeft,
                [wide(1), wrapped.clone()],
            );
            let cast = KernelTerm::machine_cast_shared(
                MachineCastSpelling::Int64From32,
                Int32,
                Int64,
                wrapped,
            );
            for (term, rhs, expected) in [(shift, 4, shifted), (cast, 2, widened)] {
                let root = KernelTerm::boolean_comparison_raw(
                    Int64,
                    CompareRelation::Equal,
                    [term, wide(rhs)],
                );
                assert_eq!(
                    crate::kernel::machine_integer::comparison::closed_condition_value(
                        BooleanOperandView::Shared(&root)
                    ),
                    expected
                );
                assert!(!root.has_cached_native_argument());
            }
        }
    }

    #[test]
    fn machine_observation_retains_its_format_and_reconstructs_after_source_drop() {
        let word = OldMachineTerm::Variable(Variable(87654322));
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
        let input = PureFunctionArgument::Value(ProgramValue::UInt32(OldMachineTerm::Variable(
            Variable(70),
        )));
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
            condition: Box::new(OldConditionTerm::Variable(Variable(993402))),
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
        assert_eq!(weak.upgrade().as_ref(), Some(&common));
        assert!(!common.has_cached_native_argument());
        let restored = KernelTermExport::default().integer(&common).unwrap();
        assert_eq!(KernelTermImport::default().integer(&restored), common);
    }

    #[test]
    fn legacy_pointer_equality_does_not_discard_auxiliary_qualifiers() {
        let pointer = Pointer::new(Address::symbolic(Variable(76)), ProgramType::Int32Pointer);
        let constant = pointer.clone().with_declared_object_class(Some(
            crate::kernel::effective_type::CAccessClass::Scalar(
                crate::kernel::effective_type::CScalarClass::Int,
            ),
        ));
        assert_eq!(
            pointer, constant,
            "the declared class is auxiliary, not pointer identity"
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
        assert!(restored.object_class().is_some());
        let PureFunctionArgument::Value(ProgramValue::Pointer(restored)) =
            KernelTermExport::default().argument(&plain).unwrap()
        else {
            panic!("pointer")
        };
        assert!(restored.object_class().is_none());
    }

    #[test]
    fn legacy_adapter_keeps_complete_pointers_and_scoped_integer_nodes() {
        let base = Address::symbolic(Variable(75));
        let root = Pointer::new(base.clone(), ProgramType::Int32Pointer);
        let member = root
            .clone()
            .with_bounds(Some(SubobjectBounds::new(base, 4u32.into())));
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
            condition: Box::new(OldConditionTerm::Constant(true)),
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
#[cfg(test)]
thread_local! {
    static INTEGER_EXPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl KernelTermExport {
    pub(crate) fn argument(
        &mut self,
        term: &KernelTerm,
    ) -> Result<PureFunctionArgument, &'static str> {
        if let KernelTermNode::WrittenMachine(input) = term.node() {
            return Ok(PureFunctionArgument::Value(machine::wrap_exact(
                input.format(),
                input.value().clone(),
            )));
        }
        if let KernelTermNode::ObservedPointer(value) = term.node() {
            return self.argument(value.source());
        }
        if let Some(argument) = term.written_argument() {
            return Ok(argument.clone());
        }
        if let KernelTermNode::ImportedScalar(input) = term.node() {
            return Ok(PureFunctionArgument::Value(
                KernelTerm::imported_scalar_as_native(input),
            ));
        }
        if FloatOperandView::from_shared(term).is_some() {
            return Self::float(term).map(PureFunctionArgument::Value);
        }
        if let Some(value) = term.old_boolean_argument() {
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
                            OldMachineTerm::Variable(*variable),
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
        if term.ty() == &KernelType::Integer {
            return Ok(PureFunctionArgument::Integer(SharedIntegerTerm::from_root(
                term.clone(),
            )));
        }
        if let KernelTermNode::MachineObservationInput {
            format,
            observation,
            ..
        } = term.node()
        {
            return Ok(PureFunctionArgument::Value(machine::wrap_exact(
                *format,
                observation.value().clone(),
            )));
        }
        if let KernelType::Program(program_type) = term.ty()
            && let Some(format) = MachineIntegerType::from_program_type(*program_type)
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
            KernelTermNode::PointerRead { value, .. }
            | KernelTermNode::PointerArithmetic { value, .. }
            | KernelTermNode::PointerCall { value, .. }
            | KernelTermNode::Pointer(value) => {
                PureFunctionArgument::Value(ProgramValue::Pointer(value.export()?))
            }
            KernelTermNode::ArrayReference { .. } => term.old_pointer_argument().unwrap().clone(),
            KernelTermNode::ProgramParameter { operand } => PureFunctionArgument::Value(
                ProgramValue::Parameter(Box::new(self.algebraic(operand)?)),
            ),
            _ => return Err("kernel term sort has not migrated to the checker bridge"),
        };
        self.values.insert(term.clone(), value.clone());
        Ok(value)
    }
    #[cfg(test)]
    pub(crate) fn integer_export_count() -> usize {
        INTEGER_EXPORT_COUNT.with(std::cell::Cell::get)
    }

    pub(crate) fn integer(&mut self, term: &KernelTerm) -> Result<SharedIntegerTerm, &'static str> {
        #[cfg(test)]
        INTEGER_EXPORT_COUNT.with(|count| count.set(count.get() + 1));
        match self.argument(term)? {
            PureFunctionArgument::Integer(value) => Ok(value),
            _ => Err("expected Integer kernel term"),
        }
    }
}

#[cfg(test)]
mod mixed_arguments;
