//! Typed term classes inside the trusted graph: offset addition congruence and
//! int32 addition and registered same-state int32 loads, connected by int32
//! scaling. Full-width scaling retains its signed interpretation. Unsigned
//! division/remainder and bitwise XOR have congruence only;
//! UInt64 arithmetic/bitwise applications, pointer addresses and complete
//! same-state 64-bit reads share those classes. Other integer operators
//! and conversions use typed curried applications; congruence supplies no
//! arithmetic definedness. Floating-point expressions and binders stay opaque.
//! Application signatures use operand classes; parent-use indexes propagate late
//! merges. Equal addresses in one block also equate their byte offsets.
//! No general scalar arithmetic solving or injectivity runs here. Residue
//! projection retains word-constructor folding identities via indexed nodes.
//! Shallow keys preserve widths, signedness, and machine-term state identity.

use super::{
    AffineOffset, MachineAtom, OffsetAtom, Pointer, PointerBlock, PointerOffsetTerm, Variable,
};
use crate::kernel::unary_node;
use crate::kernel::unary_term;
use crate::kernel::{MachineBinaryOp, MachineIntegerType};
use crate::kernel::{bits32_constant, constant_i64, constant_u64, int64_constant, uint64_constant};
use crate::persistent::{PersistentMap, PersistentSet};
use std::sync::Arc;

mod congruence;
pub(super) mod constants;
mod machine_relations;
mod shared_machine;
pub(super) use congruence::has_machine_operands;

/// The sort of a read that may meet a stored cell under an aliased address.
/// A stored data pointer is not: it reaches its read only through checked
/// read evidence (`checked_pointer_read_stored_value`). A stored function
/// pointer value has no object provenance to check, so a function pointer
/// read meets a function pointer cell directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CellRead {
    Int32,
    UInt64,
    FunctionPointer,
    /// An 8- or 16-bit read, equal to a stored value of its width.
    Narrow(crate::kernel::CarrierWidth),
}

/// Shallow registration key: the read, its exact state and observation
/// source, and the graph's address application before class normalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct WideReadSource {
    read: u64,
    retained_state: (u32, u32),
    origin: Option<(u32, u32)>,
    address: u64,
}

/// A read to look up, and the blocks to look in: all of its block class, or
/// only the members a union just brought to it.
#[derive(Clone)]
pub(super) struct PendingCellRead {
    pub(super) read: u64,
    pub(super) memory: crate::kernel::SharedMemory,
    // The memory a load variable was read in, at its naming state.
    pub(super) origin: Option<crate::kernel::SharedMemory>,
    pub(super) pointer: Pointer,
    pub(super) kind: CellRead,
    pub(super) only: Option<Arc<[(PointerBlock, AffineOffset)]>>,
}

/// The memory a load variable was read in, when it is the naming state
/// under another value: an observed cell names a value without changing
/// memory, so it keeps the state identity and may hold cells the naming
/// value lacks. An origin at another state is not consulted; the graph
/// does not equate distinct states.
fn load_origin(
    term: &crate::kernel::MachineTerm,
    named: &crate::kernel::SharedMemory,
) -> Option<crate::kernel::SharedMemory> {
    crate::kernel::eval::scalar_read_observation(crate::kernel::MachineOperandView::Legacy(term))
        .and_then(|read| read.origin)
        .filter(|origin| origin.read_identity() == named.read_identity())
}

/// The producer distinguishes affine definitions from assumed equalities.
/// Keep that distinction on each edge through iterative congruence closure.
#[derive(Default)]
struct PendingUnions(Vec<(u64, u64, bool)>);

impl PendingUnions {
    fn push(&mut self, (left, right): (u64, u64)) {
        self.0.push((left, right, false));
    }

    fn push_definition(&mut self, (left, right): (u64, u64)) {
        self.0.push((left, right, true));
    }
}

#[cfg(test)]
thread_local! {
    static POINTER_FACT_MERGE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn take_pointer_fact_merge_visits() -> usize {
    POINTER_FACT_MERGE_VISITS.with(|visits| visits.replace(0))
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::kernel::equality_graph) enum PointerFactKey {
    AddressSeparation,
    Predicate(u64),
    PredicateShape(String, usize, usize, crate::kernel::ProgramType),
    FunctionContracts,
    ObjectType(crate::kernel::effective_type::CAccessClass),
}

/// The type-erased source handle breaks the recursive Send/Sync type path
/// through checked fact metadata and memory construction. It retains the
/// original immutable allocation; its address is a safe shallow source key.
pub(super) trait PointerFactSource: Send + Sync {
    fn proposition(&self) -> &crate::kernel::Proposition;
}

impl PointerFactSource for crate::kernel::ExecutionPureFact {
    fn proposition(&self) -> &crate::kernel::Proposition {
        self.proposition()
    }
}

/// Retain exact source identity for removal, and admission order for iteration.
/// Allocation addresses are lookup keys only; proof search never orders by them.
#[derive(Clone, Default)]
pub(super) struct PointerFactSources {
    identities: PersistentMap<usize, usize>,
    sources: PersistentMap<usize, Arc<dyn PointerFactSource>>,
    next: usize,
}

impl PointerFactSources {
    pub(super) fn insert(&mut self, identity: usize, source: Arc<dyn PointerFactSource>) -> usize {
        if let Some(order) = self.identities.get(&identity) {
            return *order;
        }
        let order = self.next;
        self.next = self
            .next
            .checked_add(1)
            .expect("pointer fact source identity exhausted");
        self.identities.insert(identity, order);
        self.sources.insert(order, source);
        order
    }

    pub(super) fn remove(&mut self, identity: &usize) -> Option<usize> {
        let order = self.identities.get(identity).copied()?;
        self.identities.remove(identity);
        self.sources.remove(&order);
        Some(order)
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = (&usize, &Arc<dyn PointerFactSource>)> {
        self.sources.iter()
    }
}

pub(super) type PointerFactBucket =
    PersistentMap<String, PersistentMap<(bool, usize), Arc<dyn PointerFactSource>>>;

/// The word operator a 32-bit operator computes: a sign-free `uint32`
/// operator is the `int32` one of the same words; division, remainder and
/// the right shift keep their format, which reads the words. A deliberate
/// equivalence in reasoning, not a construction shortcut: the terms keep
/// their formats (`design/machine-integers.md`, Stage 3).
pub(super) fn word_operator(
    op: crate::kernel::BitvectorBinaryOp,
) -> crate::kernel::BitvectorBinaryOp {
    use crate::kernel::BitvectorBinaryOp as B;
    match op {
        B::Machine(
            MachineIntegerType::UInt32,
            op @ (MachineBinaryOp::Add
            | MachineBinaryOp::Subtract
            | MachineBinaryOp::Multiply
            | MachineBinaryOp::ShiftLeft
            | MachineBinaryOp::BitwiseAnd
            | MachineBinaryOp::BitwiseOr
            | MachineBinaryOp::BitwiseXor),
        ) => B::Machine(MachineIntegerType::Int32, op),
        op => op,
    }
}

/// These tags keep signed division and wider integer operations distinct.
/// Congruence does not establish C/Rust arithmetic definedness.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Int32Binary {
    UnsignedDivide,
    UnsignedRemainder,
    BitwiseXor,
    Other(crate::kernel::BitvectorBinaryOp),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Int32Unary {
    Not,
    Cast(
        crate::kernel::MachineIntegerType,
        crate::kernel::MachineIntegerType,
    ),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum UInt64Binary {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    And,
    Or,
    Xor,
}

pub(super) fn uint64_binary(
    term: &crate::kernel::MachineTerm,
) -> Option<(
    UInt64Binary,
    &crate::kernel::MachineTerm,
    &crate::kernel::MachineTerm,
)> {
    use crate::kernel::MachineTerm as T;
    let (op, a, b) = match term {
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left: a,
            right: b,
        } => (UInt64Binary::Add, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Subtract,
            left: a,
            right: b,
        } => (UInt64Binary::Subtract, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Multiply,
            left: a,
            right: b,
        } => (UInt64Binary::Multiply, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Divide,
            left: a,
            right: b,
        } => (UInt64Binary::Divide, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Remainder,
            left: a,
            right: b,
        } => (UInt64Binary::Remainder, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::BitwiseAnd,
            left: a,
            right: b,
        } => (UInt64Binary::And, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::BitwiseOr,
            left: a,
            right: b,
        } => (UInt64Binary::Or, a, b),
        T::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::BitwiseXor,
            left: a,
            right: b,
        } => (UInt64Binary::Xor, a, b),
        _ => return None,
    };
    Some((op, a, b))
}

/// The same registered four-byte read accepted by `enqueue_int32_load`.
/// A scalar variable without this typed producer metadata stays opaque.
pub(super) fn int32_read(
    term: &crate::kernel::MachineTerm,
) -> Option<(crate::kernel::SharedMemory, Pointer)> {
    let read = crate::kernel::eval::scalar_read_observation(
        crate::kernel::MachineOperandView::Legacy(term),
    )?;
    (read.kind.is_word32() && read.bytes == 4).then_some((read.memory, read.pointer))
}

pub(super) fn uint64_read(
    term: &crate::kernel::MachineTerm,
) -> Option<(crate::kernel::SharedMemory, Pointer)> {
    use crate::kernel::{LoadKind, MachineTerm as T};
    match term {
        T::MemoryLoad(memory, pointer, LoadKind::Bits64) => {
            Some((memory.clone(), pointer.as_ref().clone()))
        }
        T::Variable(variable)
            if crate::kernel::registered_load_kind_for_variable(variable)
                == Some(LoadKind::Bits64)
                && crate::kernel::registered_load_bytes_for_variable(variable) == Some(8) =>
        {
            crate::kernel::registered_load_for_variable(variable)
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum IntegerOperation {
    Observe(crate::kernel::MachineIntegerType),
    Negate,
    Add,
    Subtract,
    Multiply,
    Quotient,
    Remainder,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Apply(u64, u64),
    TypeName(bool, String, usize),
    TypeC(crate::kernel::ProgramType),
    TypeObjectPointer(
        crate::kernel::ProgramType,
        crate::kernel::effective_type::CAccessClass,
    ),
    TypeInteger,
    IntegerAtom(crate::kernel::SharedIntegerTerm),
    IntegerFold(
        Option<crate::kernel::MachineIntegerType>,
        Variable,
        Variable,
        crate::kernel::SharedIntegerTerm,
    ),
    MachineUnary(crate::kernel::BitvectorUnaryOp, crate::kernel::CarrierWidth),
    MachineBinary(
        crate::kernel::BitvectorBinaryOp,
        crate::kernel::CarrierWidth,
    ),
    IntegerToMachine(crate::kernel::MachineIntegerType),
    Machine128(MachineAtom),
    /// An 8- or 16-bit native value's atom, by its bits.
    MachineNarrow(MachineAtom),
    IntegerOperation(IntegerOperation),
    IntegerFunction(crate::kernel::SharedPureApplication, usize),
    PointerFunction(crate::kernel::SharedPureApplication, usize),
    PointerFunctionValue(crate::kernel::SharedPureApplication, usize),
    PointerFunctionIdentity(crate::kernel::SharedPureApplication),
    AlgebraicVariable(crate::kernel::SharedPureApplication, Variable),
    AlgebraicConstructor(crate::kernel::SharedPureApplication, String, usize),
    AlgebraicFunction(crate::kernel::SharedPureApplication, String, usize),
    AlgebraicMemoryRead(crate::kernel::SharedPureApplication, (u32, u32)),
    Function(
        crate::kernel::SharedPureApplication,
        crate::kernel::CarrierWidth,
        usize,
    ),
    ArgumentTag(congruence::ArgumentTag),
    OpaqueArgument(crate::kernel::SharedPureApplication),
    OpaqueMachineCount(MachineAtom),
    Condition(congruence::ConditionKind, u64, u64),
    UInt64(MachineAtom),
    UInt64Binary(UInt64Binary, u64, u64),
    UInt64Address(u64),
    UInt64Read((u32, u32), u64),
    Address(u64, u64),
    AddressShift(u64, i64),
    AddressOffset(u64, u64),
    PointerRead((u32, u32), u64, crate::kernel::LoadKind),
    Footprint(u64, u64),
    Int32(MachineAtom),
    Int32Read((u32, u32), u64),
    /// An 8- or 16-bit read of a state at an address, of its load kind.
    NarrowRead((u32, u32), u64, crate::kernel::LoadKind),
    Int32Add(u64, u64),
    Int32Binary(Int32Binary, u64, u64),
    Int32Unary(Int32Unary, u64),
    Constant(i64),
    Variable(Variable),
    Add(u64, u64),
    Int32Scaled(u64, i64),
    Int64Scaled(u64, i64, bool),
    /// `Bool` values (`TermClasses::bool_node`): a literal, a binder, a
    /// `-> Bool` function's head, the conditional's head, and the read head
    /// of one state's `bool` cells.
    BoolConstant(bool),
    BoolVariable(Variable),
    BoolFunction(crate::kernel::SharedPureApplication, usize),
    BoolIf,
    BoolRead((u32, u32)),
    /// The head of rule C1's cast `b as F` (Stage 5), applied to `b`'s
    /// class.
    BoolCast(crate::kernel::MachineIntegerType),
}

// Operand IDs in an application are structural; in a signature they are
// current class roots. Constructor and width remain part of every signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Application {
    Apply(u64, u64),
    Condition(congruence::ConditionKind, u64, u64),
    UInt64Binary(UInt64Binary, u64, u64),
    UInt64Address(u64),
    UInt64Read((u32, u32), u64),
    Address(u64, u64),
    AddressShift(u64, i64),
    AddressOffset(u64, u64),
    PointerRead((u32, u32), u64, crate::kernel::LoadKind),
    Footprint(u64, u64),
    Add(u64, u64),
    Int32Add(u64, u64),
    Int32Binary(Int32Binary, u64, u64),
    Int32Unary(Int32Unary, u64),
    Int32Scaled(u64, i64),
    Int64Scaled(u64, i64, bool),
    // Defining state, exact storage block ID, offset node/class ID.
    // Only registered four-byte loads in the int32 interpretation enter here.
    Int32Load((u32, u32), u64),
    // A registered 8- or 16-bit read: its defining state, its address
    // class, and its kind. Two reads of one state and kind at equal
    // addresses are one value.
    NarrowLoad((u32, u32), u64, crate::kernel::LoadKind),
}

impl Application {
    fn operands(self) -> impl Iterator<Item = u64> {
        match self {
            Self::Apply(left, right)
            | Self::Condition(_, left, right)
            | Self::Add(left, right)
            | Self::UInt64Binary(_, left, right)
            | Self::Int32Add(left, right)
            | Self::Int32Binary(_, left, right)
            | Self::AddressOffset(left, right)
            | Self::Footprint(left, right) => [Some(left), Some(right)],
            Self::Int32Unary(_, value)
            | Self::Address(_, value)
            | Self::UInt64Address(value)
            | Self::UInt64Read(_, value)
            | Self::PointerRead(_, value, _)
            | Self::AddressShift(value, _)
            | Self::Int32Scaled(value, _)
            | Self::Int64Scaled(value, _, _)
            | Self::Int32Load(_, value)
            | Self::NarrowLoad(_, value, _) => [Some(value), None],
        }
        .into_iter()
        .flatten()
    }

    fn signature(self, classes: &TermClasses) -> Self {
        match self {
            Self::Apply(left, right) => Self::Apply(classes.root(left), classes.root(right)),
            Self::Condition(kind, left, right) => {
                let (mut left, mut right) = (classes.root(left), classes.root(right));
                if matches!(
                    kind,
                    congruence::ConditionKind::PointerEq
                        | congruence::ConditionKind::PointerValueEq
                        | congruence::ConditionKind::OffsetEq
                ) && left > right
                {
                    std::mem::swap(&mut left, &mut right);
                }
                Self::Condition(kind, left, right)
            }
            Self::UInt64Binary(op, left, right) => {
                Self::UInt64Binary(op, classes.root(left), classes.root(right))
            }
            Self::UInt64Address(address) => Self::UInt64Address(classes.root(address)),
            Self::UInt64Read(retained_state, address) => {
                Self::UInt64Read(retained_state, classes.root(address))
            }
            Self::Address(block, offset) => Self::Address(block, classes.root(offset)),
            Self::AddressShift(address, bytes) => Self::AddressShift(classes.root(address), bytes),
            Self::AddressOffset(address, offset) => {
                Self::AddressOffset(classes.root(address), classes.root(offset))
            }
            Self::PointerRead(retained_state, address, kind) => {
                Self::PointerRead(retained_state, classes.root(address), kind)
            }
            Self::Footprint(start, end) => Self::Footprint(classes.root(start), classes.root(end)),
            Self::Add(left, right) => Self::Add(classes.root(left), classes.root(right)),
            Self::Int32Add(left, right) => Self::Int32Add(classes.root(left), classes.root(right)),
            Self::Int32Binary(op, left, right) => {
                Self::Int32Binary(op, classes.root(left), classes.root(right))
            }
            Self::Int32Unary(op, value) => Self::Int32Unary(op, classes.root(value)),
            Self::Int32Scaled(value, width) => Self::Int32Scaled(classes.root(value), width),
            Self::Int64Scaled(value, width, unsigned) => {
                Self::Int64Scaled(classes.root(value), width, unsigned)
            }
            Self::Int32Load(retained_state, address) => {
                Self::Int32Load(retained_state, classes.root(address))
            }
            Self::NarrowLoad(retained_state, address, kind) => {
                Self::NarrowLoad(retained_state, classes.root(address), kind)
            }
        }
    }
}

#[derive(Clone, Copy)]
pub(in crate::kernel) struct TermClassMerge {
    pub(in crate::kernel) moved: u64,
    pub(in crate::kernel) kept: u64,
}
#[derive(Clone)]
struct MergeHistory {
    depth: usize,
    merge: TermClassMerge,
    parent: Option<Arc<MergeHistory>>,
}

// This is disposable derived state, not proof-context storage. Forking starts
// an empty local cache in constant work instead of copying a growing table.
#[derive(Default)]
struct RootLookupCache(std::cell::RefCell<crate::id_hash::U64Map<(usize, u64)>>);

impl Clone for RootLookupCache {
    fn clone(&self) -> Self {
        Self::default()
    }
}

/// One cast of rule C1 in the term classes: its condition node and the
/// classes of the constants 0 and 1 at its format.
#[derive(Clone, Copy, Debug)]
pub(super) struct BoolCastLink {
    condition: u64,
    zero: u64,
    one: u64,
}

/// The identity of a product's shared kernel term: one hash-consed root,
/// whichever handle names it. A legacy spelling is imported, which reads its
/// two operands and attaches nothing to them.
fn byte_product_key(value: &crate::kernel::SharedMachineIntegerTerm) -> Option<u64> {
    match value.operand_view() {
        crate::kernel::MachineOperandView::Shared(root) => Some(root.id()),
        crate::kernel::MachineOperandView::Legacy(term) => {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, term)
                .map(|root| root.id())
        }
    }
}

/// The index and stride of an `int32` product by a constant from two to
/// `INT_MAX`, in either operand order: the products whose byte offset names
/// an element (`byte_product_offsets`). A constant-size match on the root.
pub(super) fn byte_product_operands(
    value: &crate::kernel::SharedMachineIntegerTerm,
) -> Option<(crate::kernel::SharedMachineIntegerTerm, i64)> {
    let (MachineIntegerType::Int32, MachineBinaryOp::Multiply, [left, right]) =
        value.operand_view().binary()?
    else {
        return None;
    };
    let (index, stride) = match (left.word32_constant(), right.word32_constant()) {
        (None, Some(stride)) => (left, stride),
        (Some(stride), None) => (right, stride),
        _ => return None,
    };
    (2..=i32::MAX as u32)
        .contains(&stride)
        .then(|| (index.retain(MachineIntegerType::Int32), i64::from(stride)))
}

#[derive(Clone, Default)]
pub(super) struct TermClasses {
    // Derived residue operations use shallow graph IDs. Repeated cancellation
    // of shared prefixes reuses this cache; a restriction starts a new graph.
    modular_word_operations: PersistentMap<(MachineBinaryOp, u64, u64), u64>,
    // Exact shared operands retain their handles. Class IDs are stable even
    // after union; callers use root(), and persistent clones isolate branches.
    shared_machine_classes:
        PersistentMap<(u64, crate::kernel::CarrierWidth), (crate::kernel::KernelTerm, u64)>,
    scalar_witnesses: constants::ScalarWitnesses,
    scalar_conflicts: PersistentSet<u64>,
    /// Source propositions follow address and condition classes. Only the moved class is
    /// visited on union; queries select one key and never enumerate aliases.
    pointer_facts: PersistentMap<u64, PersistentMap<PointerFactKey, PointerFactBucket>>,
    // Retain the exact schema allocation used by each key, even when the
    // interned token uses an independently allocated equal schema. Keys are
    // allocation identity and a shallow nominal node, never a model tree.
    algebraic_types: PersistentMap<
        (usize, u64),
        (
            Arc<[crate::kernel::AlgebraicVariantType]>,
            crate::kernel::SharedPureApplication,
        ),
    >,
    // One exact constructor witness per typed model class. Only a selected
    // equality's root operands are retained, once, so nested models are not
    // copied at every subtree. Union carries this witness in constant work.
    algebraic_constructors: PersistentMap<u64, Arc<crate::kernel::AlgebraicTerm>>,
    // Constructor heads by variant and arity, and one interned constructor
    // application per class. Union compares the two classes' applications:
    // one variant joins their fields (injectivity), two variants make the
    // context empty. Each union reads only its two witnesses.
    constructor_heads: PersistentMap<u64, (String, usize)>,
    constructor_applications: PersistentMap<u64, u64>,
    argument_tags: PersistentSet<u64>,
    condition_kinds: PersistentSet<(congruence::ConditionKind, bool)>,
    // Truth is an annotation of a condition class, not a union between all
    // true facts. Unrelated order facts must not create value equivalences.
    condition_truth: PersistentMap<u64, u8>,
    // The truth of each `Bool` binder's admitted facts, kept whether or not a
    // `Bool` value has interned the binder yet, so a binder interned later
    // starts with it and the answer does not depend on the order facts were
    // admitted in. One entry per binder fact; nothing reads it but interning.
    bool_binder_truth: PersistentMap<crate::kernel::Variable, u8>,
    // Rule C1's link (Stage 5): each class holding a cast `b as F` names
    // `b`'s condition node and the classes of the constants 0 and 1 at `F`;
    // each condition class names its casts. A truth reaching the condition
    // merges the cast with its constant, and a constant reaching the cast
    // gives the condition its truth. Two links per cast, nothing scanned.
    bool_cast_links: PersistentMap<u64, BoolCastLink>,
    condition_casts: PersistentMap<u64, PersistentSet<u64>>,
    // Unions a truth asked for while a merge was running, made once it ends.
    pending_cast_unions: Vec<(u64, u64)>,
    closing: bool,
    // The cross-format relations R0, R-dist and R-comp (`machine_relations`):
    // the head each machine operator or conversion node names; per class,
    // its sign-free operators by format and operator, the conversions
    // applied to it by kind, and the conversions it holds by kind; and the
    // pairs already fired. Each per-class map holds one entry per kind, so a
    // union moves and fires a bounded number of entries.
    machine_heads: PersistentMap<u64, machine_relations::MachineHead>,
    class_operators: PersistentMap<
        u64,
        PersistentMap<
            (
                machine_relations::OperatorFormat,
                machine_relations::SignFree,
            ),
            u64,
        >,
    >,
    casts_of_class: PersistentMap<u64, PersistentMap<machine_relations::CastKey, u64>>,
    class_casts: PersistentMap<u64, PersistentMap<machine_relations::CastKey, u64>>,
    fired_machine_relations: PersistentSet<(u64, u64)>,
    pending_machine_relations: Vec<(machine_relations::Relation, u64, u64)>,
    relating_machine_terms: bool,
    // Constant signed int32 bounds belong to a value class, not a spelling.
    // A class union intersects two intervals in constant local work.
    signed_int32_intervals: PersistentMap<u64, (i64, i64)>,
    origin: Arc<()>,
    // Completeness metadata for affine interval consumers, not equality facts.
    // Propagates once per affected class/application through indexed uses.
    non_affine_classes: PersistentSet<u64>,
    affine_applications: PersistentMap<u64, PersistentSet<u64>>,
    affine_uses: PersistentMap<u64, PersistentSet<u64>>,
    // Only applications with literal-folding rules need revisiting when an
    // existing class first learns a constant. Boolean observations do not.
    constant_uses: PersistentMap<u64, PersistentSet<u64>>,
    non_affine_address_blocks: PersistentSet<PointerBlock>,
    address_blocks: PersistentMap<u64, PointerBlock>,
    history: Option<Arc<MergeHistory>>,
    // Node IDs are local to a persistent registration prefix. The last marker
    // detects divergent query registrations without scanning that prefix.
    markers: PersistentMap<u64, Arc<()>>,
    address_uses: PersistentMap<PointerBlock, PersistentMap<u64, Arc<PointerOffsetTerm>>>,
    // The pointer block classes, mirrored from the graph's block union-find
    // as `relabel` reports each union: every member's base relative to its
    // class root, as in `EqualityGraphState::members`. A read looks for a
    // stored cell at its address spelled in each member.
    block_roots: PersistentMap<PointerBlock, (PointerBlock, AffineOffset)>,
    block_members: PersistentMap<PointerBlock, PersistentMap<PointerBlock, AffineOffset>>,
    address_nodes: PersistentSet<u64>,
    // A displacement definition is permanent for one raw address spelling.
    // Repeated queries reuse it without re-registering its base or closure.
    registered_address_shifts: PersistentSet<(u64, u64)>,
    // The displacement of each registered shifted address whose numeric sum
    // no read has needed yet: `read_address` defines it on first use, so an
    // address that is never read (a resource's) adds no numeric nodes.
    numeric_shifts: PersistentMap<u64, (u64, i64)>,
    // One explicit pointer spelling per numeric-address class. This is byte
    // geometry only: numeric equality must never merge pointer provenance.
    numeric_addresses: PersistentMap<u64, Pointer>,
    // The address node of each registered (block, raw offset) spelling. Its
    // affine definition is permanent, so a repeated registration (every
    // pointer equality query registers both sides) returns it after interning
    // the offset, without renormalizing or reclosing. Keys are shallow IDs.
    registered_addresses: PersistentMap<(u64, u64), u64>,
    // One offset witness per exact block in each address class. When address
    // classes merge, a shared block proves its two offsets equal. Small-side
    // class union visits only moved witnesses, never ambient pointer facts.
    offsets_by_address_block: PersistentMap<u64, PersistentMap<u64, u64>>,
    // Addresses that explicitly use each offset class, indexed by exact block.
    // An offset predicate query visits only its operands' registered addresses.
    addresses_by_offset: PersistentMap<u64, PersistentMap<u64, u64>>,
    // Retained concrete address evidence follows typed class merges. This
    // disambiguates parameters sharing the external address-space block.
    storage_addresses: PersistentMap<u64, Option<Pointer>>,
    // One producer-registered additive spelling per index width and address
    // class. A narrow spelling must not discard the wide coordinate whose
    // bounds justify a borrow. Queries never enumerate class members.
    additive_addresses: PersistentMap<u64, (Option<Arc<Pointer>>, Option<Arc<Pointer>>)>,
    // The offset views of same-block pointer equations. These checked
    // producer spellings carry no block identity and are applied only in the
    // query's own block.
    additive_offsets: PersistentMap<
        u64,
        (
            Option<Arc<PointerOffsetTerm>>,
            Option<Arc<PointerOffsetTerm>>,
        ),
    >,
    alignment_witnesses: PersistentMap<u64, (u64, Pointer)>,
    // Byte products `x * K` whose `int32` multiplication the context knows
    // does not wrap, keyed by the product's shared kernel term: the element
    // index `x` and stride `K` their byte offset is one exact offset with.
    defined_byte_products: PersistentMap<u64, (crate::kernel::SharedMachineIntegerTerm, i64)>,
    // The registered byte-offset node `Int32Scaled { x * K, 1 }` of each such
    // product spelling, keyed the same way, so a fact admitted after the node
    // finds it without a scan.
    byte_product_nodes: PersistentMap<u64, u64>,
    // One zero-offset pointer read or pure-call value per class. Congruence emits only
    // newly identified pairs for the legacy affine/index projection.
    pointer_value_witnesses: PersistentMap<u64, PointerBlock>,
    pointer_values: PersistentMap<u64, crate::kernel::PointerValue>,
    extent_values: PersistentMap<u64, crate::kernel::PointerValue>,
    read_domains: crate::kernel::pointer_designations::ValueClasses<Pointer>,
    read_designation_nodes: PersistentMap<Pointer, u64>,
    read_extent_nodes: PersistentMap<Pointer, u64>,
    pointer_value_merges: imbl::Vector<(PointerBlock, PointerBlock)>,
    nodes: PersistentMap<Node, u64>,
    load_blocks: PersistentMap<PointerBlock, u64>,
    // The load nodes, four-byte and narrow, already queued for registration.
    registered_int32_loads: PersistentSet<u64>,
    // An observed word may name its own read. Register each exact source
    // once, before interning its stored value, to close that cycle. Keep
    // distinct states, origins and address spellings as separate sources.
    registered_uint64_cell_reads: PersistentSet<WideReadSource>,
    // Registration dependencies are drained before any public answer. Keeping
    // this worklist iterative handles loads used as indices of further loads.
    pending_loads: Vec<(
        u64,
        crate::kernel::SharedMemory,
        crate::kernel::Pointer,
        Option<crate::kernel::SharedMemory>,
    )>,
    // Signed byte reads still to be related to their unsigned read (R-mem).
    pending_signed_byte_reads: Vec<(u64, crate::kernel::SharedMemory, crate::kernel::Pointer)>,
    // `uint32` reads still to be related to their cell's `int32` read by σ
    // (R-mem at 32 bits).
    pending_unsigned_word_reads: Vec<(u64, crate::kernel::SharedMemory, crate::kernel::Pointer)>,
    // 8- and 16-bit reads whose load application is still to be registered
    // (`enqueue_narrow_load`).
    pending_narrow_loads: Vec<(
        u64,
        crate::kernel::SharedMemory,
        crate::kernel::Pointer,
        crate::kernel::LoadKind,
        Option<crate::kernel::SharedMemory>,
    )>,
    // Reads whose stored cell under another spelling of their address is
    // still to be looked up; drained with the other registration work.
    pending_cell_reads: Vec<PendingCellRead>,
    // The endpoints of recorded true 64-bit equality facts, by class. A
    // consumer that needs a recorded fact about a word (a pointer recovered
    // from `word == address(p)`) finds the facts of every word equal to it.
    // A merge moves the smaller set.
    wide_equation_endpoints: PersistentMap<u64, PersistentSet<crate::kernel::MachineTerm>>,
    // Reads that found no stored cell, by the root of their block class. A
    // later union of that class looks again, so the answer does not depend
    // on whether the read or the pointer equality came first. A read leaves
    // once found.
    unresolved_cell_reads: PersistentMap<PointerBlock, PersistentMap<u64, Arc<PendingCellRead>>>,
    pending_pointer_calls: Vec<(u64, crate::kernel::SharedPureApplication)>,
    pending_pointer_identities: Vec<(u64, crate::kernel::SharedPureApplication)>,
    registering_dependencies: bool,
    // Weight counts class members plus registered parent uses. Moving the
    // lighter side bounds both root depth and reindexing, including a class
    // with many application parents repeatedly joined to fresh singleton terms.
    parents: PersistentMap<u64, u64>,
    // Cache representative lookups under the current merge epoch. A new union
    // invalidates entries lazily, without a scan. Keys are shallow node IDs,
    // with at most one entry per node; semantic graph roots remain persistent.
    root_cache: RootLookupCache,
    weights: PersistentMap<u64, usize>,
    int32_constants: PersistentMap<u64, i32>,
    uint64_constants: PersistentMap<u64, u64>,
    /// The bits of the constant an 8- or 16-bit class holds. A class has
    /// one width, so its bits name its value at either signedness.
    pub(super) narrow_constants: PersistentMap<u64, u32>,
    // Monotonic within one checked context; forks copy it and a restriction
    // starts a new graph. Queries read one flag.
    scalar_constant_conflict: bool,
    applications: PersistentMap<u64, Application>,
    uses: PersistentMap<u64, PersistentSet<u64>>,
    signatures: PersistentMap<Application, u64>,
    application_signatures: PersistentMap<u64, Application>,
}

impl TermClasses {
    pub(super) fn pointer_facts(&self, address: u64, key: &PointerFactKey) -> PointerFactBucket {
        crate::instrumentation::record_deterministic_work(1);
        self.pointer_facts
            .get(&self.root(address))
            .and_then(|facts| facts.get(key))
            .cloned()
            .unwrap_or_default()
    }

    pub(super) fn adjust_pointer_fact(
        &mut self,
        address: u64,
        key: PointerFactKey,
        identity: (bool, usize),
        source: &Arc<dyn PointerFactSource>,
        insert: bool,
    ) {
        crate::instrumentation::record_deterministic_work(1);
        let root = self.root(address);
        let mut keys = self.pointer_facts.get(&root).cloned().unwrap_or_default();
        let mut groups = keys.get(&key).cloned().unwrap_or_default();
        let group = match (&key, source.proposition()) {
            (
                PointerFactKey::FunctionContracts,
                crate::kernel::Proposition::Predicate { name, arguments },
            ) => function_contract_group(
                crate::kernel::FunctionContract::surface_name_from_predicate(name)
                    .expect("contract predicate"),
                &arguments[2..],
            ),
            _ => String::new(),
        };
        let bucket = groups.get(&group).cloned().unwrap_or_default();
        // Admission ordinals stay shallow even for facts with large C states.
        // They preserve deterministic search order across allocation layouts.
        if insert && !bucket.contains_key(&identity) {
            // Payloads participate in union weighting, so a large class of
            // witnesses cannot be moved repeatedly by fresh singleton terms.
            self.weights.insert(root, self.weight(root) + 1);
        }
        let bucket = if insert {
            bucket.with_inserted(identity, source.clone())
        } else {
            bucket.without_key(&identity)
        };
        if bucket.is_empty() {
            groups.remove(&group);
        } else {
            groups.insert(group, bucket);
        }
        if groups.is_empty() {
            keys.remove(&key);
        } else {
            keys.insert(key, groups);
        }
        if keys.is_empty() {
            self.pointer_facts.remove(&root);
        } else {
            self.pointer_facts.insert(root, keys);
        }
    }

    fn merge_pointer_facts(&mut self, moved: u64, kept: u64) {
        let Some(moved_facts) = self.pointer_facts.get(&moved).cloned() else {
            return;
        };
        let mut kept_facts = self.pointer_facts.get(&kept).cloned().unwrap_or_default();
        for (key, groups) in moved_facts.iter() {
            let mut kept_groups = kept_facts.get(key).cloned().unwrap_or_default();
            for (group, sources) in groups.iter() {
                let mut bucket = kept_groups.get(group).cloned().unwrap_or_default();
                for (identity, source) in sources.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    #[cfg(test)]
                    POINTER_FACT_MERGE_VISITS.with(|visits| visits.set(visits.get() + 1));
                    bucket.insert(*identity, source.clone());
                }
                kept_groups.insert(group.clone(), bucket);
            }
            kept_facts.insert(key.clone(), kept_groups);
        }
        self.pointer_facts.remove(&moved);
        self.pointer_facts.insert(kept, kept_facts);
    }
}

impl TermClasses {
    pub(super) fn merges_since(&self, ancestor: &Self) -> Option<Vec<TermClassMerge>> {
        if !Arc::ptr_eq(&self.origin, &ancestor.origin) {
            return None;
        }
        if let Some(last) = ancestor.nodes.len().checked_sub(1) {
            let marker = self.markers.get(&(last as u64))?;
            if !Arc::ptr_eq(marker, ancestor.markers.get(&(last as u64))?) {
                return None;
            }
        }
        let mut cursor = self.history.clone();
        let previous = &ancestor.history;
        let previous_depth = previous.as_ref().map_or(0, |node| node.depth);
        let mut merges = Vec::new();
        while !match (&cursor, previous) {
            (None, None) => true,
            (Some(current), Some(previous)) => Arc::ptr_eq(current, previous),
            _ => false,
        } {
            let node = cursor.as_ref()?;
            if node.depth <= previous_depth {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            merges.push(node.merge);
            cursor = node.parent.clone();
        }
        merges.reverse();
        Some(merges)
    }

    pub(super) fn address(
        &mut self,
        block: PointerBlock,
        offset: PointerOffsetTerm,
    ) -> (u64, bool) {
        let (address, new, raw_offset) = self.address_without_shift(block.clone(), offset.clone());
        // Preserve the byte displacement as an operation on the complete
        // address. Flattening it into a block's affine coordinates can hide
        // the aliased base subexpression after a previous block merge.
        // One selected prefix suffices; do not recursively publish prefixes
        // or enumerate other addresses in the class.
        let shift = match &offset {
            PointerOffsetTerm::Add(base, displacement) => displacement
                .as_const()
                .filter(|bytes| *bytes != 0)
                .map(|bytes| (base.as_ref().clone(), bytes)),
            PointerOffsetTerm::Constant(bytes) if *bytes != 0 => {
                Some((PointerOffsetTerm::Constant(0), *bytes))
            }
            _ => None,
        };
        if let Some((base, bytes)) = shift
            && !self
                .registered_address_shifts
                .contains(&(address, raw_offset))
        {
            let base = self.address_without_shift(block.clone(), base).0;
            let shifted = self.intern_node(Node::AddressShift(base, bytes));
            self.close_with_affine_definition(vec![(address, shifted)], true);
            if !self.numeric_shifts.contains_key(&address) {
                self.numeric_shifts = self.numeric_shifts.with_inserted(address, (base, bytes));
            }
            self.registered_address_shifts = self
                .registered_address_shifts
                .with_value((address, raw_offset));
        }
        if let PointerOffsetTerm::Add(base, displacement) = &offset
            && displacement.as_const().is_none()
            && !self
                .registered_address_shifts
                .contains(&(address, raw_offset))
            && let Some(block_id) = self.load_blocks.get(&block).copied()
        {
            // Only a retained typed-read base needs this extra application:
            // ordinary affine coordinates already share offset congruence.
            // Query the selected prefix without creating unrelated addresses.
            let base_offset = self.intern(base);
            if let Some(base) = self
                .registered_addresses
                .get(&(block_id, base_offset))
                .copied()
                && self.pointer_value_witnesses.contains_key(&self.root(base))
            {
                let displacement = self.intern(displacement);
                let shifted = self.intern_node(Node::AddressOffset(base, displacement));
                self.close_with_affine_definition(vec![(address, shifted)], true);
                self.registered_address_shifts = self
                    .registered_address_shifts
                    .with_value((address, raw_offset));
            }
        }
        (address, new)
    }

    /// A typed pointer read is an application of the complete address, not
    /// its affine block representative. Existing parent uses propagate late
    /// address merges without enumerating aliases or unrelated reads.
    pub(super) fn pointer_read(
        &mut self,
        retained_state: (u32, u32),
        address: u64,
        kind: crate::kernel::LoadKind,
        value: u64,
        block: PointerBlock,
        cell: Option<(crate::kernel::SharedMemory, Pointer)>,
    ) {
        let address = self.read_address(address);
        let read = self.intern_node(Node::PointerRead(retained_state, address, kind));
        self.close_with_affine_definition(vec![(value, read)], true);
        self.retain_pointer_value_witness(self.root(value), block);
        if let Some((memory, pointer)) = cell {
            self.pending_cell_reads.push(PendingCellRead {
                read: value,
                memory,
                origin: None,
                pointer,
                kind: CellRead::FunctionPointer,
                only: None,
            });
            self.register_pending_loads();
        }
    }

    /// The operand of a read: the numeric address of `address`, not the
    /// pointer. Memory is addressed, so two reads of one state at equal
    /// addresses read the same bytes even when the pointers are not equal
    /// (a C pointer comparison states only an address equality). Equal
    /// pointers have equal addresses, so pointer congruence still reaches
    /// every read through this application.
    pub(super) fn read_address(&mut self, address: u64) -> u64 {
        let numeric = self.intern_node(Node::UInt64Address(address));
        // The numeric address of a displaced pointer is the base's plus the
        // displacement (modulo 2^64), so an address equality of two bases
        // relates the reads of one field of each. Defined once, on first read.
        if let Some((base, bytes)) = self.numeric_shifts.get(&address).copied() {
            self.numeric_shifts = self.numeric_shifts.without_key(&address);
            let numeric_base = self.read_address(base);
            let displacement = self.intern_node(Node::UInt64(MachineAtom::uint64(
                crate::kernel::MachineTerm::uint64_constant(bytes as u64),
            )));
            let sum = self.intern_node(Node::UInt64Binary(
                UInt64Binary::Add,
                numeric_base,
                displacement,
            ));
            self.close_with_affine_definition(vec![(numeric, sum)], true);
        }
        numeric
    }

    pub(super) fn numeric_address(&mut self, pointer: &Pointer) -> u64 {
        let address = self
            .address(pointer.block.clone(), pointer.offset.clone())
            .0;
        let numeric = self.read_address(address);
        self.retain_numeric_address(self.root(numeric), pointer.clone());
        numeric
    }

    fn retain_numeric_address(&mut self, root: u64, pointer: Pointer) {
        let displaced = |p: &Pointer| match &p.offset {
            PointerOffsetTerm::Add(_, offset) => offset.as_const().is_some_and(|bytes| bytes != 0),
            PointerOffsetTerm::Constant(bytes) => *bytes != 0,
            _ => false,
        };
        if self
            .numeric_addresses
            .get(&root)
            .is_none_or(|prior| (displaced(&pointer), &pointer) > (displaced(prior), prior))
        {
            self.numeric_addresses.insert(root, pointer);
        }
    }

    pub(super) fn numeric_address_spelling(&mut self, pointer: &Pointer) -> Pointer {
        let numeric = self.numeric_address(pointer);
        self.numeric_addresses
            .get(&self.root(numeric))
            .expect("registered address")
            .clone()
    }

    fn retain_pointer_value_witness(&mut self, root: u64, block: PointerBlock) {
        if let Some(other) = self.pointer_value_witnesses.get(&root) {
            if other != &block {
                self.pointer_value_merges.push_back((other.clone(), block));
            }
        } else {
            self.pointer_value_witnesses.insert(root, block);
        }
    }

    pub(super) fn take_pointer_value_merges(
        &mut self,
    ) -> imbl::Vector<(PointerBlock, PointerBlock)> {
        std::mem::take(&mut self.pointer_value_merges)
    }

    #[cfg(test)]
    pub(super) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// A selected bound can name an address without constructing a pointer
    /// spelling. This query registers definitions only; it supplies no storage
    /// witness. Each query joins the current block representative, while owned
    /// native addresses retain the existing late-merge registration machinery.
    pub(super) fn index_address_query(
        &mut self,
        base: &Pointer,
        index: &crate::kernel::KernelTerm,
        width: u32,
        representative: PointerBlock,
        delta: &AffineOffset,
    ) -> u64 {
        use crate::kernel::MachineOperandView as V;
        let base_address = self.address(base.block.clone(), base.offset.clone()).0;
        let base_offset = self.intern(&base.offset);
        let index_class = self.shared_int32_class(index);
        let displacement = self.intern_node(Node::Int32Scaled(index_class, i64::from(width)));
        let zero_base = base.offset == PointerOffsetTerm::Constant(0);
        let raw = if zero_base {
            displacement
        } else {
            self.intern_node(Node::Add(base_offset, displacement))
        };
        let affine = AffineOffset::of(&base.offset).and_then(|mut affine| {
            affine.add_atom(
                OffsetAtom::Int32(MachineAtom::from_operand(
                    MachineIntegerType::Int32,
                    V::Shared(index),
                )),
                i128::from(width),
            )?;
            Some(affine)
        });
        let normalized = affine
            .as_ref()
            .and_then(|a| self.intern_affine_offset(a))
            .unwrap_or(raw);
        self.register_pending_loads();
        self.close_with_affine_definition(vec![(raw, normalized)], true);
        let block = *self
            .load_blocks
            .get(&base.block)
            .expect("registered base block");
        let address = self.intern_node(Node::Address(block, normalized));
        if let Some(bytes) = self
            .scalar_leaf_of_class(index_class)
            .and_then(|value| value.as_const())
            .map(|value| i64::from(value as i32) * i64::from(width))
            && bytes != 0
        {
            let shifted = self.intern_node(Node::AddressShift(base_address, bytes));
            self.close_with_affine_definition(vec![(address, shifted)], true);
        }

        if !zero_base
            && self
                .pointer_value_witnesses
                .contains_key(&self.root(base_address))
        {
            let shifted = self.intern_node(Node::AddressOffset(base_address, displacement));
            self.close_with_affine_definition(vec![(address, shifted)], true);
        }
        if representative != base.block
            && let Some(delta_node) = self.intern_affine_offset(delta)
        {
            self.address(representative.clone(), PointerOffsetTerm::Constant(0));
            let translated = self.intern_node(Node::Add(raw, delta_node));
            let normalized = affine
                .as_ref()
                .and_then(|a| a.checked_add(delta))
                .and_then(|a| self.intern_affine_offset(&a))
                .unwrap_or(translated);
            self.close_with_affine_definition(vec![(translated, normalized)], true);
            let block = *self
                .load_blocks
                .get(&representative)
                .expect("registered representative");
            let canonical = self.intern_node(Node::Address(block, normalized));
            self.add_address_equality(address, canonical);
        }
        self.root(address)
    }

    fn address_without_shift(
        &mut self,
        block: PointerBlock,
        offset: PointerOffsetTerm,
    ) -> (u64, bool, u64) {
        // Affine normalization is already trusted by pointer equality. Keep
        // the original syntax connected to its definitional normal form so
        // whole-offset premises and affine addresses share these applications.
        let raw = self.intern(&offset);
        if let Some(block_id) = self.load_blocks.get(&block)
            && let Some(id) = self.registered_addresses.get(&(*block_id, raw)).copied()
        {
            self.register_pending_loads();
            return (id, false, raw);
        }
        let operand = AffineOffset::of(&offset)
            .and_then(|value| self.intern_affine_offset(&value))
            .unwrap_or(raw);
        self.register_pending_loads();
        self.close_with_affine_definition(vec![(raw, operand)], true);
        let next_block = self.load_blocks.len() as u64;
        let new_block = !self.load_blocks.contains_key(&block);
        let block_id = match self.load_blocks.get(&block) {
            Some(id) => *id,
            None => {
                self.address_blocks.insert(next_block, block.clone());
                self.load_blocks.insert(block.clone(), next_block);
                next_block
            }
        };
        let node = Node::Address(block_id, operand);
        let new = !self.nodes.contains_key(&node);
        let id = self.intern_node(node);
        self.registered_addresses.insert((block_id, raw), id);
        let mut uses = self.address_uses.get(&block).cloned().unwrap_or_default();
        if !uses.contains_key(&id) {
            uses.insert(id, Arc::new(offset));
            self.address_uses.insert(block.clone(), uses);
        }
        if new_block && let PointerBlock::PureFunctionApplication(application) = block {
            // Give the call its zero-offset address once. Arguments may enqueue
            // nested calls; the shared dependency worklist drains them iteratively.
            let zero = if operand == self.intern(&PointerOffsetTerm::Constant(0)) {
                id
            } else {
                self.address_without_shift(
                    PointerBlock::PureFunctionApplication(application.clone()),
                    PointerOffsetTerm::Constant(0),
                )
                .0
            };
            self.pending_pointer_calls.push((zero, application));
            self.register_pending_loads();
        }
        (id, new, raw)
    }

    /// Only original concrete address inputs carry storage evidence. Affine
    /// projections into a representative's coordinates must never mint it.
    pub(super) fn retain_storage_address(&mut self, id: u64, storage: &Pointer) {
        let root = self.root(id);
        let retained = match self.storage_addresses.get(&root) {
            None => Some(storage.clone()),
            Some(Some(previous)) if previous.block == storage.block => Some(previous.clone()),
            _ => None,
        };
        self.storage_addresses.insert(root, retained);
    }

    pub(super) fn storage_address(&self, id: u64) -> Option<Pointer> {
        self.storage_addresses
            .get(&self.root(id))
            .cloned()
            .flatten()
    }

    fn merge_address_offsets(&mut self, moved: u64, kept: u64, pending: &mut PendingUnions) {
        let Some(moved_offsets) = self.offsets_by_address_block.get(&moved).cloned() else {
            return;
        };
        let mut kept_offsets = self
            .offsets_by_address_block
            .get(&kept)
            .cloned()
            .unwrap_or_default();
        for (block, offset) in moved_offsets.iter() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(previous) = kept_offsets.get(block) {
                pending.push((*previous, *offset));
            } else {
                kept_offsets.insert(*block, *offset);
            }
        }
        self.offsets_by_address_block.remove(&moved);
        self.offsets_by_address_block.insert(kept, kept_offsets);
    }

    fn merge_storage_addresses(&mut self, moved: u64, kept: u64) {
        let merged = match (
            self.storage_addresses.get(&moved).cloned(),
            self.storage_addresses.get(&kept).cloned(),
        ) {
            (None, right) => right,
            (left, None) => left,
            (Some(Some(left)), Some(Some(right))) if left.block == right.block => Some(Some(right)),
            _ => Some(None),
        };
        if let Some(merged) = merged {
            self.storage_addresses.insert(kept, merged);
        }
        self.storage_addresses.remove(&moved);
    }

    pub(super) fn retain_additive_address(&mut self, id: u64, pointer: &Pointer) {
        if !matches!(pointer.offset, PointerOffsetTerm::Add(_, _)) {
            return;
        }
        let wide = Self::additive_offset_is_wide(&pointer.offset);
        let root = self.root(id);
        let mut spellings = self
            .additive_addresses
            .get(&root)
            .cloned()
            .unwrap_or_default();
        let selected = if wide {
            &mut spellings.1
        } else {
            &mut spellings.0
        };
        if selected
            .as_ref()
            .is_none_or(|prior| wide && Self::prefer_wide_address(pointer, prior))
        {
            *selected = Some(Arc::new(pointer.clone()));
            self.additive_addresses.insert(root, spellings);
        }
    }

    // A wide supplier checks the final displacement in its uint64 coordinate.
    // Prefer that producer over a wide prefix followed by a signed displacement;
    // both denote the same checked address, but only the former retains the
    // native index on which the caller stated its window bounds.
    fn prefer_wide_offset(new: &PointerOffsetTerm, prior: &PointerOffsetTerm) -> bool {
        let native = |offset: &PointerOffsetTerm| {
            matches!(offset,
            PointerOffsetTerm::Add(_, right) if matches!(right.as_ref(),
                PointerOffsetTerm::Int64Scaled { unsigned: true, .. }))
        };
        native(new) && !native(prior)
    }

    // An external-buffer spelling retains the complete caller coordinate.
    // A captured batch cursor's symbolic base can hide a prefix displacement;
    // choose the checked external producer on a tie without searching aliases.
    fn prefer_wide_address(new: &Pointer, prior: &Pointer) -> bool {
        Self::prefer_wide_offset(&new.offset, &prior.offset)
            || !Self::prefer_wide_offset(&prior.offset, &new.offset)
                && matches!(new.block, PointerBlock::ExternalArgument)
                && matches!(prior.block, PointerBlock::Symbolic(_))
    }

    fn additive_offset_is_wide(offset: &PointerOffsetTerm) -> bool {
        let mut pending = vec![offset];
        let mut wide = false;
        while let Some(offset) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                PointerOffsetTerm::Int64Scaled { .. } => {
                    wide = true;
                    break;
                }
                _ => {}
            }
        }
        wide
    }

    fn retain_additive_offset(&mut self, id: u64, offset: &PointerOffsetTerm) {
        if !matches!(offset, PointerOffsetTerm::Add(_, _)) {
            return;
        }
        let wide = Self::additive_offset_is_wide(offset);
        let root = self.root(id);
        let mut spellings = self
            .additive_offsets
            .get(&root)
            .cloned()
            .unwrap_or_default();
        let selected = if wide {
            &mut spellings.1
        } else {
            &mut spellings.0
        };
        if selected
            .as_ref()
            .is_none_or(|prior| wide && Self::prefer_wide_offset(offset, prior))
        {
            *selected = Some(Arc::new(offset.clone()));
            self.additive_offsets.insert(root, spellings);
        }
    }

    pub(super) fn additive_offset(
        &mut self,
        offset: &PointerOffsetTerm,
        wide: bool,
    ) -> Option<PointerOffsetTerm> {
        let id = self.intern(offset);
        let (narrow, wide_spelling) = self.additive_offsets.get(&self.root(id))?;
        (if wide {
            wide_spelling.as_ref()
        } else {
            narrow.as_ref().or(wide_spelling.as_ref())
        })
        .map(|offset| (**offset).clone())
    }

    fn merge_additive_offsets(&mut self, moved: u64, kept: u64) {
        if let Some((narrow, wide)) = self.additive_offsets.get(&moved).cloned() {
            let mut spellings = self
                .additive_offsets
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            if spellings.0.is_none() {
                spellings.0 = narrow;
            }
            if let Some(wide) = wide
                && spellings
                    .1
                    .as_ref()
                    .is_none_or(|prior| Self::prefer_wide_offset(&wide, prior))
            {
                spellings.1 = Some(wide);
            }
            self.additive_offsets.insert(kept, spellings);
        }
        self.additive_offsets.remove(&moved);
    }

    pub(super) fn additive_address(&self, id: u64) -> Option<Pointer> {
        self.additive_addresses
            .get(&self.root(id))
            .and_then(|(narrow, wide)| narrow.as_ref().or(wide.as_ref()))
            .map(|pointer| (**pointer).clone())
    }

    pub(super) fn wide_additive_address(&self, id: u64) -> Option<Pointer> {
        self.additive_addresses
            .get(&self.root(id))
            .and_then(|(_, wide)| wide.as_ref())
            .map(|pointer| (**pointer).clone())
    }

    fn merge_additive_addresses(&mut self, moved: u64, kept: u64) {
        if let Some((narrow, wide)) = self.additive_addresses.get(&moved).cloned() {
            let mut spellings = self
                .additive_addresses
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            if spellings.0.is_none() {
                spellings.0 = narrow;
            }
            if let Some(wide) = wide
                && spellings
                    .1
                    .as_ref()
                    .is_none_or(|prior| Self::prefer_wide_address(&wide, prior))
            {
                spellings.1 = Some(wide);
            }
            self.additive_addresses.insert(kept, spellings);
        }
        self.additive_addresses.remove(&moved);
    }

    pub(super) fn retain_alignment(&mut self, id: u64, alignment: u64, pointer: &Pointer) {
        let root = self.root(id);
        if self
            .alignment_witnesses
            .get(&root)
            .is_none_or(|(old, _)| *old < alignment)
        {
            self.alignment_witnesses
                .insert(root, (alignment, pointer.clone()));
        }
    }

    pub(super) fn alignment_witness(&self, id: u64) -> Option<(u64, Pointer)> {
        self.alignment_witnesses.get(&self.root(id)).cloned()
    }

    fn merge_alignment_witnesses(&mut self, moved: u64, kept: u64) {
        if let Some((alignment, pointer)) = self.alignment_witnesses.get(&moved).cloned() {
            self.retain_alignment(kept, alignment, &pointer);
        }
        self.alignment_witnesses.remove(&moved);
    }

    pub(super) fn footprint(&mut self, start: u64, end: u64) -> u64 {
        let id = self.intern_node(Node::Footprint(start, end));
        self.root(id)
    }

    pub(super) fn shift_addresses(
        &mut self,
        moved: &PointerBlock,
        kept: &PointerBlock,
        delta: &AffineOffset,
    ) {
        if !self.affine_addresses_complete(moved) {
            self.non_affine_address_blocks =
                self.non_affine_address_blocks.with_value(kept.clone());
        }
        let Some(uses) = self.address_uses.get(moved).cloned() else {
            return;
        };
        let Some(delta) = delta.to_offset_term() else {
            // The affine block relation remains valid, but its displacement
            // has no bounded spelling in this term fragment. Do not let a
            // consumer turn incomplete address registrations into a denial.
            return;
        };
        self.address_uses.remove(moved);
        for (id, offset) in uses.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let translated =
                PointerOffsetTerm::Add(Box::new((**offset).clone()), Box::new(delta.clone()));
            let (new, _) = self.address(kept.clone(), translated);
            self.close(vec![(*id, new)]);
        }
    }

    /// Checked pointer premises join address applications in the same closure
    /// that propagates whole-offset equality. No adjacency search is retained.
    pub(super) fn add_address_equality(&mut self, left: u64, right: u64) -> bool {
        debug_assert!(self.address_nodes.contains(&left));
        debug_assert!(self.address_nodes.contains(&right));
        self.close(vec![(left, right)])
    }

    pub(super) fn class_root(&self, id: u64) -> u64 {
        self.root(id)
    }

    pub(super) fn has_scalar_constant_conflict(&self) -> bool {
        self.scalar_constant_conflict
    }

    /// Whether a query can find two offsets equal that differ in spelling: a
    /// merge exists, or a defined byte product joins its byte offset to its
    /// element offset as soon as the query registers that node.
    pub(super) fn has_equivalences(&self) -> bool {
        !self.parents.is_empty() || !self.defined_byte_products.is_empty()
    }

    /// A non-affine offset equality can add suppliers not represented by an
    /// affine interval tree. Report unknown only for address blocks reached by
    /// that equality's registered parent dependencies. No class/frame walk.
    pub(super) fn affine_addresses_complete(&self, block: &PointerBlock) -> bool {
        !self.non_affine_address_blocks.contains(block)
    }

    fn mark_non_affine(&mut self, id: u64) {
        let mut pending = vec![id];
        while let Some(id) = pending.pop() {
            let root = self.root(id);
            if self.non_affine_classes.contains(&root) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            self.non_affine_classes = self.non_affine_classes.with_value(root);
            let applications = self
                .affine_applications
                .get(&root)
                .cloned()
                .unwrap_or_default();
            self.affine_applications.remove(&root);
            for id in applications.iter() {
                crate::instrumentation::record_deterministic_work(1);
                let application = *self.applications.get(id).expect("application");
                if let Application::Address(block, _) = application {
                    let block = self.address_blocks.get(&block).expect("address block");
                    self.non_affine_address_blocks =
                        self.non_affine_address_blocks.with_value(block.clone());
                }
                // Remove already-affected parents from the completeness-use
                // index. A later fork must not revisit them just because one
                // previously unrelated operand learns its first alias.
                for operand in application.operands() {
                    let operand = self.root(operand);
                    if let Some(uses) = self.affine_uses.get(&operand) {
                        let uses = uses.without_value(id);
                        if uses.is_empty() {
                            self.affine_uses.remove(&operand);
                        } else {
                            self.affine_uses.insert(operand, uses);
                        }
                    }
                }
            }
            if let Some(uses) = self.affine_uses.get(&root) {
                pending.extend(uses.iter().copied());
            }
        }
    }

    fn merge_affine_applications(&mut self, moved: u64, kept: u64) {
        // Only clean classes retain these sets. Each moved application/use is
        // already charged to the graph's smaller-side union weight.
        for map in [&mut self.affine_applications, &mut self.affine_uses] {
            if let Some(moved_set) = map.get(&moved).cloned() {
                let mut kept_set = map.get(&kept).cloned().unwrap_or_default();
                for id in moved_set.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    kept_set = kept_set.with_value(*id);
                }
                map.remove(&moved);
                map.insert(kept, kept_set);
            }
        }
    }

    /// Register the mathematical offset directly. Internal normalization uses
    /// retained atom identities; structural spelling order belongs to output.
    /// Keep the same representable coefficient domain as `to_offset_term`.
    fn intern_affine_offset(&mut self, offset: &AffineOffset) -> Option<u64> {
        use crate::kernel::MachineOperandView as V;
        let constant = i64::try_from(offset.constant).ok()?;
        let mut result = self.intern_node(Node::Constant(constant));
        let mut empty = constant == 0;
        for (atom, coefficient) in &offset.terms {
            crate::instrumentation::record_deterministic_work(1);
            let coefficient = i64::try_from(*coefficient).ok()?;
            let node =
                match atom {
                    OffsetAtom::Variable(variable) if coefficient == 1 => Node::Variable(*variable),
                    OffsetAtom::Variable(_) => return None,
                    OffsetAtom::Int32(value) => {
                        let shared = value;
                        let value = match value.operand_view() {
                            V::Legacy(term) => self.intern_int32(term),
                            V::Shared(root) => self
                                .intern_shared_machine(root, crate::kernel::CarrierWidth::Bits32),
                        };
                        if coefficient == 1 {
                            let id = self.intern_node(Node::Int32Scaled(value, 1));
                            self.register_byte_product_node(&shared.0, id);
                            result = if empty {
                                id
                            } else {
                                self.intern_node(Node::Add(result, id))
                            };
                            empty = false;
                            continue;
                        }
                        Node::Int32Scaled(value, coefficient)
                    }
                    OffsetAtom::Int64 { value, unsigned } => {
                        let value = match value.operand_view() {
                            V::Legacy(term) => self.intern_uint64(term),
                            V::Shared(root) => self
                                .intern_shared_machine(root, crate::kernel::CarrierWidth::Bits64),
                        };
                        Node::Int64Scaled(value, coefficient, *unsigned)
                    }
                };
            let addend = self.intern_node(node);
            result = if empty {
                addend
            } else {
                self.intern_node(Node::Add(result, addend))
            };
            empty = false;
        }
        Some(result)
    }

    fn intern(&mut self, term: &PointerOffsetTerm) -> u64 {
        enum Work<'a> {
            Term(&'a PointerOffsetTerm),
            Add,
        }
        let mut pending = vec![Work::Term(term)];
        let mut values = Vec::new();
        let mut byte_products = Vec::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let node = match work {
                Work::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    Node::Add(left, right)
                }
                Work::Term(term) => match term {
                    PointerOffsetTerm::Constant(value) => Node::Constant(*value),
                    PointerOffsetTerm::Variable(variable) => Node::Variable(*variable),
                    PointerOffsetTerm::Add(left, right) => {
                        pending.push(Work::Add);
                        pending.push(Work::Term(right));
                        pending.push(Work::Term(left));
                        continue;
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                        let node = Node::Int32Scaled(
                            match value.operand_view() {
                                crate::kernel::MachineOperandView::Legacy(term) => {
                                    self.intern_int32(term)
                                }
                                crate::kernel::MachineOperandView::Shared(root) => self
                                    .intern_shared_machine(
                                        root,
                                        crate::kernel::CarrierWidth::Bits32,
                                    ),
                            },
                            *byte_width,
                        );
                        if *byte_width == 1 {
                            let id = self.intern_node(node);
                            byte_products.push((value, id));
                            values.push(id);
                            continue;
                        }
                        node
                    }
                    PointerOffsetTerm::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => Node::Int64Scaled(
                        match value.operand_view() {
                            crate::kernel::MachineOperandView::Legacy(term) => {
                                self.intern_uint64(term)
                            }
                            crate::kernel::MachineOperandView::Shared(root) => self
                                .intern_shared_machine(root, crate::kernel::CarrierWidth::Bits64),
                        },
                        *byte_width,
                        *unsigned,
                    ),
                },
            };
            let id = self.intern_node(node);
            values.push(id);
        }
        for (value, id) in byte_products {
            self.register_byte_product_node(value, id);
        }
        values.pop().expect("offset term")
    }

    /// File the byte-offset node `Int32Scaled { x * K, 1 }` under its
    /// product's identity, and join it to element `x` at stride `K` when the
    /// product is already known not to wrap. One keyed lookup; any other
    /// value is left alone.
    fn register_byte_product_node(
        &mut self,
        value: &crate::kernel::SharedMachineIntegerTerm,
        id: u64,
    ) {
        if byte_product_operands(value).is_none() {
            return;
        }
        let Some(key) = byte_product_key(value) else {
            return;
        };
        if self.byte_product_nodes.get(&key).is_none() {
            self.byte_product_nodes.insert(key, id);
        }
        if let Some((index, stride)) = self.defined_byte_products.get(&key).cloned() {
            let element = self.intern(&PointerOffsetTerm::Int32Scaled {
                value: index,
                byte_width: stride,
            });
            self.close(vec![(id, element)]);
        }
    }

    /// Admit that the `int32` product `value`, `index * stride`, does not
    /// wrap: its byte offset and element `index` at `stride` are one exact
    /// offset. A byte-offset node already registered for the product is joined
    /// now; one registered later joins when it is registered. Nothing is
    /// interned unless that node exists.
    pub(super) fn admit_defined_byte_product(
        &mut self,
        value: &crate::kernel::SharedMachineIntegerTerm,
        index: crate::kernel::SharedMachineIntegerTerm,
        stride: i64,
    ) {
        let Some(key) = byte_product_key(value) else {
            return;
        };
        self.defined_byte_products
            .insert(key, (index.clone(), stride));
        if let Some(node) = self.byte_product_nodes.get(&key).copied() {
            let element = self.intern(&PointerOffsetTerm::Int32Scaled {
                value: index,
                byte_width: stride,
            });
            self.close(vec![(node, element)]);
        }
    }

    fn intern_node(&mut self, node: Node) -> u64 {
        if let Some(id) = self.nodes.get(&node).copied() {
            self.enqueue_int32_load(id, &node);
            self.enqueue_narrow_load(id, &node);
            return id;
        }
        let id = self.nodes.len() as u64;
        match &node {
            Node::AlgebraicConstructor(_, variant, arity) => {
                self.constructor_heads.insert(id, (variant.clone(), *arity));
            }
            Node::ArgumentTag(_) => self.argument_tags = self.argument_tags.with_value(id),
            _ => {}
        }
        let application = match &node {
            Node::Apply(left, right) => Some(Application::Apply(*left, *right)),
            Node::Condition(kind, left, right) => {
                Some(Application::Condition(*kind, *left, *right))
            }
            Node::UInt64Binary(op, left, right) => {
                Some(Application::UInt64Binary(*op, *left, *right))
            }
            Node::UInt64Address(address) => Some(Application::UInt64Address(*address)),
            Node::UInt64Read(retained_state, address) => {
                Some(Application::UInt64Read(*retained_state, *address))
            }
            Node::Address(block, offset) => {
                self.address_nodes = self.address_nodes.with_value(id);
                self.offsets_by_address_block
                    .insert(id, PersistentMap::default().with_inserted(*block, *offset));
                let root = self.root(*offset);
                let mut addresses = self
                    .addresses_by_offset
                    .get(&root)
                    .cloned()
                    .unwrap_or_default();
                if !addresses.contains_key(block) {
                    addresses.insert(*block, id);
                    self.addresses_by_offset.insert(root, addresses);
                }
                Some(Application::Address(*block, *offset))
            }
            Node::AddressShift(address, bytes) => {
                self.address_nodes = self.address_nodes.with_value(id);
                Some(Application::AddressShift(*address, *bytes))
            }
            Node::AddressOffset(address, offset) => {
                self.address_nodes = self.address_nodes.with_value(id);
                Some(Application::AddressOffset(*address, *offset))
            }
            Node::PointerRead(retained_state, address, kind) => {
                Some(Application::PointerRead(*retained_state, *address, *kind))
            }
            Node::Int32Read(retained_state, address) => {
                Some(Application::Int32Load(*retained_state, *address))
            }
            Node::NarrowRead(retained_state, address, kind) => {
                Some(Application::NarrowLoad(*retained_state, *address, *kind))
            }
            Node::Footprint(start, end) => Some(Application::Footprint(*start, *end)),
            Node::Add(left, right) => Some(Application::Add(*left, *right)),
            Node::Int32Add(left, right) => Some(Application::Int32Add(*left, *right)),
            Node::Int32Binary(op, left, right) => {
                Some(Application::Int32Binary(*op, *left, *right))
            }
            Node::Int32Unary(op, value) => Some(Application::Int32Unary(*op, *value)),
            Node::Int32Scaled(value, width) => Some(Application::Int32Scaled(*value, *width)),
            Node::Int64Scaled(value, width, unsigned) => {
                Some(Application::Int64Scaled(*value, *width, *unsigned))
            }
            Node::Int32(value) => {
                if let Some(variable) = value.operand_view().variable() {
                    self.register_scalar_variable(id, *variable);
                }
                if let Some(value) = value.operand_view().word32_constant() {
                    self.int32_constants.insert(id, value as i32);
                }
                None
            }
            Node::MachineNarrow(atom) => {
                if let Some(crate::kernel::native_constant!(_, bits)) =
                    atom.operand_view().literal()
                {
                    self.narrow_constants.insert(id, bits as u32);
                }
                None
            }
            Node::UInt64(value) => {
                let literal = match value.operand_view().literal() {
                    Some(uint64_constant!(value)) => Some(constant_u64(value)),
                    Some(int64_constant!(value)) => Some(constant_i64(value) as u64),
                    _ => None,
                };
                if let Some(value) = literal {
                    self.uint64_constants.insert(id, value);
                }
                None
            }
            _ => None,
        };
        self.enqueue_int32_load(id, &node);
        self.enqueue_narrow_load(id, &node);
        self.enqueue_signed_byte_read(id, &node);
        self.retain_machine_head(id, &node);
        self.nodes.insert(node, id);
        self.markers.insert(id, Arc::new(()));
        if let Some(application) = application {
            self.register_application(id, application);
        }
        id
    }

    fn enqueue_int32_load(&mut self, id: u64, node: &Node) {
        let Node::Int32(atom) = node else { return };
        if self.registered_int32_loads.contains(&id) {
            return;
        }
        let Some(read) = crate::kernel::eval::scalar_read_observation(atom.operand_view()) else {
            return;
        };
        if read.bytes != 4 || !read.kind.is_word32() {
            return;
        }
        self.registered_int32_loads = self.registered_int32_loads.with_value(id);
        if read.kind == crate::kernel::LoadKind::UInt32 {
            self.pending_unsigned_word_reads
                .push((id, read.memory, read.pointer));
            return;
        }
        let origin = read
            .origin
            .filter(|origin| origin.read_identity() == read.memory.read_identity());
        self.pending_loads
            .push((id, read.memory, read.pointer, origin));
    }

    fn enqueue_narrow_load(&mut self, id: u64, node: &Node) {
        let Node::MachineNarrow(atom) = node else {
            return;
        };
        if self.registered_int32_loads.contains(&id) {
            return;
        }
        let Some(read) = crate::kernel::eval::scalar_read_observation(atom.operand_view()) else {
            return;
        };
        let bytes = match read.kind {
            crate::kernel::LoadKind::Int8 | crate::kernel::LoadKind::UInt8 => 1,
            crate::kernel::LoadKind::Int16 | crate::kernel::LoadKind::UInt16 => 2,
            _ => return,
        };
        // A wider recorded observation must not acquire a narrower read rule.
        if read.bytes != bytes {
            return;
        }
        self.registered_int32_loads = self.registered_int32_loads.with_value(id);
        let origin = read
            .origin
            .filter(|origin| origin.read_identity() == read.memory.read_identity());
        self.pending_narrow_loads
            .push((id, read.memory, read.pointer, read.kind, origin));
    }

    fn enqueue_signed_byte_read(&mut self, id: u64, node: &Node) {
        let Node::MachineNarrow(atom) = node else {
            return;
        };
        let Some(read) = crate::kernel::eval::scalar_read_observation(atom.operand_view()) else {
            return;
        };
        if read.kind != crate::kernel::LoadKind::Int8 || read.bytes != 1 {
            return;
        }
        self.pending_signed_byte_reads
            .push((id, read.memory, read.pointer));
    }

    fn register_pending_loads(&mut self) {
        if self.registering_dependencies {
            return;
        }
        self.registering_dependencies = true;
        loop {
            if let Some((value, application)) = self.pending_pointer_calls.pop() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(bits) = application.integer_address_bits() {
                    // Decode only numeric coordinates. In particular, do not
                    // merge the address node with a word or a pointer value.
                    // The existing dependency worklist also handles nested
                    // casts without recursively registering their states.
                    let numeric = self.read_address(value);
                    let bits = self.intern_uint64(bits);
                    self.close_with_affine_definition(vec![(numeric, bits)], true);
                    continue;
                }
                let call = self.intern_pointer_call(&application);
                self.close_with_affine_definition(vec![(value, call)], true);
                self.retain_pointer_value_witness(
                    self.root(value),
                    PointerBlock::PureFunctionApplication(application),
                );
                continue;
            }
            if let Some((identity, application)) = self.pending_pointer_identities.pop() {
                crate::instrumentation::record_deterministic_work(1);
                let value = self.intern_pointer_call_identity(&application);
                self.close_with_affine_definition(vec![(identity, value)], true);
                continue;
            }
            // R-mem at 32 bits: a `uint32` read is σ of its cell's `int32`
            // read, whose own registration makes it the cell's word load
            // application. One read interned, one σ node, one union.
            if let Some((unsigned, memory, pointer)) = self.pending_unsigned_word_reads.pop() {
                crate::instrumentation::record_deterministic_work(1);
                let signed = crate::kernel::eval::scalar_read_for_exact_cell(
                    &memory,
                    &pointer,
                    crate::kernel::LoadKind::Int32,
                    4,
                );
                let signed = self.intern_machine(&signed, false);
                let cast = self.intern_node(Node::Int32Unary(
                    Int32Unary::Cast(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineIntegerType::UInt32,
                    ),
                    signed,
                ));
                self.close(vec![(unsigned, cast)]);
                continue;
            }
            if let Some((signed, memory, pointer)) = self.pending_signed_byte_reads.pop() {
                crate::instrumentation::record_deterministic_work(1);
                let unsigned = crate::kernel::eval::scalar_read_for_exact_cell(
                    &memory,
                    &pointer,
                    crate::kernel::LoadKind::UInt8,
                    1,
                );
                let byte = self.intern_typed_machine(&unsigned, crate::kernel::CarrierWidth::Bits8);
                let cast = self.narrow_cast_node(
                    crate::kernel::MachineIntegerType::UInt8,
                    crate::kernel::MachineIntegerType::Int8,
                    byte,
                    false,
                );
                self.close(vec![(signed, cast)]);
                continue;
            }
            if let Some((id, memory, pointer, kind, origin)) = self.pending_narrow_loads.pop() {
                crate::instrumentation::record_deterministic_work(1);
                let address = self
                    .address(pointer.block.clone(), pointer.offset.clone())
                    .0;
                let address = self.read_address(address);
                self.register_application(
                    id,
                    Application::NarrowLoad(memory.read_identity(), address, kind),
                );
                // The read's recorded projection source at the same address,
                // as for a four-byte read: one indexed edge, no history walk.
                if let Some(source) =
                    crate::kernel::prelude::canonical_load_projection_source(&memory, &pointer)
                {
                    let source_read =
                        self.intern_node(Node::NarrowRead(source.read_identity(), address, kind));
                    self.close_with_affine_definition(vec![(id, source_read)], true);
                }
                // The value a store left in the read's cell, as for a
                // four-byte read.
                let width = if kind.byte_width() == 1 {
                    crate::kernel::CarrierWidth::Bits8
                } else {
                    crate::kernel::CarrierWidth::Bits16
                };
                self.pending_cell_reads.push(PendingCellRead {
                    read: id,
                    memory,
                    origin,
                    pointer,
                    kind: CellRead::Narrow(width),
                    only: None,
                });
                continue;
            }
            let Some((id, memory, pointer, origin)) = self.pending_loads.pop() else {
                break;
            };
            crate::instrumentation::record_deterministic_work(1);
            // Integer reads use the same complete address application as
            // pointer and uint64 reads. A checked equality between addresses
            // must reindex this read even when no affine block relabel exists.
            let address = self
                .address(pointer.block.clone(), pointer.offset.clone())
                .0;
            let address = self.read_address(address);
            self.register_application(id, Application::Int32Load(memory.read_identity(), address));
            // Canonicalization recorded this exact cell projection when it
            // constructed the read. Retain both applications: the named read
            // and its source at the same address. This is one indexed edge,
            // not the mutable observation origin or a walk through history.
            if let Some(source) =
                crate::kernel::prelude::canonical_load_projection_source(&memory, &pointer)
            {
                let source_read =
                    self.intern_node(Node::Int32Read(source.read_identity(), address));
                self.close_with_affine_definition(vec![(id, source_read)], true);
            }
            self.pending_cell_reads.push(PendingCellRead {
                read: id,
                memory,
                origin,
                pointer,
                kind: CellRead::Int32,
                only: None,
            });
        }
        while let Some(pending) = self.pending_cell_reads.pop() {
            self.equate_read_with_aliased_cell(pending);
        }
        self.registering_dependencies = false;
    }

    /// A read of a state at an address equals the value the state
    /// stores at an equal address under another spelling: a store through
    /// `p` read through `id` once `p == id`. The read keeps its own term,
    /// fact-free; the equality of the two addresses is this context's, so
    /// the union is too (`docs/internals/spellability.md`). The spellings
    /// are the read's address in each member of its block class, one cell
    /// lookup each, as `EqualityGraph::pointer_spellings` spells them.
    fn equate_read_with_aliased_cell(&mut self, pending: PendingCellRead) {
        let PendingCellRead {
            read,
            ref memory,
            ref origin,
            ref pointer,
            kind,
            ref only,
        } = pending;
        let (root, own) = self
            .block_roots
            .get(&pointer.block)
            .cloned()
            .unwrap_or_else(|| (pointer.block.clone(), AffineOffset::default()));
        let members: Arc<[(PointerBlock, AffineOffset)]> = only.clone().unwrap_or_else(|| {
            std::iter::once((root.clone(), AffineOffset::default()))
                .chain(
                    self.block_members
                        .get(&root)
                        .into_iter()
                        .flat_map(|members| members.iter())
                        .map(|(member, delta)| (member.clone(), delta.clone())),
                )
                .collect()
        });
        let offset = AffineOffset::of(&pointer.offset);
        let mut found = None;
        for (member, delta) in members.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let spelling = if *member == pointer.block {
                Some(pointer.offset.clone())
            } else {
                offset
                    .as_ref()
                    .and_then(|offset| offset.checked_add(&own.checked_sub(delta)?))
                    .and_then(|offset| offset.to_offset_term())
            };
            let Some(spelling) = spelling else {
                continue;
            };
            let cell = Pointer {
                block: member.clone(),
                offset: spelling,
            };
            let stored = std::iter::once(memory)
                .chain(origin)
                .find_map(|memory| memory.known_value(&cell));
            use crate::kernel::ProgramValue as V;
            found = match (stored, kind) {
                (Some(V::Int64(value) | V::UInt64(value)), CellRead::UInt64)
                | (Some(V::Int32(value)), CellRead::Int32) => Some(Ok(value)),
                // The `int32` read of a cell storing a `uint32` value is σ of
                // that value (rule K5's reinterpretation, σ a node).
                (Some(V::UInt32(value)), CellRead::Int32) => {
                    Some(Ok(crate::kernel::MachineTerm::sign_cast32(
                        crate::kernel::MachineIntegerType::UInt32,
                        crate::kernel::MachineIntegerType::Int32,
                        value,
                    )))
                }
                (
                    Some(V::Bool(value) | V::Int8(value) | V::UInt8(value)),
                    CellRead::Narrow(crate::kernel::CarrierWidth::Bits8),
                )
                | (
                    Some(V::Int16(value) | V::UInt16(value)),
                    CellRead::Narrow(crate::kernel::CarrierWidth::Bits16),
                ) => Some(Ok(value)),
                (Some(V::Pointer(value)), CellRead::FunctionPointer)
                    if matches!(
                        value.program_type(),
                        crate::kernel::ProgramType::FunctionPointer(_)
                    ) =>
                {
                    Some(Err(value.pointer().clone()))
                }
                _ => continue,
            };
            break;
        }
        let value = match found {
            Some(Ok(value)) => match kind {
                CellRead::Narrow(width) => self.intern_typed_machine(&value, width),
                _ => self.intern_machine(&value, kind == CellRead::UInt64),
            },
            // The read's value is a pointer; its address is the designator's.
            Some(Err(stored)) => self.address(stored.block, stored.offset).0,
            None => {
                let mut reads = self
                    .unresolved_cell_reads
                    .get(&root)
                    .cloned()
                    .unwrap_or_default();
                if !reads.contains_key(&read) {
                    reads.insert(
                        read,
                        Arc::new(PendingCellRead {
                            only: None,
                            ..pending
                        }),
                    );
                    self.unresolved_cell_reads.insert(root, reads);
                }
                return;
            }
        };
        self.close(vec![(read, value)]);
    }

    /// Mirrors one block union of the graph: `moved` (its class's root) and
    /// its members, each with its new base relative to `kept`, join `kept`'s
    /// class. Each side's unresolved reads then look in the members the
    /// other side brings. Work is in the moved members and those reads.
    pub(super) fn join_block_classes(
        &mut self,
        moved: &PointerBlock,
        kept: &PointerBlock,
        moved_members: &[(PointerBlock, AffineOffset)],
    ) {
        let kept_members: Arc<[(PointerBlock, AffineOffset)]> =
            std::iter::once((kept.clone(), AffineOffset::default()))
                .chain(
                    self.block_members
                        .get(kept)
                        .into_iter()
                        .flat_map(|members| members.iter())
                        .map(|(member, delta)| (member.clone(), delta.clone())),
                )
                .collect();
        let moved_members: Arc<[(PointerBlock, AffineOffset)]> = moved_members.into();
        let mut members = self.block_members.get(kept).cloned().unwrap_or_default();
        for (member, delta) in moved_members.iter() {
            crate::instrumentation::record_deterministic_work(1);
            self.block_roots
                .insert(member.clone(), (kept.clone(), delta.clone()));
            members.insert(member.clone(), delta.clone());
        }
        self.block_members.remove(moved);
        self.block_members.insert(kept.clone(), members);
        let moved_reads = self.unresolved_cell_reads.get(moved).cloned();
        let kept_reads = self.unresolved_cell_reads.get(kept).cloned();
        self.unresolved_cell_reads.remove(moved);
        self.unresolved_cell_reads.remove(kept);
        for (reads, other) in [(moved_reads, kept_members), (kept_reads, moved_members)] {
            for entry in reads.iter().flat_map(|reads| reads.values()) {
                crate::instrumentation::record_deterministic_work(1);
                self.pending_cell_reads.push(PendingCellRead {
                    only: Some(other.clone()),
                    ..(**entry).clone()
                });
            }
        }
        self.register_pending_loads();
    }

    pub(super) fn record_wide_equation_endpoint(&mut self, term: &crate::kernel::MachineTerm) {
        let id = self.intern_uint64(term);
        self.register_pending_loads();
        let root = self.root(id);
        let endpoints = self
            .wide_equation_endpoints
            .get(&root)
            .cloned()
            .unwrap_or_default();
        if !endpoints.contains(term) {
            self.wide_equation_endpoints
                .insert(root, endpoints.with_value(term.clone()));
        }
    }

    /// The recorded equality endpoints in `term`'s class.
    pub(super) fn wide_equation_endpoints_equal_to(
        &mut self,
        term: &crate::kernel::MachineTerm,
    ) -> PersistentSet<crate::kernel::MachineTerm> {
        let id = self.intern_uint64(term);
        self.register_pending_loads();
        self.wide_equation_endpoints_of_class(id)
    }

    pub(super) fn wide_equation_endpoints_of_class(
        &self,
        id: u64,
    ) -> PersistentSet<crate::kernel::MachineTerm> {
        self.wide_equation_endpoints
            .get(&self.root(id))
            .cloned()
            .unwrap_or_default()
    }

    fn merge_wide_equation_endpoints(&mut self, moved: u64, kept: u64) {
        let Some(moved_endpoints) = self.wide_equation_endpoints.get(&moved).cloned() else {
            return;
        };
        self.wide_equation_endpoints.remove(&moved);
        let kept_endpoints = self
            .wide_equation_endpoints
            .get(&kept)
            .cloned()
            .unwrap_or_default();
        let (mut larger, smaller) = if moved_endpoints.len() > kept_endpoints.len() {
            (moved_endpoints, kept_endpoints)
        } else {
            (kept_endpoints, moved_endpoints)
        };
        for endpoint in smaller.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger = larger.with_value(endpoint.clone());
        }
        self.wide_equation_endpoints.insert(kept, larger);
    }

    fn intern_uint64(&mut self, term: &crate::kernel::MachineTerm) -> u64 {
        self.intern_machine(term, true)
    }

    pub(super) fn uint64_constant(&mut self, term: &crate::kernel::MachineTerm) -> Option<u64> {
        let id = self.intern_uint64(term);
        self.register_pending_loads();
        let root = self.root(id);
        if self.scalar_conflicts.contains(&root) {
            return None;
        }
        self.uint64_constants.get(&root).copied()
    }

    pub(super) fn shared_uint64_class(&mut self, term: &crate::kernel::KernelTerm) -> u64 {
        let id = self.intern_shared_machine(term, crate::kernel::CarrierWidth::Bits64);
        self.register_pending_loads();
        id
    }

    pub(super) fn uint64_constant_of_class(&self, id: u64) -> Option<u64> {
        let root = self.root(id);
        if self.scalar_conflicts.contains(&root) {
            return None;
        }
        self.uint64_constants.get(&root).copied()
    }

    pub(super) fn are_uint64_equal(
        &mut self,
        left: &crate::kernel::MachineTerm,
        right: &crate::kernel::MachineTerm,
    ) -> bool {
        let left = self.intern_uint64(left);
        let right = self.intern_uint64(right);
        self.register_pending_loads();
        self.root(left) == self.root(right)
    }

    pub(super) fn add_uint64_equality(
        &mut self,
        left: &crate::kernel::MachineTerm,
        right: &crate::kernel::MachineTerm,
    ) -> bool {
        let left = self.intern_uint64(left);
        let right = self.intern_uint64(right);
        self.register_pending_loads();
        left != right && self.close(vec![(left, right)])
    }

    pub(super) fn scalar_class_root(&self, id: u64) -> u64 {
        self.root(id)
    }

    fn intern_int32(&mut self, term: &crate::kernel::MachineTerm) -> u64 {
        // This interner runs under the graph mutex. Memory canonicalization
        // can re-enter this graph through a cell-version walk; callers perform
        // it before locking, while raw reads here retain their own state.
        self.intern_machine(term, false)
    }

    pub(super) fn int32_class(&mut self, term: &crate::kernel::MachineTerm) -> u64 {
        let node = self.intern_int32(term);
        self.register_pending_loads();
        self.root(node)
    }

    pub(super) fn shared_int32_class(&mut self, term: &crate::kernel::KernelTerm) -> u64 {
        let node = self.intern_shared_machine(term, crate::kernel::CarrierWidth::Bits32);
        self.register_pending_loads();
        self.root(node)
    }

    pub(super) fn existing_scalar_atom(
        &self,
        term: &crate::kernel::MachineTerm,
    ) -> Option<Option<u64>> {
        let application = has_machine_operands(term);
        (!application).then(|| {
            self.nodes
                .get(&Node::Int32(MachineAtom::int32(term.clone())))
                .copied()
        })
    }

    pub(super) fn signed_int32_interval(&self, node: u64) -> Option<(i64, i64)> {
        self.signed_int32_intervals
            .get(&self.root(node))
            .copied()
            .filter(|(lower, upper)| lower <= upper)
    }

    fn retain_signed_int32_interval(
        &mut self,
        term: crate::kernel::MachineOperandView<'_>,
        lower: i64,
        upper: i64,
    ) {
        let node = match term {
            crate::kernel::MachineOperandView::Shared(term) => {
                self.intern_shared_machine(term, crate::kernel::CarrierWidth::Bits32)
            }
            crate::kernel::MachineOperandView::Legacy(term) => self.intern_int32(term),
        };
        self.register_pending_loads();
        let root = self.root(node);
        let previous = self
            .signed_int32_intervals
            .get(&root)
            .copied()
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        self.signed_int32_intervals
            .insert(root, (previous.0.max(lower), previous.1.min(upper)));
        crate::instrumentation::record_deterministic_work(1);
    }

    /// Without scalar equality inputs, an unknown folding-only application cannot
    /// create a new interval. Reuse its existing node when present;
    /// avoid registering fresh arithmetic just to discover that it is unbound.
    pub(super) fn existing_scalar_interval_node(
        &self,
        term: &crate::kernel::MachineTerm,
    ) -> Option<Option<u64>> {
        if term.as_const().is_none() {
            let unary = if let unary_term!(Bits32, BitwiseNot, value) = term {
                Some((Int32Unary::Not, value.as_ref()))
            } else {
                constants::word_cast_operand(term).map(|(value, source, destination)| {
                    (Int32Unary::Cast(source, destination), value)
                })
            };
            if let Some((op, operand)) = unary {
                return self.existing_scalar_atom(operand).map(|operand| {
                    operand
                        .and_then(|operand| self.nodes.get(&Node::Int32Unary(op, operand)).copied())
                });
            }
        }
        if term.as_const().is_none()
            && let Some((op, left, right)) = term.as_binary()
            && op.is_bitvector32()
            && let op = word_operator(op)
            && !matches!(
                op,
                crate::kernel::BitvectorBinaryOp::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineBinaryOp::Add
                ) | crate::kernel::BitvectorBinaryOp::Machine(
                    crate::kernel::MachineIntegerType::UInt32,
                    crate::kernel::MachineBinaryOp::Divide
                ) | crate::kernel::BitvectorBinaryOp::Machine(
                    crate::kernel::MachineIntegerType::UInt32,
                    crate::kernel::MachineBinaryOp::Remainder
                ) | crate::kernel::BitvectorBinaryOp::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineBinaryOp::BitwiseXor
                )
            )
            && let (Some(left), Some(right)) = (
                self.existing_scalar_atom(left),
                self.existing_scalar_atom(right),
            )
        {
            return Some(left.zip(right).and_then(|(left, right)| {
                self.nodes
                    .get(&Node::Int32Binary(Int32Binary::Other(op), left, right))
                    .copied()
            }));
        }
        None
    }

    pub(super) fn are_int32_equal(
        &mut self,
        left: &crate::kernel::MachineTerm,
        right: &crate::kernel::MachineTerm,
    ) -> bool {
        use crate::kernel::MachineTerm;
        if left == right {
            return true;
        }
        // Opaque atoms cannot acquire equality by query registration. Consult
        // their existing nodes directly, avoiding registration of unrelated
        // order endpoints and unsupported expressions. Loads and addition
        // still need registration because their definitions can join classes.
        let opaque = |term: &MachineTerm| {
            if has_machine_operands(term) {
                return None;
            }
            let term = term.clone();
            (!has_machine_operands(&term)).then(|| Node::Int32(MachineAtom::int32(term)))
        };
        let left_atom = opaque(left);
        let right_atom = opaque(right);
        if left_atom.is_some() && left_atom == right_atom {
            return true;
        }
        // Two opaque endpoints cannot introduce one another. An application
        // can, however, introduce an operand and prove itself equal to it
        // (for example, a wide cast round trip). Do not reject its missing
        // opaque endpoint before registering that explicit expression.
        if left_atom.is_some() && right_atom.is_some() {
            for atom in [&left_atom, &right_atom].into_iter().flatten() {
                if let Node::Int32(value) = atom
                    && !matches!(value.operand_view().literal(), Some(bits32_constant!(_)))
                    && !self.nodes.contains_key(atom)
                {
                    return false;
                }
            }
        }
        if let (Some(left), Some(right)) = (left_atom, right_atom) {
            // Predicate signatures may register operands without equating any
            // values. Distinct opaque atoms cannot meet in that graph.
            if !self.has_equivalences() {
                return false;
            }
            return match (self.nodes.get(&left), self.nodes.get(&right)) {
                (Some(left), Some(right)) => {
                    left == right
                        || ((self.parents.contains_key(left) || self.parents.contains_key(right))
                            && self.root(*left) == self.root(*right))
                }
                _ => false,
            };
        }
        let left = self.intern_int32(left);
        let right = self.intern_int32(right);
        self.register_pending_loads();
        // Reflexivity needs no class traversal, even when this node was merged.
        left == right || self.root(left) == self.root(right)
    }

    pub(super) fn add_int32_equality(
        &mut self,
        left: &crate::kernel::MachineTerm,
        right: &crate::kernel::MachineTerm,
    ) -> bool {
        let left = self.intern_int32(left);
        let right = self.intern_int32(right);
        self.register_pending_loads();
        left != right && self.close(vec![(left, right)])
    }

    /// Retain a root-local word identity established by the comparison form.
    /// Keeping its result makes a later shared prefix reuse the earlier step.
    pub(super) fn add_shared_word_identity(
        &mut self,
        left: &crate::kernel::KernelTerm,
        right: &crate::kernel::KernelTerm,
    ) -> bool {
        let left = self.shared_int32_class(left);
        let right = self.shared_int32_class(right);
        left != right && self.close(vec![(left, right)])
    }

    fn root(&self, mut id: u64) -> u64 {
        let original = id;
        let epoch = self.history.as_ref().map_or(0, |history| history.depth);
        if let Some((cached_epoch, root)) = self.root_cache.0.borrow().get(&id).copied()
            && cached_epoch == epoch
        {
            return root;
        }
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match self.parents.get(&id) {
                Some(parent) => id = *parent,
                None => break,
            }
        }
        self.root_cache.0.borrow_mut().insert(original, (epoch, id));
        id
    }

    pub(super) fn are_equal(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let left = self.intern(left);
        let right = self.intern(right);
        self.register_pending_loads();
        self.root(left) == self.root(right)
    }

    pub(super) fn add_equality(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let left_id = self.intern(left);
        let right_id = self.intern(right);
        self.retain_additive_offset(left_id, left);
        self.retain_additive_offset(right_id, right);
        self.register_pending_loads();
        self.close(vec![(left_id, right_id)])
    }

    fn weight(&self, id: u64) -> usize {
        self.weights.get(&id).copied().unwrap_or(1)
    }

    fn register_application(&mut self, id: u64, application: Application) {
        self.applications.insert(id, application);
        let class = self.root(id);
        // Conditions and footprint predicates are boolean observations,
        // never address operands. Their congruence uses remain in `uses`.
        let affine = !matches!(
            application,
            Application::Condition(..) | Application::Footprint(..)
        ) && !self.non_affine_classes.contains(&class);
        if affine {
            let applications = self
                .affine_applications
                .get(&class)
                .cloned()
                .unwrap_or_default();
            self.affine_applications
                .insert(class, applications.with_value(id));
        }
        for operand in application.operands() {
            let root = self.root(operand);
            if matches!(
                application,
                Application::Add(..)
                    | Application::UInt64Binary(..)
                    | Application::Int32Add(..)
                    | Application::Int32Binary(..)
                    | Application::Int32Unary(..)
                    | Application::Int32Scaled(..)
                    | Application::Int64Scaled(..)
            ) {
                let uses = self.constant_uses.get(&root).cloned().unwrap_or_default();
                self.constant_uses.insert(root, uses.with_value(id));
            }
            if affine {
                let uses = self.affine_uses.get(&root).cloned().unwrap_or_default();
                self.affine_uses.insert(root, uses.with_value(id));
            }
            let uses = self.uses.get(&root).cloned().unwrap_or_default();
            if !uses.contains(&id) {
                self.uses.insert(root, uses.with_value(id));
                self.weights.insert(root, self.weight(root) + 1);
            }
        }
        let mut pending = PendingUnions::default();
        self.reindex_application(id, &mut pending);
        self.close_pending(pending);
    }

    /// Record an interned constructor application as its class's witness,
    /// joining it with a witness the class already has.
    fn retain_constructor_application(&mut self, id: u64) {
        let root = self.root(id);
        match self.constructor_applications.get(&root).copied() {
            None => {
                self.constructor_applications.insert(root, id);
            }
            Some(existing) if existing != id => {
                let mut pending = PendingUnions::default();
                self.join_constructor_applications(existing, id, &mut pending);
                self.close_pending(pending);
            }
            Some(_) => {}
        }
    }

    /// Two constructor applications in one class denote one value. The same
    /// variant has equal fields; distinct variants cannot be equal, so the
    /// context is empty. A field wrapped in one argument tag also joins the
    /// wrapped values, since a tag only names the field's sort.
    fn join_constructor_applications(
        &mut self,
        left: u64,
        right: u64,
        pending: &mut PendingUnions,
    ) {
        let (Some((left_head, left_fields)), Some((right_head, right_fields))) = (
            self.constructor_fields(left),
            self.constructor_fields(right),
        ) else {
            return;
        };
        let (Some((left_variant, _)), Some((right_variant, _))) = (
            self.constructor_heads.get(&left_head),
            self.constructor_heads.get(&right_head),
        ) else {
            return;
        };
        if left_variant != right_variant {
            self.scalar_constant_conflict = true;
            return;
        }
        if left_fields.len() != right_fields.len() {
            return;
        }
        for (left, right) in left_fields.into_iter().zip(right_fields) {
            crate::instrumentation::record_deterministic_work(1);
            pending.push((left, right));
            if let (
                Some(Application::Apply(left_tag, left)),
                Some(Application::Apply(right_tag, right)),
            ) = (self.applications.get(&left), self.applications.get(&right))
                && left_tag == right_tag
                && self.argument_tags.contains(left_tag)
            {
                pending.push((*left, *right));
            }
        }
    }

    /// The head and structural field nodes of a full constructor application.
    fn constructor_fields(&self, mut id: u64) -> Option<(u64, Vec<u64>)> {
        let mut fields = Vec::new();
        while !self.constructor_heads.contains_key(&id) {
            let Some(Application::Apply(head, field)) = self.applications.get(&id) else {
                return None;
            };
            fields.push(*field);
            id = *head;
        }
        let (_, arity) = self.constructor_heads.get(&id)?;
        if fields.len() != *arity {
            return None;
        }
        fields.reverse();
        Some((id, fields))
    }

    fn retain_condition_truth(&mut self, id: u64, truth: u8) {
        let root = self.root(id);
        let previous = self.condition_truth.get(&root).copied().unwrap_or(0);
        let combined = previous | truth;
        self.scalar_constant_conflict |= combined == 3;
        if combined != previous {
            self.condition_truth.insert(root, combined);
            if combined == 2 {
                self.cast_disequality_truth(id);
            }
            // Rule C1: a decided `Bool`'s casts are its constant.
            if matches!(combined, 1 | 2)
                && let Some(casts) = self.condition_casts.get(&root).cloned()
            {
                for cast in casts.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(link) = self.bool_cast_links.get(&self.root(*cast)).copied() {
                        let constant = if combined == 1 { link.one } else { link.zero };
                        self.pending_cast_unions.push((*cast, constant));
                    }
                }
                self.flush_cast_unions();
            }
        }
    }

    /// Rule C1: link the cast node `cast` of `b as F` with `b`'s condition
    /// node and the constants 0 and 1 at `F`, and pass on whatever either
    /// side already knows.
    pub(super) fn link_bool_cast(&mut self, cast: u64, condition: u64, zero: u64, one: u64) {
        let cast_root = self.root(cast);
        let condition_root = self.root(condition);
        match self.bool_cast_links.get(&cast_root).copied() {
            // Two casts in one class: `a as F == b as F` holds exactly when
            // `a` and `b` have the same truth.
            Some(link) if self.root(link.condition) != condition_root => {
                self.pending_cast_unions.push((link.condition, condition));
            }
            Some(_) => {}
            None => {
                self.bool_cast_links.insert(
                    cast_root,
                    BoolCastLink {
                        condition,
                        zero,
                        one,
                    },
                );
            }
        }
        let casts = self
            .condition_casts
            .get(&condition_root)
            .cloned()
            .unwrap_or_default()
            .with_value(cast);
        self.condition_casts.insert(condition_root, casts);
        match self.condition_truth.get(&condition_root).copied() {
            Some(1) => self.pending_cast_unions.push((cast, one)),
            Some(2) => self.pending_cast_unions.push((cast, zero)),
            _ => {}
        }
        self.cast_value_truth(cast_root);
        if let Some(uses) = self.uses.get(&cast_root).cloned() {
            for application in uses.iter() {
                if self.condition_truth.get(&self.root(*application)) == Some(&2) {
                    self.cast_disequality_truth(*application);
                }
            }
        }
        self.flush_cast_unions();
    }

    /// Rule C1: a cast class that holds a constant decides its `Bool`: 1 is
    /// true, 0 false, and any other value a contradiction.
    fn cast_value_truth(&mut self, class: u64) {
        let Some(link) = self.bool_cast_links.get(&class).copied() else {
            return;
        };
        let value = self
            .int32_constants
            .get(&class)
            .map(|value| i128::from(*value))
            .or_else(|| {
                self.uint64_constants
                    .get(&class)
                    .map(|value| i128::from(*value))
            })
            .or_else(|| {
                self.narrow_constants
                    .get(&class)
                    .map(|value| i128::from(*value))
            });
        match value {
            Some(1) => self.retain_condition_truth(link.condition, 1),
            Some(0) => self.retain_condition_truth(link.condition, 2),
            Some(_) => self.scalar_constant_conflict = true,
            None => {}
        }
    }

    /// Rule C1 read through a disequality: a cast is 0 or 1, so `b as F`
    /// unequal to 0 makes `b` true, and unequal to 1 makes it false. `node`
    /// is a false equality's condition node; one lookup per operand.
    fn cast_disequality_truth(&mut self, node: u64) {
        let Some(Application::Condition(
            congruence::ConditionKind::Int32Eq | congruence::ConditionKind::UInt64Eq,
            left,
            right,
        )) = self.applications.get(&node).copied()
        else {
            return;
        };
        for (cast, other) in [(left, right), (right, left)] {
            let Some(link) = self.bool_cast_links.get(&self.root(cast)).copied() else {
                continue;
            };
            let other = self.root(other);
            if other == self.root(link.zero) {
                self.retain_condition_truth(link.condition, 1);
            } else if other == self.root(link.one) {
                self.retain_condition_truth(link.condition, 2);
            }
        }
        // Two casts that differ: `a as F != b as F` holds exactly when `a`
        // and `b` differ in truth, the `Bool` equality `a == b` is false.
        if let (Some(left), Some(right)) = (
            self.bool_cast_links.get(&self.root(left)).copied(),
            self.bool_cast_links.get(&self.root(right)).copied(),
        ) {
            for (a, b) in [
                (left.condition, right.condition),
                (right.condition, left.condition),
            ] {
                let equality =
                    self.intern_node(Node::Condition(congruence::ConditionKind::BoolEq, a, b));
                self.retain_condition_truth(equality, 2);
            }
        }
    }

    fn flush_cast_unions(&mut self) {
        if self.closing || self.pending_cast_unions.is_empty() {
            return;
        }
        let unions = std::mem::take(&mut self.pending_cast_unions);
        self.close(unions);
    }

    /// The node of the constant `term` folds to at `ty`'s width: an 8- or
    /// 16-bit constant by its bits, or a 32-bit word. `None` when the term
    /// is not a constant of that width.
    fn machine_literal_node(
        &mut self,
        ty: crate::kernel::MachineIntegerType,
        term: &crate::kernel::MachineTerm,
    ) -> Option<u64> {
        use crate::kernel::{MachineIntegerType as M, MachineTerm as T};
        let width = ty.format().bits();
        if width < 32 {
            let bits = term.narrow_constant_bits(ty)?;
            let canonical = if width == 8 { M::UInt8 } else { M::UInt16 };
            return Some(self.intern_node(Node::MachineNarrow(MachineAtom::new(
                canonical,
                T::narrow_constant(canonical, bits),
            ))));
        }
        if width == 32 {
            let value = term.as_const()?;
            return Some(self.intern_node(Node::Int32(MachineAtom::int32(T::constant(value)))));
        }
        None
    }

    fn reindex_application(&mut self, id: u64, pending: &mut PendingUnions) {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(old) = self.application_signatures.get(&id).copied()
            && self.signatures.get(&old) == Some(&id)
        {
            self.signatures.remove(&old);
        }
        let signature = self
            .applications
            .get(&id)
            .expect("registered application")
            .signature(self);
        // Equality inputs merge operands rather than adding a second truth
        // predicate. A disequality becomes contradictory when those operands
        // meet, including after a late congruence merge. Parent-use indexing
        // brings only affected predicates here.
        if matches!(signature, Application::Condition(..))
            && self.condition_truth.get(&self.root(id)) == Some(&2)
        {
            self.cast_disequality_truth(id);
        }
        if let Application::Condition(kind, left, right) = signature
            && left == right
        {
            use congruence::ConditionKind::*;
            let truth = match kind {
                Int32Eq | UInt64Eq | PointerEq | OffsetEq | AlgebraicEq | IntegerEq | BoolEq => {
                    Some(1)
                }
                IntegerNe => Some(2),
                _ => None,
            };
            if let Some(truth) = truth {
                self.retain_condition_truth(id, truth);
            }
        }
        if signature
            .operands()
            .any(|operand| self.non_affine_classes.contains(&operand))
        {
            if let Application::Address(block, _) = signature {
                let block = self.address_blocks.get(&block).expect("address block");
                self.non_affine_address_blocks =
                    self.non_affine_address_blocks.with_value(block.clone());
            }
            self.mark_non_affine(id);
        }
        // PointerOffsetTerm folds literal int32 indices to byte constants.
        // Join that definitional form without solving any scalar arithmetic.
        if let Application::Int32Scaled(value, width) = signature
            && let Some(value) = self.int32_constants.get(&value)
            && let Some(bytes) = i64::from(*value).checked_mul(width)
        {
            let constant = self.intern_node(Node::Constant(bytes));
            pending.push((id, constant));
        }
        // Full-word equality selects the index value. Scaling is exact
        // offset arithmetic: preserve signedness and reject products outside
        // i64 rather than folding their wrapped low bits.
        if let Application::Int64Scaled(value, width, unsigned) = signature
            && let Some(bits) = self.uint64_constants.get(&value).copied()
            && let Some(index) = if unsigned {
                i64::try_from(bits).ok()
            } else {
                Some(bits as i64)
            }
            && let Some(bytes) = index.checked_mul(width)
        {
            let constant = self.intern_node(Node::Constant(bytes));
            pending.push((id, constant));
        }
        // PointerOffsetTerm removes zero addends at construction. Retain
        // that identity when a selected scaled index learns zero later;
        // parent-use indexing then reconnects the existing address and reads.
        if let Application::Add(left, right) = signature
            && let Some(zero) = self.nodes.get(&Node::Constant(0)).copied()
        {
            let zero = self.root(zero);
            if left == zero {
                pending.push_definition((id, right));
            } else if right == zero {
                pending.push_definition((id, left));
            }
        }
        // The checking constructor removes a zero addend. Keep that same
        // equality on shared word nodes, including when an operand learns zero.
        if let Application::Int32Add(left, right) = signature {
            if self.int32_constants.get(&left) == Some(&0) {
                pending.push((id, right));
            } else if self.int32_constants.get(&right) == Some(&0) {
                pending.push((id, left));
            }
        }
        // Kernel int32 values are bitvectors. Folding their sum wraps at 32
        // bits, just like MachineTerm::as_const; C signed definedness is a
        // separate obligation and is not established by equality congruence.
        if let Application::Int32Add(left, right) = signature
            && let (Some(left), Some(right)) = (
                self.int32_constants.get(&left),
                self.int32_constants.get(&right),
            )
        {
            let value = left.wrapping_add(*right) as u32;
            let constant = self.intern_node(Node::Int32(MachineAtom::int32(
                crate::kernel::MachineTerm::constant(value),
            )));
            pending.push((id, constant));
        }
        // Root-local identities formerly supplied by the boxed checking
        // constructors. Each firing reads the two selected operand summaries;
        // class merges revisit only indexed parent applications.
        if let Application::Int32Binary(op, left, right) = signature {
            use crate::kernel::{BitvectorBinaryOp as B, MachineBinaryOp as M};
            let operation = match op {
                Int32Binary::UnsignedDivide => Some(M::Divide),
                Int32Binary::BitwiseXor => Some(M::BitwiseXor),
                Int32Binary::Other(B::Machine(format, op)) if format.format().bits() == 32 => {
                    Some(op)
                }
                _ => None,
            };
            let a = self.int32_constants.get(&left).copied().map(|v| v as u32);
            let b = self.int32_constants.get(&right).copied().map(|v| v as u32);
            let identity = match operation {
                Some(M::Subtract) if b == Some(0) => Some(left),
                Some(M::Multiply) if a == Some(1) => Some(right),
                Some(M::Multiply | M::Divide) if b == Some(1) => Some(left),
                Some(M::BitwiseAnd) if a == Some(u32::MAX) => Some(right),
                Some(M::BitwiseAnd) if b == Some(u32::MAX) => Some(left),
                Some(M::BitwiseOr | M::BitwiseXor) if a == Some(0) => Some(right),
                Some(M::BitwiseOr | M::BitwiseXor | M::ShiftRight) if b == Some(0) => Some(left),
                Some(M::BitwiseAnd | M::BitwiseOr) if left == right => Some(left),
                _ => None,
            };
            let constant = match operation {
                Some(M::Subtract | M::BitwiseXor) if left == right => Some(0),
                Some(M::Multiply | M::BitwiseAnd) if a == Some(0) || b == Some(0) => Some(0),
                Some(M::BitwiseOr) if a == Some(u32::MAX) || b == Some(u32::MAX) => Some(u32::MAX),
                _ => None,
            };
            if let Some(other) = identity {
                pending.push((id, other));
            } else if let Some(value) = constant {
                let other = self.intern_node(Node::Int32(MachineAtom::int32(
                    crate::kernel::MachineTerm::constant(value),
                )));
                pending.push((id, other));
            }
        }
        if let Application::Int32Binary(op, left, right) = signature
            && let (Some(a), Some(b)) = (
                self.int32_constants.get(&left).copied(),
                self.int32_constants.get(&right).copied(),
            )
        {
            use crate::kernel::BitvectorBinaryOp as O;
            let op = match op {
                Int32Binary::UnsignedDivide => O::Machine(
                    crate::kernel::MachineIntegerType::UInt32,
                    crate::kernel::MachineBinaryOp::Divide,
                ),
                Int32Binary::UnsignedRemainder => O::Machine(
                    crate::kernel::MachineIntegerType::UInt32,
                    crate::kernel::MachineBinaryOp::Remainder,
                ),
                Int32Binary::BitwiseXor => O::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineBinaryOp::BitwiseXor,
                ),
                Int32Binary::Other(op) => op,
            };
            let term = op.build(
                crate::kernel::MachineTerm::constant(a as u32),
                crate::kernel::MachineTerm::constant(b as u32),
            );
            if let Some(value) = term.as_const() {
                let literal = self.intern_node(Node::Int32(MachineAtom::int32(
                    crate::kernel::MachineTerm::constant(value),
                )));
                pending.push((id, literal));
            }
        }
        // A conversion of a narrow constant, or a conversion into a narrow
        // format of a constant, is that constant converted: a node of the
        // destination's width. One lookup per firing.
        if let Application::Int32Unary(Int32Unary::Cast(source, destination), value) = signature
            && (source.format().bits() < 32 || destination.format().bits() < 32)
        {
            use crate::kernel::MachineTerm as T;
            let operand = if source.format().bits() < 32 {
                self.narrow_constants
                    .get(&value)
                    .map(|bits| T::narrow_constant(source, u128::from(*bits)))
            } else {
                self.int32_constants
                    .get(&value)
                    .map(|value| T::constant(*value as u32))
            };
            if let Some(operand) = operand {
                let converted = T::machine_integer_cast(source, destination, operand);
                if let Some(literal) = self.machine_literal_node(destination, &converted) {
                    pending.push((id, literal));
                }
            }
        } else if let Application::Int32Unary(op, value) = signature
            && let Some(value) = self.int32_constants.get(&value).copied()
        {
            use crate::kernel::MachineTerm as T;
            let value = T::constant(value as u32);
            let term = match op {
                Int32Unary::Not => unary_node!(Int32, BitwiseNot, Box::new(value)),
                Int32Unary::Cast(source, destination) => {
                    T::machine_integer_cast(source, destination, value)
                }
            };
            if let Some(value) = term.as_const() {
                let literal = self.intern_node(Node::Int32(MachineAtom::int32(T::constant(value))));
                pending.push((id, literal));
            }
        }
        if let Application::UInt64Binary(op, left, right) = signature
            && let (Some(a), Some(b)) = (
                self.uint64_constants.get(&left).copied(),
                self.uint64_constants.get(&right).copied(),
            )
        {
            let value = match op {
                UInt64Binary::Add => Some(a.wrapping_add(b)),
                UInt64Binary::Subtract => Some(a.wrapping_sub(b)),
                UInt64Binary::Multiply => Some(a.wrapping_mul(b)),
                UInt64Binary::Divide => a.checked_div(b),
                UInt64Binary::Remainder => a.checked_rem(b),
                UInt64Binary::And => Some(a & b),
                UInt64Binary::Or => Some(a | b),
                UInt64Binary::Xor => Some(a ^ b),
            };
            if let Some(value) = value {
                let literal = self.intern_node(Node::UInt64(MachineAtom::uint64(
                    crate::kernel::MachineTerm::uint64_constant(value),
                )));
                pending.push((id, literal));
            }
        }
        if let Some(other) = self.signatures.get(&signature) {
            if *other != id {
                pending.push((id, *other));
            }
        } else {
            self.signatures.insert(signature, id);
        }
        self.application_signatures.insert(id, signature);
        self.relate_machine_application(id);
    }

    fn close(&mut self, pending: Vec<(u64, u64)>) -> bool {
        self.close_with_affine_definition(pending, false)
    }

    fn close_with_affine_definition(
        &mut self,
        pending: Vec<(u64, u64)>,
        affine_definition: bool,
    ) -> bool {
        let last = pending.len().checked_sub(1);
        self.close_pending(PendingUnions(
            pending
                .into_iter()
                .enumerate()
                .map(|(index, (left, right))| {
                    (left, right, affine_definition && Some(index) == last)
                })
                .collect(),
        ))
    }

    fn close_pending(&mut self, mut pending: PendingUnions) -> bool {
        let mut changed = false;
        let was_closing = std::mem::replace(&mut self.closing, true);
        loop {
            pending.0.extend(
                self.pending_cast_unions
                    .drain(..)
                    .map(|(left, right)| (left, right, false)),
            );
            let Some((left, right, definitional)) = pending.0.pop() else {
                if !self.pending_machine_relations.is_empty() && !self.relating_machine_terms {
                    self.fire_machine_relation(&mut pending);
                    continue;
                }
                break;
            };
            crate::instrumentation::record_deterministic_work(1);
            let mut kept = self.root(left);
            let mut moved = self.root(right);
            if kept == moved {
                continue;
            }
            if self.weight(kept) < self.weight(moved) {
                std::mem::swap(&mut kept, &mut moved);
            }
            let learns_offset_zero = self
                .nodes
                .get(&Node::Constant(0))
                .is_some_and(|zero| self.root(*zero) == moved);
            let non_affine = (!definitional && !self.address_nodes.contains(&kept))
                || self.non_affine_classes.contains(&kept)
                || self.non_affine_classes.contains(&moved);
            if non_affine {
                self.mark_non_affine(kept);
                self.mark_non_affine(moved);
            }
            if let Some(witness) = self.pointer_value_witnesses.get(&moved).cloned() {
                self.pointer_value_witnesses.remove(&moved);
                self.retain_pointer_value_witness(kept, witness);
            }
            if let Some(value) = self.pointer_values.get(&moved).cloned() {
                self.pointer_values.remove(&moved);
                self.retain_pointer_value(kept, value);
            }
            if let Some(value) = self.extent_values.get(&moved).cloned() {
                self.extent_values.remove(&moved);
                let witness = self
                    .extent_values
                    .get(&kept)
                    .map_or(value.clone(), |previous| {
                        crate::kernel::pointer_designations::prefer_pointer(previous, &value)
                    });
                self.extent_values.insert(kept, witness);
            }
            self.merge_affine_applications(moved, kept);
            let weight = self.weight(kept) + self.weight(moved);
            self.merge_address_offsets(moved, kept, &mut pending);
            self.merge_wide_equation_endpoints(moved, kept);
            if let Some(moved_addresses) = self.addresses_by_offset.get(&moved).cloned() {
                let mut kept_addresses = self
                    .addresses_by_offset
                    .get(&kept)
                    .cloned()
                    .unwrap_or_default();
                for (block, address) in moved_addresses.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if !kept_addresses.contains_key(block) {
                        kept_addresses.insert(*block, *address);
                    }
                }
                self.addresses_by_offset.remove(&moved);
                self.addresses_by_offset.insert(kept, kept_addresses);
            }
            self.merge_storage_addresses(moved, kept);
            if let Some(pointer) = self.numeric_addresses.get(&moved).cloned() {
                self.numeric_addresses.remove(&moved);
                self.retain_numeric_address(kept, pointer);
            }
            self.merge_pointer_facts(moved, kept);
            if let Some(constructor) = self.algebraic_constructors.get(&moved).cloned() {
                crate::instrumentation::record_deterministic_work(1);
                self.algebraic_constructors.remove(&moved);
                if !self.algebraic_constructors.contains_key(&kept) {
                    self.algebraic_constructors.insert(kept, constructor);
                }
            }
            if let Some(application) = self.constructor_applications.get(&moved).copied() {
                self.constructor_applications.remove(&moved);
                match self.constructor_applications.get(&kept).copied() {
                    Some(existing) => {
                        self.join_constructor_applications(existing, application, &mut pending);
                    }
                    None => {
                        self.constructor_applications.insert(kept, application);
                    }
                }
            }
            self.merge_additive_addresses(moved, kept);
            self.merge_additive_offsets(moved, kept);
            self.merge_alignment_witnesses(moved, kept);
            if let Some((lower, upper)) = self.signed_int32_intervals.get(&moved).copied() {
                crate::instrumentation::record_deterministic_work(1);
                let (kept_lower, kept_upper) = self
                    .signed_int32_intervals
                    .get(&kept)
                    .copied()
                    .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
                self.signed_int32_intervals.remove(&moved);
                self.signed_int32_intervals
                    .insert(kept, (lower.max(kept_lower), upper.min(kept_upper)));
            }
            // Rule C1's links follow their classes.
            if let Some(moved_casts) = self.condition_casts.get(&moved).cloned() {
                self.condition_casts.remove(&moved);
                let mut kept_casts = self.condition_casts.get(&kept).cloned().unwrap_or_default();
                for cast in moved_casts.iter() {
                    kept_casts = kept_casts.with_value(*cast);
                }
                self.condition_casts.insert(kept, kept_casts);
            }
            if let Some(link) = self.bool_cast_links.get(&moved).copied() {
                self.bool_cast_links.remove(&moved);
                match self.bool_cast_links.get(&kept).copied() {
                    Some(kept_link) => self
                        .pending_cast_unions
                        .push((kept_link.condition, link.condition)),
                    None => {
                        self.bool_cast_links.insert(kept, link);
                    }
                }
            }
            if let Some(truth) = self.condition_truth.get(&moved).copied() {
                self.condition_truth.remove(&moved);
                self.retain_condition_truth(kept, truth);
            }
            self.parents.insert(moved, kept);
            self.history = Some(Arc::new(MergeHistory {
                depth: self.history.as_ref().map_or(1, |node| node.depth + 1),
                merge: TermClassMerge { moved, kept },
                parent: self.history.clone(),
            }));
            self.weights.remove(&moved);
            self.weights.insert(kept, weight);
            let kept_was_settled = self.int32_constants.contains_key(&kept);
            let moved_uses = self.uses.get(&moved).cloned().unwrap_or_default();
            let mut kept_uses = self.uses.get(&kept).cloned().unwrap_or_default();
            // Equality and congruence have already justified this union.
            // Distinct literal values in either width make the context empty;
            // retaining one folding representative must not erase that fact.
            if let (Some(left), Some(right)) = (
                self.int32_constants.get(&kept),
                self.int32_constants.get(&moved),
            ) {
                self.scalar_constant_conflict |= left != right;
                if left != right {
                    self.mark_scalar_conflict(kept);
                    let uses = self.constant_uses.get(&moved).cloned().unwrap_or_default();
                    for id in uses.iter() {
                        self.mark_scalar_conflict(*id);
                    }
                }
            }
            if let Some(value) = self.uint64_constants.get(&moved).copied() {
                if let Some(previous) = self.uint64_constants.get(&kept) {
                    self.scalar_constant_conflict |= *previous != value;
                    if *previous != value {
                        self.mark_scalar_conflict(kept);
                    }
                } else {
                    self.uint64_constants.insert(kept, value);
                    let uses = self.constant_uses.get(&kept).cloned().unwrap_or_default();
                    for id in uses.iter() {
                        self.reindex_application(*id, &mut pending);
                    }
                }
                self.uint64_constants.remove(&moved);
            }
            match (
                self.narrow_constants.get(&kept).copied(),
                self.narrow_constants.get(&moved).copied(),
            ) {
                (Some(left), Some(right)) if left != right => {
                    self.scalar_constant_conflict = true;
                    self.mark_scalar_conflict(kept);
                }
                (None, Some(value)) => {
                    self.narrow_constants.insert(kept, value);
                    let uses = self.constant_uses.get(&kept).cloned().unwrap_or_default();
                    for id in uses.iter() {
                        self.reindex_application(*id, &mut pending);
                    }
                }
                _ => {}
            }
            self.narrow_constants.remove(&moved);
            // A class learns a literal only once. Its existing applications
            // then need constant evaluation as well as the moved applications.
            if !self.int32_constants.contains_key(&kept)
                && let Some(value) = self.int32_constants.get(&moved).copied()
            {
                self.int32_constants.insert(kept, value);
                let literal_uses = self.constant_uses.get(&kept).cloned().unwrap_or_default();
                for id in literal_uses.iter() {
                    self.reindex_application(*id, &mut pending);
                }
            }
            self.int32_constants.remove(&moved);
            // Rule C1: a cast class that learned a constant decides its `Bool`.
            self.cast_value_truth(kept);
            self.merge_scalar_witnesses(moved, kept, kept_was_settled, &mut pending);
            if let Some(moved_literal_uses) = self.constant_uses.get(&moved).cloned() {
                self.constant_uses.remove(&moved);
                let mut kept_literal_uses =
                    self.constant_uses.get(&kept).cloned().unwrap_or_default();
                for id in moved_literal_uses.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    kept_literal_uses = kept_literal_uses.with_value(*id);
                }
                self.constant_uses.insert(kept, kept_literal_uses);
            }
            // A zero literal joining the heavier offset class changes its
            // value without changing that class's root. Revisit only its
            // existing addition parents, just as scalar literal propagation
            // revisits its selected constant uses.
            if learns_offset_zero {
                let additions = self.constant_uses.get(&kept).cloned().unwrap_or_default();
                for id in additions.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if matches!(self.applications.get(id), Some(Application::Add(..))) {
                        self.reindex_application(*id, &mut pending);
                    }
                }
            }
            self.merge_machine_relations(moved, kept);
            for id in moved_uses.iter() {
                crate::instrumentation::record_deterministic_work(1);
                kept_uses = kept_uses.with_value(*id);
                self.reindex_application(*id, &mut pending);
            }
            self.uses.remove(&moved);
            if !kept_uses.is_empty() {
                self.uses.insert(kept, kept_uses);
            }
            changed = true;
        }
        self.closing = was_closing;
        changed
    }
}

/// Separates a contract's name from its values in a function-contract group.
pub(super) const CONTRACT_VALUES_SEPARATOR: char = '\u{1f}';

/// The group a contract fact belongs to: the contract's name, then the
/// values it fixes for the contract's value parameters, so one group holds
/// the facts that call the same contract with the same values. A contract
/// with no value parameters is grouped by its name alone.
fn function_contract_group(name: &str, values: &[crate::kernel::Term]) -> String {
    if values.is_empty() {
        return name.to_string();
    }
    format!("{name}{CONTRACT_VALUES_SEPARATOR}{values:?}")
}

#[cfg(test)]
mod tests {
    use super::super::EqualityGraph;
    use super::*;
    use crate::kernel::{ConditionTerm, MachineTerm, Pointer, PureFactContext};

    fn var(id: u64) -> PointerOffsetTerm {
        PointerOffsetTerm::Variable(Variable(id))
    }
    fn equality(left: &PointerOffsetTerm, right: &PointerOffsetTerm) -> ConditionTerm {
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone())
    }

    fn add(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
        // Preserve nested applications rather than folding constants here.
        PointerOffsetTerm::Add(Box::new(left), Box::new(right))
    }

    #[test]
    fn affine_registration_retains_shared_machine_atoms() {
        use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let native = MachineTerm::add(
            MachineTerm::Variable(Variable(991301)),
            MachineTerm::Variable(Variable(991302)),
        );
        let root = KernelTermImport::default()
            .machine_arithmetic(format, &native)
            .unwrap();
        let mut affine = AffineOffset::constant(12);
        affine
            .add_atom(
                OffsetAtom::Int32(MachineAtom::from_operand(format, V::Shared(&root))),
                4,
            )
            .unwrap();
        let written = PointerOffsetTerm::add(
            PointerOffsetTerm::Constant(12),
            PointerOffsetTerm::scale_int32(native, 4),
        );
        let mut terms = TermClasses::default();
        let exports = KernelTermExport::machine_export_count();
        let shared = terms.intern_affine_offset(&affine).unwrap();
        let native = terms.intern(&written);
        assert_eq!(terms.root(shared), terms.root(native));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn addition_congruence_handles_both_operands_and_insertion_orders() {
        for equality_first in [false, true] {
            let mut graph = EqualityGraph::default();
            let (a, b, c, d) = (var(100), var(101), var(102), var(103));
            let (left, right) = (var(104), var(105));
            if equality_first {
                graph.add_offset_equality(&a, &b);
                graph.add_offset_equality(&c, &d);
            }
            graph.add_offset_equality(&add(a.clone(), c.clone()), &left);
            graph.add_offset_equality(&add(b.clone(), d.clone()), &right);
            if !equality_first {
                assert!(!graph.are_offsets_equal(&left, &right));
                graph.add_offset_equality(&a, &b);
                assert!(!graph.are_offsets_equal(&left, &right));
                graph.add_offset_equality(&c, &d);
            }
            // Query the aliases, not the addition trees: closure must already
            // have propagated the operand equalities into their parents.
            assert!(graph.are_offsets_equal(&left, &right));
        }
    }

    #[test]
    fn addition_congruence_propagates_nested_late_merges_and_is_branch_local() {
        let nested = |mut term| {
            for i in 0..64 {
                term = add(term, var(200 + i));
            }
            term
        };
        let (a, b, left, right) = (var(110), var(111), var(112), var(113));
        let mut parent = EqualityGraph::default();
        parent.add_offset_equality(&nested(a.clone()), &left);
        parent.add_offset_equality(&nested(b.clone()), &right);
        let sibling = parent.clone();
        let mut branch = parent.clone();
        branch.add_offset_equality(&a, &b);
        assert!(branch.are_offsets_equal(&left, &right));
        assert!(!parent.are_offsets_equal(&left, &right));
        assert!(!sibling.are_offsets_equal(&left, &right));
    }

    #[test]
    fn addition_congruence_does_not_cancel_or_equate_distinct_displacements() {
        let (a, b, c) = (var(120), var(121), var(122));
        let mut graph = EqualityGraph::default();
        graph.add_offset_equality(&add(a.clone(), c.clone()), &add(b.clone(), c.clone()));
        assert!(!graph.are_offsets_equal(&a, &b));
        graph.add_offset_equality(&a, &b);
        assert!(!graph.are_offsets_equal(
            &add(a, PointerOffsetTerm::Constant(1)),
            &add(b, PointerOffsetTerm::Constant(2)),
        ));
    }

    #[test]
    fn addition_congruence_closes_cycles_without_generating_terms() {
        let a = var(130);
        let b = add(a.clone(), var(131));
        let c = add(b.clone(), var(131));
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_offsets_equal(&a, &c));
        graph.add_offset_equality(&a, &b);
        assert!(graph.are_offsets_equal(&a, &c));
    }

    #[test]
    fn addition_congruence_matches_a_small_exhaustive_closure() {
        // Independent oracle for the term-class fragment: repeatedly scan
        // every pair of applications, relabeling a flat partition. The public
        // graph query additionally accepts affine equalities, so compare the
        // indexed term classes directly with this congruence-only oracle.
        let mut terms = vec![var(300), var(301), var(302)];
        let mut applications = Vec::new();
        for left in 0..3 {
            for right in 0..3 {
                applications.push((terms.len(), left, right));
                terms.push(add(terms[left].clone(), terms[right].clone()));
            }
        }
        for left in 3..12 {
            applications.push((terms.len(), left, 0));
            terms.push(add(terms[left].clone(), terms[0].clone()));
        }
        fn join(classes: &mut [usize], left: usize, right: usize) -> bool {
            let (left, right) = (classes[left], classes[right]);
            if left == right {
                return false;
            }
            for class in classes {
                if *class == right {
                    *class = left;
                }
            }
            true
        }
        for seed in 1..=4u64 {
            let mut graph = TermClasses::default();
            for term in &terms {
                assert!(graph.are_equal(term, term));
            }
            let mut classes = (0..terms.len()).collect::<Vec<_>>();
            let mut random = seed;
            for _ in 0..8 {
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let left = (random >> 32) as usize % terms.len();
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let right = (random >> 32) as usize % terms.len();
                graph.add_equality(&terms[left], &terms[right]);
                join(&mut classes, left, right);
                loop {
                    let mut changed = false;
                    for &(a, al, ar) in &applications {
                        for &(b, bl, br) in &applications {
                            if classes[al] == classes[bl] && classes[ar] == classes[br] {
                                changed |= join(&mut classes, a, b);
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                for (a, left) in terms.iter().enumerate() {
                    for (b, right) in terms.iter().enumerate() {
                        assert_eq!(
                            graph.are_equal(left, right),
                            classes[a] == classes[b],
                            "seed={seed}, a={a}, b={b}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn affine_completeness_follows_only_affected_address_dependencies() {
        let base = Pointer::symbolic(Variable(895_050));
        let other = Pointer::symbolic(Variable(895_051));
        let alias = Pointer::symbolic(Variable(895_052));
        let mut graph = EqualityGraph::default();
        graph.address_class(&Pointer {
            block: base.block.clone(),
            offset: add(var(895_053), var(895_054)),
        });
        graph.address_class(&other.offset_by_bytes(8));
        let sibling = graph.clone();
        graph.add_offset_equality(&var(895_053), &var(895_055));
        assert!(!graph.affine_addresses_complete(&base.block));
        assert!(graph.affine_addresses_complete(&other.block));
        assert!(sibling.affine_addresses_complete(&base.block));
        // A newly registered parent inherits the already-affected operand.
        let late = Pointer::symbolic(Variable(895_056));
        graph.address_class(&Pointer {
            block: late.block.clone(),
            offset: add(var(895_055), var(895_057)),
        });
        assert!(!graph.affine_addresses_complete(&late.block));
        graph.add_equality(&base, &alias);
        assert!(!graph.affine_addresses_complete(&alias.block));
        assert!(graph.affine_addresses_complete(&other.block));
    }

    #[test]
    fn offset_equality_is_transitive_symmetric_and_branch_local() {
        let (a, b, c) = (var(1), var(2), var(3));
        let mut parent = EqualityGraph::default();
        parent.add_offset_equality(&a, &b);
        let mut branch = parent.clone();
        branch.add_offset_equality(&b, &c);
        assert!(branch.are_offsets_equal(&c, &a));
        assert!(branch.are_offsets_equal(&a, &a));
        assert!(!parent.are_offsets_equal(&a, &c));
        let plus_one =
            |x| PointerOffsetTerm::Add(Box::new(x), Box::new(PointerOffsetTerm::Constant(1)));
        assert!(branch.are_offsets_equal(&plus_one(a), &plus_one(c)));
    }

    #[test]
    fn late_wide_constants_reconnect_offsets_without_using_low_words_or_wrapping() {
        let value = MachineTerm::Variable(Variable(895_080));
        let base = Pointer::symbolic(Variable(895_081));
        let scaled = |width, unsigned| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scaled_int64_node(value.clone(), width, unsigned),
        };
        for unsigned in [false, true] {
            for width in [1, 4, 8] {
                let pointer = scaled(width, unsigned);
                let mut graph = EqualityGraph::default();
                assert!(!graph.are_equal(&pointer, &base));
                let sibling = graph.clone();
                graph.add_uint64_equality(&value, &MachineTerm::uint64_constant(0));
                assert!(
                    graph.are_equal(&pointer, &base),
                    "late zero: {width}, {unsigned}"
                );
                assert!(!sibling.are_equal(&pointer, &base));
            }
        }
        let mut low_word_only = EqualityGraph::default();
        low_word_only.add_int32_equality(
            &MachineTerm::legacy_cast(
                crate::kernel::MachineCastSpelling::UInt32From64,
                Box::new(value.clone()),
            ),
            &MachineTerm::constant(0),
        );
        assert!(!low_word_only.are_equal(&scaled(1, true), &base));
        let mut high_word = EqualityGraph::default();
        high_word.add_uint64_equality(&value, &MachineTerm::uint64_constant(1u64 << 32));
        assert!(high_word.are_equal(
            &scaled(4, true),
            &Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Constant(4i64 << 32)
            }
        ));
        assert!(!high_word.are_equal(&scaled(4, true), &base));
        let mut overflow = EqualityGraph::default();
        overflow.add_uint64_equality(&value, &MachineTerm::uint64_constant(1u64 << 63));
        for unsigned in [false, true] {
            assert!(!overflow.are_equal(&scaled(2, unsigned), &base));
        }
    }

    #[test]
    fn offset_equality_preserves_width_signedness_and_state_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let scaled =
            |value, width, unsigned| PointerOffsetTerm::scaled_int64_node(value, width, unsigned);
        let value = MachineTerm::Variable(Variable(10));
        let signed = scaled(value.clone(), 4, false);
        let target = var(11);
        let mut graph = EqualityGraph::default();
        graph.add_offset_equality(&signed, &target);
        assert!(!graph.are_offsets_equal(&scaled(value.clone(), 8, false), &target));
        assert!(!graph.are_offsets_equal(&scaled(value, 4, true), &target));
        let before =
            crate::kernel::intern_memory(crate::kernel::Memory::new().with_block("offset", 8));
        let address = Pointer::symbolic(Variable(12));
        let after = crate::kernel::intern_memory(before.memory().clone().store(
            address.clone(),
            crate::kernel::ProgramValue::Int32(MachineTerm::constant(9)),
        ));
        let load = |memory: &crate::kernel::SharedMemory| {
            MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &address,
                crate::kernel::LoadKind::Int32,
                8,
                memory,
            ))
        };
        let old = scaled(load(&before), 4, false);
        let new = scaled(load(&after), 4, false);
        graph.add_offset_equality(&old, &target);
        assert!(!graph.are_offsets_equal(&new, &target));
        assert!(!graph.are_offsets_equal(&add(new, var(13)), &add(target, var(13))));
    }

    #[test]
    fn offset_context_restriction_preserves_only_retained_equalities() {
        let (a, b, c) = (var(20), var(21), var(22));
        let ab = equality(&a, &b);
        let bc = equality(&b, &c);
        let p = Pointer::symbolic(Variable(23));
        let q = Pointer::symbolic(Variable(24));
        let pq = ConditionTerm::pointer_equal(p.clone(), q.clone());
        let context = PureFactContext::new()
            .assume_condition(ab.clone(), true)
            .assume_condition(bc.clone(), true)
            .assume_condition(pq.clone(), true);
        assert!(context.equality_graph.are_offsets_equal(&a, &c));
        let translated_a = add(a.clone(), var(25));
        let translated_c = add(c.clone(), var(25));
        assert!(
            context
                .equality_graph
                .are_offsets_equal(&translated_a, &translated_c)
        );
        let restricted = context.restricted_to_facts(&[(ab, true)], &[]);
        assert!(!restricted.equality_graph.are_offsets_equal(&a, &c));
        assert!(restricted.equality_graph.are_offsets_equal(&a, &b));
        let reversed = context.clone().assume_condition(bc, false);
        assert!(reversed.is_inconsistent());
        assert!(reversed.equality_graph.are_offsets_equal(&a, &c));
        assert!(context.equality_graph.are_offsets_equal(&a, &c));
    }

    #[test]
    fn complete_pointer_identity_tracks_symbolic_extent_widths() {
        use crate::kernel::{PointerValue, ProgramType, SubobjectExtent};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(942_001));
        let width = MachineTerm::Variable(Variable(942_002));
        let bounded = |width| {
            PointerValue::new(pointer.clone(), ProgramType::Int32Pointer).with_extent(Some(
                SubobjectExtent {
                    start: pointer.clone(),
                    width,
                },
            ))
        };
        let dynamic = bounded(width.clone());
        let four = bounded(4u32.into());
        let eight = bounded(8u32.into());
        let mut classes = TermClasses::default();
        assert!(!classes.pointer_values_equal(&dynamic, &four));
        classes.add_int32_equality(&width, &MachineTerm::constant(4));
        assert!(classes.pointer_values_equal(&dynamic, &four));
        assert!(!classes.pointer_values_equal(&dynamic, &eight));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/equality_graph/terms/tests.rs");
    }
}
