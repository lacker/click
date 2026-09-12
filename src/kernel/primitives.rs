use super::api::{
    int16, int32, normalize_exact_memory_loads_in_pointer_offset, uint8, uint16, uint32,
};
use super::memory_provenance::{AtomicMemoryLoadEqualityEvidence, PointerOffsetEqualityEvidence};
use super::reasoning::{
    bitvector_terms_proven_equal_for_memory_resolution, bitvector_variable, collect_or_cases,
    instantiate_range_fold_step, memory_snapshots_proven_equal_at_pointer,
    pointers_proven_distinct_for_memory_resolution, pointers_proven_equal_for_memory_resolution,
    resource_context_has_read, signed_bitvector_constant, signed_i64_bitvector_constant,
};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;
use std::sync::{Arc, OnceLock};

mod contracts;
pub(crate) use contracts::{memory_range_byte_count, memory_range_byte_count_guards};
mod integer;
pub use integer::{
    AlgebraicIntegerMatchArm, IntegerComparisonOperator, IntegerRangeFoldIndex, IntegerTerm,
    SharedIntegerApplication, SharedIntegerRangeEndpoint, SharedIntegerTerm,
};
pub use integer::{MachineIntegerType, SharedMachineIntegerTerm};
mod derivations;
mod memory_state;
pub(crate) use memory_state::{
    clear_block_alignment_registry, register_block_alignment, registered_block_alignment,
    registered_block_alignment_charged,
};
mod resource_algebra;
mod term_operations;
pub(super) use derivations::*;
pub(crate) use memory_state::resource_context_has_symbolic_int32_range_read;
pub(super) use resource_algebra::*;

pub(super) const C_POINTER_BYTE_WIDTH: u32 = 8;

/// The allocator alignment guaranteed by the LP64 heap model.  Keep this
/// beside the pointer primitives so all proof routes use the same profile
/// contract rather than copying a second limit into a checker.
pub(crate) const HEAP_ALLOCATION_ALIGNMENT: u64 = 16;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable(pub u64);

/// A derived index of the free symbolic variables stored in one immutable
/// execution-environment version. Environment clones share the initialized
/// index; builder-style mutations replace it along with the changed semantic
/// storage.
#[derive(Clone, Default)]
pub(super) struct CExecutionEnvironmentVariableIndex {
    values: Arc<OnceLock<Arc<BTreeSet<Variable>>>>,
    #[cfg(test)]
    builds: Arc<std::sync::atomic::AtomicUsize>,
}

impl CExecutionEnvironmentVariableIndex {
    pub(super) fn get_or_init(
        &self,
        initialize: impl FnOnce() -> BTreeSet<Variable>,
    ) -> Arc<BTreeSet<Variable>> {
        self.values
            .get_or_init(|| {
                #[cfg(test)]
                self.builds
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Arc::new(initialize())
            })
            .clone()
    }

    #[cfg(test)]
    pub(super) fn build_count(&self) -> usize {
        self.builds.load(std::sync::atomic::Ordering::Relaxed)
    }

    #[cfg(test)]
    pub(super) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.values, &other.values)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    Condition,
    Bitvector32,
    Bitvector64,
    Integer,
    PointerOffset,
    CType,
    CInt32,
    CInt64,
    CPointer(CType),
    CValue,
    Sequence(Option<CType>),
    Algebraic(AlgebraicType),
    CMemory,
    CState,
    CStatementOutcome,
    CFunctionOutcome,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Bitvector32Term {
    Constant(u32),
    /// Signed 64-bit constants are kept in the same term arena as the
    /// original 32-bit terms so equality, substitution, and memory-load
    /// indexing continue to share one checked representation.
    Int64Constant(i64),
    /// Unsigned 64-bit constants retain all 64 bits; interpreting these as a
    /// signed value would lose the distinction above `i64::MAX`.
    UInt64Constant(u64),
    Variable(Variable),
    Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UnsignedDivide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UnsignedRemainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    ArithmeticShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    LogicalShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseNot(Box<Bitvector32Term>),
    If {
        condition: Box<ConditionTerm>,
        then_term: Box<Bitvector32Term>,
        else_term: Box<Bitvector32Term>,
    },
    RangeFold {
        start: Box<Bitvector32Term>,
        end: Box<Bitvector32Term>,
        initial: Box<Bitvector32Term>,
        accumulator: Variable,
        item: Variable,
        body: Box<Bitvector32Term>,
    },
    /// An opaque application retained across one-step unfolding of a total
    /// pure Click function at symbolic arguments.
    PureFunctionApplication {
        name: String,
        arguments: Vec<Bitvector32Term>,
    },
    /// A Click function application remains a logical term until a checked
    /// function-unfold step exposes its definition. Unlike the legacy
    /// bitvector-only application above, Click arguments retain their source
    /// sorts and state-indexed array references.
    ClickFunctionApplication {
        name: String,
        arguments: Vec<PureFunctionArgument>,
    },
    /// Exhaustive elimination of an algebraic value. Unknown scrutinees stay
    /// symbolic; a checked reduction selects an arm only after the scrutinee
    /// is known to be a constructor.
    AlgebraicMatch {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicBitvectorMatchArm>,
    },
    MemoryLoad(SharedCMemory, Box<Pointer>),
    /// The 64-bit integer representation of a non-null object pointer under
    /// the LP64 profile.  The term keeps the exact source pointer, so the
    /// integer carries provenance: a cast back recovers that pointer, and two
    /// addresses compare as their pointers do.  No arithmetic on the term
    /// is interpreted as address arithmetic; tag bits are handled by checked
    /// rewrites on top of this term.
    PointerAddress(Box<Pointer>),
    IntegerToMachine {
        value: SharedIntegerTerm,
        destination: MachineIntegerType,
    },
    Int64From32(Box<Bitvector32Term>),
    UInt64From32(Box<Bitvector32Term>),
    /// Unsigned narrowing modulo 2^32; the operand is a signed or unsigned
    /// 64-bit integer and the result is a 32-bit bitvector.
    UInt32From64(Box<Bitvector32Term>),
    Int64FromUInt32(Box<Bitvector32Term>),
    UInt64FromInt32(Box<Bitvector32Term>),
    UInt64FromInt64(Box<Bitvector32Term>),
    Int64Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64ArithmeticShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseNot(Box<Bitvector32Term>),
    UInt64Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64LogicalShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseNot(Box<Bitvector32Term>),
    Float32Negate(Box<Bitvector32Term>),
    Float32Binary {
        operator: CFloatBinaryOperator,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    },
    Float64Negate(Box<Bitvector32Term>),
    Float64Binary {
        operator: CFloatBinaryOperator,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PointerOffsetTerm {
    Constant(i64),
    Variable(Variable),
    Add(Box<PointerOffsetTerm>, Box<PointerOffsetTerm>),
    Int32Scaled {
        value: Box<Bitvector32Term>,
        byte_width: i64,
    },
    /// A pointer displacement formed from a signed or unsigned 64-bit
    /// element index.  The term arena intentionally remains shared with the
    /// existing 32-bit form, but its numeric interpretation must not be
    /// truncated to `i32` while forming an address.
    Int64Scaled {
        value: Box<Bitvector32Term>,
        byte_width: i64,
        unsigned: bool,
    },
}

impl PointerOffsetTerm {
    /// Every bitvector term nested in this offset, for traversals that must
    /// look through a pointer embedded in a term.
    pub(crate) fn scaled_values(&self) -> Vec<&Bitvector32Term> {
        let mut values = Vec::new();
        let mut pending = vec![self];
        while let Some(offset) = pending.pop() {
            match offset {
                Self::Constant(_) | Self::Variable(_) => {}
                Self::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Self::Int32Scaled { value, .. } | Self::Int64Scaled { value, .. } => {
                    values.push(value.as_ref());
                }
            }
        }
        values
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ConditionTerm {
    Constant(bool),
    Variable(Variable),
    /// Logical equality of immutable algebraic values, not a C comparison.
    AlgebraicEqual(Box<AlgebraicTerm>, Box<AlgebraicTerm>),
    Bitvector32SignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32Equal(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedAddOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedSubtractOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedMultiplyOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedDivideOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedShiftLeftOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64Equal(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedAddOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedSubtractOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedMultiplyOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedDivideOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedShiftLeftOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Float32(CFloatCondition),
    Float64(CFloatCondition),
    PointerOffsetEqual(Box<PointerOffsetTerm>, Box<PointerOffsetTerm>),
    PointerEqual(Box<Pointer>, Box<Pointer>),
    IntegerLessThan(SharedIntegerTerm, SharedIntegerTerm),
    IntegerLessEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerGreaterThan(SharedIntegerTerm, SharedIntegerTerm),
    IntegerGreaterEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerNotEqual(SharedIntegerTerm, SharedIntegerTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Pointer {
    pub block: PointerBlock,
    pub offset: PointerOffsetTerm,
}

/// A C pointer value carries both its raw address and the type through which
/// the address is being viewed.  `Pointer` remains the untyped address
/// identity used by memory, aliasing, and provenance; pointer casts retag the
/// value without changing that identity.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CPointerValue {
    pointer: Pointer,
    c_type: CType,
    pointee_volatile: bool,
    pointee_constant: bool,
}

impl CPointerValue {
    pub(crate) fn new(pointer: Pointer, c_type: CType) -> Self {
        assert!(
            c_type.is_pointer(),
            "C pointer values require a pointer type"
        );
        Self {
            pointer,
            c_type,
            pointee_volatile: false,
            pointee_constant: false,
        }
    }

    pub(crate) fn pointer(&self) -> &Pointer {
        &self.pointer
    }

    pub(crate) fn into_pointer(self) -> Pointer {
        self.pointer
    }

    pub(crate) fn c_type(&self) -> CType {
        self.c_type
    }

    pub(crate) fn pointee_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub(crate) fn pointee_constant(&self) -> bool {
        self.pointee_constant
    }

    pub(crate) fn with_type(self, c_type: CType) -> Self {
        Self {
            pointer: self.pointer,
            c_type,
            pointee_volatile: self.pointee_volatile,
            pointee_constant: self.pointee_constant,
        }
    }

    pub(crate) fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    pub(crate) fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub(crate) fn replace_pointer(&mut self, pointer: Pointer) {
        self.pointer = pointer;
    }

    pub(crate) fn is_null(&self) -> bool {
        self.pointer.block == PointerBlock::Concrete("null".to_string())
            && self.pointer.offset == PointerOffsetTerm::Constant(0)
    }
}

impl std::ops::Deref for CPointerValue {
    type Target = Pointer;

    fn deref(&self) -> &Self::Target {
        &self.pointer
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum PointerBlock {
    Concrete(String),
    /// A string literal occurrence. Distinct occurrences with identical
    /// bytes are intentionally not proven distinct: C permits an
    /// implementation to merge them. The occurrence identity still keeps
    /// one literal's pointer stable, and differing bytes prove that two
    /// occurrences cannot be the same object.
    StringLiteral {
        identity: String,
        bytes: Vec<u8>,
    },
    Function(String),
    FunctionSymbolic(Variable),
    ExternalArgument,
    Symbolic(Variable),
    /// A trusted allocation identity. Unlike a symbolic/opaque block, this is
    /// fresh and distinct from every other block identity.
    Heap(u64),
}

impl std::hash::Hash for PointerBlock {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Keep the hash domain of the pre-string-literal variants stable.
        // Pointer hashes feed deterministic load-variable identities, so
        // inserting a new enum variant must not renumber existing blocks.
        match self {
            Self::Concrete(name) => {
                0u64.hash(state);
                name.hash(state);
            }
            Self::Function(name) => {
                1u64.hash(state);
                name.hash(state);
            }
            Self::FunctionSymbolic(variable) => {
                2u64.hash(state);
                variable.hash(state);
            }
            Self::ExternalArgument => 3u64.hash(state),
            Self::Symbolic(variable) => {
                4u64.hash(state);
                variable.hash(state);
            }
            Self::Heap(identity) => {
                5u64.hash(state);
                identity.hash(state);
            }
            Self::StringLiteral { identity, bytes } => {
                6u64.hash(state);
                identity.hash(state);
                bytes.hash(state);
            }
        }
    }
}

impl PointerBlock {
    pub(crate) fn is_function(&self) -> bool {
        matches!(self, Self::Function(_) | Self::FunctionSymbolic(_))
    }

    pub(crate) fn starts_with(&self, prefix: &str) -> bool {
        match self {
            Self::Concrete(name) => name.starts_with(prefix),
            Self::StringLiteral { .. } => prefix == "string:",
            _ => false,
        }
    }

    pub(crate) fn strip_prefix<'a>(&'a self, prefix: &str) -> Option<&'a str> {
        match self {
            Self::Concrete(name) => name.strip_prefix(prefix),
            Self::StringLiteral { .. }
            | Self::Function(_)
            | Self::FunctionSymbolic(_)
            | Self::ExternalArgument
            | Self::Symbolic(_)
            | Self::Heap(_) => None,
        }
    }
}

impl From<String> for PointerBlock {
    fn from(name: String) -> Self {
        Self::Concrete(name)
    }
}

impl From<&str> for PointerBlock {
    fn from(name: &str) -> Self {
        Self::Concrete(name.to_string())
    }
}

impl std::fmt::Display for PointerBlock {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Concrete(name) => formatter.write_str(name),
            Self::StringLiteral { identity, .. } => write!(formatter, "string:{identity}"),
            Self::Function(name) => write!(formatter, "function:{name}"),
            Self::FunctionSymbolic(variable) => {
                write!(formatter, "symbolic-function-pointer:{}", variable.0)
            }
            Self::ExternalArgument => formatter.write_str("arg-memory"),
            Self::Symbolic(variable) => write!(formatter, "symbolic-pointer:{}", variable.0),
            Self::Heap(identity) => write!(formatter, "heap-allocation:{identity}"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CValue {
    Void,
    /// C `_Bool` values are represented by a 32-bit term whose value is
    /// always normalized to zero or one.  The storage width remains the
    /// ABI-defined one byte width exposed by `CType::Bool`.
    Bool(Bitvector32Term),
    Int16(Bitvector32Term),
    Int32(Bitvector32Term),
    UInt8(Bitvector32Term),
    UInt16(Bitvector32Term),
    UInt32(Bitvector32Term),
    Int64(Bitvector32Term),
    UInt64(Bitvector32Term),
    /// IEEE-754 binary32 payload represented in the shared checked term arena.
    Float32(Bitvector32Term),
    /// IEEE-754 binary64 payload represented in the shared checked term arena.
    Float64(Bitvector32Term),
    Pointer(CPointerValue),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CType {
    Void,
    Bool,
    /// An opaque object pointer with provenance but no modeled pointee type.
    /// It is valid for identity-preserving casts and comparisons, but not for
    /// dereference, indexing, or pointer arithmetic.
    VoidPointer,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int64,
    UInt64,
    Float32,
    Float64,
    Int16Pointer,
    UInt16Pointer,
    Int32Pointer,
    UInt8Pointer,
    UInt32Pointer,
    Int64Pointer,
    UInt64Pointer,
    Float32Pointer,
    Float64Pointer,
    Int16PointerPointer,
    UInt16PointerPointer,
    Int32PointerPointer,
    UInt8PointerPointer,
    UInt32PointerPointer,
    Int64PointerPointer,
    UInt64PointerPointer,
    Float32PointerPointer,
    Float64PointerPointer,
    FunctionPointer(CallbackSignature),
    Int32Array(u32),
    UInt8Array(u32),
    Int16Array(u32),
    UInt16Array(u32),
    UInt32Array(u32),
    Int64Array(u32),
    UInt64Array(u32),
    Float32Array(u32),
    Float64Array(u32),
}

/// Exact packed callback type identity. Byte alignment keeps the common C type
/// enum compact; using a u128 payload would enlarge every execution frame.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct CallbackSignature([u8; 10]);

impl CallbackSignature {
    pub const UNSPECIFIED: Self = Self([0; 10]);

    pub(crate) fn from_encoded(encoded: u128) -> Self {
        assert!(
            encoded < (1u128 << 80),
            "callback signature capacity exceeded"
        );
        Self(encoded.to_le_bytes()[..10].try_into().unwrap())
    }
}

impl std::fmt::Display for CallbackSignature {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut bytes = [0; 16];
        bytes[..10].copy_from_slice(&self.0);
        std::fmt::Display::fmt(&u128::from_le_bytes(bytes), formatter)
    }
}

impl std::fmt::Debug for CallbackSignature {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, formatter)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLValue {
    pub(super) storage: CLValueStorage,
    pub(super) value_type: CType,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLValueStorage {
    Local { name: String },
    Memory { pointer: Pointer },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpression {
    Value(CValue),
    Variable(String),
    FunctionAddress(String),
    Cast {
        expression: Box<CExpression>,
        target_type: CType,
        /// Whether the cast result points at a volatile pointer-valued cell.
        /// This carries the C qualifier in `T * volatile *` into a following
        /// dereference without confusing it with volatile `T` storage.
        pointee_volatile: bool,
        /// Whether the cast result points at const-qualified storage. Source
        /// pointee constness is retained independently when the cast is
        /// evaluated.
        pointee_constant: bool,
    },
    Conditional {
        condition: Box<CExpression>,
        then_branch: Box<CExpression>,
        else_branch: Box<CExpression>,
    },
    FloatNegate(Box<CExpression>),
    FloatClassification {
        expression: Box<CExpression>,
        classification: CFloatClassification,
    },
    AddressOf(Box<CExpression>),
    PointerOffsetBytes {
        pointer: Box<CExpression>,
        bytes: u32,
    },
    LessThan(Box<CExpression>, Box<CExpression>),
    LessEqual(Box<CExpression>, Box<CExpression>),
    GreaterThan(Box<CExpression>, Box<CExpression>),
    GreaterEqual(Box<CExpression>, Box<CExpression>),
    Equal(Box<CExpression>, Box<CExpression>),
    NotEqual(Box<CExpression>, Box<CExpression>),
    Not(Box<CExpression>),
    And(Box<CExpression>, Box<CExpression>),
    Or(Box<CExpression>, Box<CExpression>),
    Add(Box<CExpression>, Box<CExpression>),
    Subtract(Box<CExpression>, Box<CExpression>),
    Multiply(Box<CExpression>, Box<CExpression>),
    Divide(Box<CExpression>, Box<CExpression>),
    Remainder(Box<CExpression>, Box<CExpression>),
    ShiftLeft(Box<CExpression>, Box<CExpression>),
    ShiftRight(Box<CExpression>, Box<CExpression>),
    BitwiseAnd(Box<CExpression>, Box<CExpression>),
    BitwiseOr(Box<CExpression>, Box<CExpression>),
    BitwiseXor(Box<CExpression>, Box<CExpression>),
    BitwiseNot(Box<CExpression>),
    Load(Box<CExpression>),
    TypedLoad {
        pointer: Box<CExpression>,
        value_type: CType,
        /// A sequential kernel access primitive forces one observable access
        /// even when the source lvalue itself was not declared volatile.
        volatile: bool,
    },
    Index(Box<CExpression>, Box<CExpression>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CComparisonOperator {
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFloatBinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFloatClassification {
    Finite,
    Infinite,
    Zero,
    Subnormal,
    Nan,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFloatCondition {
    Comparison {
        operator: CComparisonOperator,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    },
    Classification {
        classification: CFloatClassification,
        value: Box<Bitvector32Term>,
    },
}

impl CFloatCondition {
    pub(crate) fn for_each_bitvector_term(&self, mut visit: impl FnMut(&Bitvector32Term)) {
        match self {
            Self::Comparison { left, right, .. } => {
                visit(left);
                visit(right);
            }
            Self::Classification { value, .. } => visit(value),
        }
    }

    pub(crate) fn map_bitvector_terms(
        &self,
        mut map: impl FnMut(&Bitvector32Term) -> Bitvector32Term,
    ) -> Self {
        match self {
            Self::Comparison {
                operator,
                left,
                right,
            } => Self::Comparison {
                operator: *operator,
                left: Box::new(map(left)),
                right: Box::new(map(right)),
            },
            Self::Classification {
                classification,
                value,
            } => Self::Classification {
                classification: *classification,
                value: Box::new(map(value)),
            },
        }
    }

    pub(crate) fn try_map_bitvector_terms(
        &self,
        mut map: impl FnMut(&Bitvector32Term) -> Option<Bitvector32Term>,
    ) -> Option<Self> {
        Some(match self {
            Self::Comparison {
                operator,
                left,
                right,
            } => Self::Comparison {
                operator: *operator,
                left: Box::new(map(left)?),
                right: Box::new(map(right)?),
            },
            Self::Classification {
                classification,
                value,
            } => Self::Classification {
                classification: *classification,
                value: Box::new(map(value)?),
            },
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUpdateOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecMemory {
    Current,
    FunctionEntry,
    LoopEntry,
    Fixed(CMemory),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecExpression {
    Value(CValue),
    /// Convert a mathematical Integer expression back to a machine integer.
    /// The initial kernel stage accepts only exact constant values; symbolic
    /// range-checked conversion is added once its ordinary proof obligations
    /// have a representation in the surrounding spec path.
    IntegerToMachine {
        value: Box<SpecIntegerExpression>,
        destination: MachineIntegerType,
    },
    ResourceField {
        projection: ResourceFieldProjection,
        c_type: CType,
    },
    AlgebraicMatch {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecAlgebraicMatchArm>,
    },
    CExpression(CExpression),
    CountedResourceCount {
        name: String,
        arguments: Vec<Option<SpecExpression>>,
    },
    Add(Box<SpecExpression>, Box<SpecExpression>),
    Subtract(Box<SpecExpression>, Box<SpecExpression>),
    Multiply(Box<SpecExpression>, Box<SpecExpression>),
    Divide(Box<SpecExpression>, Box<SpecExpression>),
    Remainder(Box<SpecExpression>, Box<SpecExpression>),
    ShiftLeft(Box<SpecExpression>, Box<SpecExpression>),
    ShiftRight(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseAnd(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseOr(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseXor(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseNot(Box<SpecExpression>),
    Cast(Box<SpecExpression>, CType),
    If {
        condition: Box<SpecProposition>,
        then_branch: Box<SpecExpression>,
        else_branch: Box<SpecExpression>,
    },
    RangeFold {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
        initial: Box<SpecExpression>,
        accumulator: String,
        item: String,
        body: Box<SpecExpression>,
    },
    Let {
        name: String,
        value: Box<SpecExpression>,
        body: Box<SpecExpression>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
        result_type: CType,
    },
    LoopEntrySnapshot(Box<SpecExpression>),
    PointerOffset {
        pointer: Box<SpecExpression>,
        elements: Box<SpecExpression>,
        byte_width: u32,
    },
    MemoryLoad {
        memory: SpecMemory,
        pointer: Box<SpecExpression>,
        value_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicExpression {
    pub algebraic_type: AlgebraicType,
    pub node: SpecAlgebraicExpressionNode,
}

/// A specification-side mathematical integer expression.
///
/// This stays separate from [`SpecExpression`], whose scalar nodes carry C
/// values and therefore have machine-width semantics. Surface lowering
/// resolves names to kernel variables before constructing this form; there is
/// no lookup in `CState.locals` and no C representation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecIntegerExpression {
    ResourceField(ResourceFieldProjection),
    /// A pure mathematical value. Shared children preserve specification
    /// abbreviations without copying their expanded expression trees.
    Term(IntegerTerm),
    /// An opaque pure function returning a mathematical Integer. Arguments
    /// are evaluated for facts and definedness, while the call remains a
    /// symbolic application until an explicit unfold step.
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
    },
    AlgebraicMatch {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecIntegerMatchArm>,
    },
    FromMachine(Box<SpecExpression>),
    Negate(Box<Self>),
    Add(Box<Self>, Box<Self>),
    Subtract(Box<Self>, Box<Self>),
    Multiply(Box<Self>, Box<Self>),
    /// A symbolic fold over either machine Int32 or mathematical Integer
    /// endpoints.  The kernel keeps this opaque; bounded expansion belongs
    /// to explicit fold reasoning, so evaluating this node never unrolls a
    /// range in proportion to its endpoint values.
    RangeFold {
        index: SpecIntegerRangeFoldIndex,
        initial: Box<Self>,
        accumulator: Variable,
        item: Variable,
        body: Box<Self>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecIntegerRangeFoldIndex {
    Int32 {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
    },
    Integer {
        start: Box<SpecIntegerExpression>,
        end: Box<SpecIntegerExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecAlgebraicExpressionNode {
    Variable(Variable),
    Binding(String),
    ResourceField(ResourceFieldProjection),
    Constructor {
        variant: String,
        fields: Vec<SpecAlgebraicValue>,
    },
    Match {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecAlgebraicResultMatchArm>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceFieldProjection {
    pub identity: Variable,
    pub children: Vec<String>,
    pub field_index: usize,
    /// Select the explicit entry state supplied to spec evaluation. There is
    /// no fallback to the current state when that snapshot is unavailable.
    pub at_entry: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPureFunctionArgument {
    Value(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
    ArrayRef {
        memory: SpecMemory,
        pointer: SpecExpression,
        element_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecAlgebraicValue {
    C(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    pub body: SpecExpression,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicResultMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    pub body: Box<SpecAlgebraicExpression>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecIntegerMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    /// Kernel identities used by Integer binders in the lowered arm body.
    /// C and algebraic binders are represented by their typed environments.
    pub binding_variables: Vec<Option<Variable>>,
    pub body: Box<SpecIntegerExpression>,
}

/// A fully resolved application of a Click algebraic datatype. Keeping the
/// instantiated constructor schema in the kernel term lets the kernel check
/// constructor formation and exhaustive elimination without trusting names
/// supplied by surface lowering.
#[derive(Clone, Debug)]
pub struct AlgebraicType {
    pub rigid: bool,
    pub name: String,
    pub arguments: Vec<AlgebraicValueType>,
    pub variants: std::sync::Arc<[AlgebraicVariantType]>,
    pub schemas: std::sync::Arc<AlgebraicSchemas>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicValueType {
    Parameter(String),
    C(CType),
    Integer,
    Algebraic {
        name: String,
        arguments: Vec<AlgebraicValueType>,
    },
}

/// A resource field has a logical type, never a C storage location.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFieldType {
    Integer,
    C(CType),
    Algebraic(AlgebraicType),
}

/// Checked declaration metadata. This does not create an owned instance or
/// authorize a memory access; `ResourceInstance` carries identity and state.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceFieldSchema {
    fields: std::sync::Arc<[(String, ResourceFieldType)]>,
}

impl ResourceFieldSchema {
    pub fn new(fields: Vec<(String, ResourceFieldType)>) -> Option<Self> {
        let mut names = BTreeSet::new();
        for (name, ty) in &fields {
            if name.is_empty() || !names.insert(name) {
                return None;
            }
            let valid = match ty {
                ResourceFieldType::C(ty) => !matches!(
                    ty,
                    CType::Void
                        | CType::FunctionPointer(_)
                        | CType::Int16Array(_)
                        | CType::Int32Array(_)
                        | CType::UInt8Array(_)
                        | CType::UInt16Array(_)
                        | CType::UInt32Array(_)
                        | CType::Int64Array(_)
                        | CType::UInt64Array(_)
                        | CType::Float32Array(_)
                        | CType::Float64Array(_)
                ),
                ResourceFieldType::Integer => true,
                ResourceFieldType::Algebraic(ty) => ty.has_consistent_root_schema(),
            };
            if !valid {
                return None;
            }
        }
        Some(Self {
            fields: fields.into(),
        })
    }

    pub fn fields(&self) -> &[(String, ResourceFieldType)] {
        &self.fields
    }

    pub fn is_countable(&self) -> bool {
        self.fields.is_empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicVariantType {
    pub name: String,
    pub fields: Vec<AlgebraicValueType>,
}

/// The finite nominal schema graph shared by every term of one resolved
/// algebraic type family. Groundedness is computed once when the graph is
/// formed so checking each constructor or variable does not rescan schemas
/// unrelated to that term.
#[derive(Debug)]
pub struct AlgebraicSchemas {
    variants:
        std::collections::BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>,
    grounded: std::collections::BTreeSet<AlgebraicValueType>,
}

impl AlgebraicSchemas {
    pub(crate) fn new(
        variants: std::collections::BTreeMap<
            AlgebraicValueType,
            std::sync::Arc<[AlgebraicVariantType]>,
        >,
    ) -> Self {
        let mut grounded = std::collections::BTreeSet::new();
        loop {
            let before = grounded.len();
            for (value_type, constructors) in &variants {
                if constructors.iter().any(|constructor| {
                    constructor.fields.iter().all(|field| match field {
                        AlgebraicValueType::C(_)
                        | AlgebraicValueType::Integer
                        | AlgebraicValueType::Parameter(_) => true,
                        AlgebraicValueType::Algebraic { .. } => grounded.contains(field),
                    })
                }) {
                    grounded.insert(value_type.clone());
                }
            }
            if grounded.len() == before {
                break;
            }
        }
        Self { variants, grounded }
    }

    pub(crate) fn get(
        &self,
        value_type: &AlgebraicValueType,
    ) -> Option<&std::sync::Arc<[AlgebraicVariantType]>> {
        self.variants.get(value_type)
    }

    #[cfg(test)]
    pub(crate) fn definitions(
        &self,
    ) -> &std::collections::BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>
    {
        &self.variants
    }

    fn is_grounded(&self, value_type: &AlgebraicValueType) -> bool {
        self.grounded.contains(value_type)
    }
}

/// A logical algebraic value. An arbitrary Click binder is one typed
/// variable; it is not eagerly expanded into a tag and fields for every
/// possible constructor.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicTerm {
    pub algebraic_type: AlgebraicType,
    pub node: AlgebraicTermNode,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicTermNode {
    Variable(Variable),
    Constructor {
        variant: String,
        fields: Vec<AlgebraicValue>,
    },
    Match {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicResultMatchArm>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<PureFunctionArgument>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PureFunctionArgument {
    Value(CValue),
    Integer(SharedIntegerTerm),
    Algebraic(AlgebraicTerm),
    ArrayRef {
        memory: CMemory,
        pointer: CValue,
        element_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicValue {
    C(CValue),
    Integer(IntegerTerm),
    Algebraic(AlgebraicTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicBitvectorMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: Bitvector32Term,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicResultMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: AlgebraicTerm,
}

impl AlgebraicTerm {
    /// Visit scalar payload roots without expanding datatype schemas or copying
    /// terms. Callers decide how far to traverse each scalar expression.
    pub(crate) fn for_each_bitvector_term(&self, mut visit: impl FnMut(&Bitvector32Term)) {
        enum Node<'a> {
            Algebraic(&'a AlgebraicTerm),
            Value(&'a CValue),
            Offset(&'a PointerOffsetTerm),
        }
        let mut pending = vec![Node::Algebraic(self)];
        while let Some(node) = pending.pop() {
            match node {
                Node::Algebraic(term) => match &term.node {
                    AlgebraicTermNode::Variable(_) => {}
                    AlgebraicTermNode::Constructor { fields, .. } => {
                        for field in fields {
                            match field {
                                AlgebraicValue::C(v) => pending.push(Node::Value(v)),
                                AlgebraicValue::Integer(_) => {}
                                AlgebraicValue::Algebraic(v) => pending.push(Node::Algebraic(v)),
                            }
                        }
                    }
                    AlgebraicTermNode::Match { scrutinee, arms } => {
                        pending.push(Node::Algebraic(scrutinee));
                        for arm in arms {
                            pending.push(Node::Algebraic(&arm.body));
                            for binding in &arm.bindings {
                                match binding {
                                    AlgebraicValue::C(v) => pending.push(Node::Value(v)),
                                    AlgebraicValue::Integer(_) => {}
                                    AlgebraicValue::Algebraic(v) => {
                                        pending.push(Node::Algebraic(v))
                                    }
                                }
                            }
                        }
                    }
                    AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
                        for argument in arguments {
                            pending.push(match argument {
                                PureFunctionArgument::Value(v)
                                | PureFunctionArgument::ArrayRef { pointer: v, .. } => {
                                    Node::Value(v)
                                }
                                PureFunctionArgument::Algebraic(v) => Node::Algebraic(v),
                                PureFunctionArgument::Integer(_) => continue,
                            });
                        }
                    }
                },
                Node::Value(value) => match value {
                    CValue::Void => {}
                    CValue::Bool(v) => visit(v),
                    CValue::Pointer(v) => pending.push(Node::Offset(&v.pointer().offset)),
                    CValue::Int16(v)
                    | CValue::UInt16(v)
                    | CValue::UInt8(v)
                    | CValue::Int32(v)
                    | CValue::UInt32(v)
                    | CValue::Int64(v)
                    | CValue::UInt64(v)
                    | CValue::Float32(v)
                    | CValue::Float64(v) => visit(v),
                },
                Node::Offset(offset) => match offset {
                    PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
                    PointerOffsetTerm::Add(a, b) => {
                        pending.push(Node::Offset(a));
                        pending.push(Node::Offset(b));
                    }
                    PointerOffsetTerm::Int32Scaled { value, .. }
                    | PointerOffsetTerm::Int64Scaled { value, .. } => visit(value),
                },
            }
        }
    }

    /// Returns a constructor's fields only when the constructor is formed
    /// against this term's resolved datatype schema. Logical variables are
    /// well formed but have no constructor fields.
    pub(in crate::kernel) fn checked_constructor_fields(&self) -> Option<&[AlgebraicValue]> {
        if !self.algebraic_type.has_consistent_root_schema() {
            return None;
        }
        let AlgebraicTermNode::Constructor { variant, fields } = &self.node else {
            return None;
        };
        let schema = self
            .algebraic_type
            .variants
            .iter()
            .find(|schema| schema.name == *variant)?;
        (schema.fields.len() == fields.len()
            && schema.fields.iter().zip(fields).all(|(expected, field)| {
                field.is_well_formed_for(expected, &self.algebraic_type.schemas)
            }))
        .then_some(fields)
    }

    pub(in crate::kernel) fn is_well_formed(&self) -> bool {
        if !self.algebraic_type.has_consistent_root_schema() {
            return false;
        }
        match &self.node {
            AlgebraicTermNode::Variable(_) => true,
            AlgebraicTermNode::Constructor { .. } => self.checked_constructor_fields().is_some(),
            AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
                arguments.iter().all(PureFunctionArgument::is_well_formed)
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                !scrutinee.algebraic_type.rigid
                    && scrutinee.is_well_formed()
                    && arms.len() == scrutinee.algebraic_type.variants.len()
                    && scrutinee.algebraic_type.variants.iter().all(|variant| {
                        arms.iter()
                            .filter(|arm| arm.variant == variant.name)
                            .count()
                            == 1
                            && arms
                                .iter()
                                .find(|arm| arm.variant == variant.name)
                                .is_some_and(|arm| {
                                    arm.bindings.len() == variant.fields.len()
                                        && arm.bindings.iter().zip(&variant.fields).all(
                                            |(binding, expected)| {
                                                binding.is_well_formed_for(
                                                    expected,
                                                    &scrutinee.algebraic_type.schemas,
                                                )
                                            },
                                        )
                                        && arm.body.algebraic_type == self.algebraic_type
                                        && arm.body.is_well_formed()
                                })
                    })
            }
        }
    }
}

impl AlgebraicType {
    pub(crate) fn parameter(name: String) -> Self {
        Self {
            rigid: true,
            name,
            arguments: Vec::new(),
            variants: Vec::new().into(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(Default::default())),
        }
    }

    pub(crate) fn value_type(&self) -> AlgebraicValueType {
        if self.rigid {
            return AlgebraicValueType::Parameter(self.name.clone());
        }
        AlgebraicValueType::Algebraic {
            name: self.name.clone(),
            arguments: self.arguments.clone(),
        }
    }

    pub(in crate::kernel) fn resolve_nested_type(
        &self,
        value_type: &AlgebraicValueType,
    ) -> Option<Self> {
        if let AlgebraicValueType::Parameter(name) = value_type {
            return Some(Self::parameter(name.clone()));
        }
        let AlgebraicValueType::Algebraic { name, arguments } = value_type else {
            return None;
        };
        Some(Self {
            rigid: false,
            name: name.clone(),
            arguments: arguments.clone(),
            variants: self.schemas.get(value_type)?.clone(),
            schemas: self.schemas.clone(),
        })
    }

    pub(in crate::kernel) fn has_consistent_root_schema(&self) -> bool {
        if self.rigid {
            return self.arguments.is_empty() && self.variants.is_empty();
        }
        let value_type = self.value_type();
        self.schemas
            .get(&value_type)
            .is_some_and(|variants| variants == &self.variants)
            && self.schemas.is_grounded(&value_type)
    }
}

impl PartialEq for AlgebraicType {
    fn eq(&self, other: &Self) -> bool {
        self.rigid == other.rigid
            && self.name == other.name
            && self.arguments == other.arguments
            && self.variants == other.variants
    }
}

impl Eq for AlgebraicType {}

impl std::hash::Hash for AlgebraicType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.rigid.hash(state);
        self.name.hash(state);
        self.arguments.hash(state);
        self.variants.hash(state);
    }
}

impl PartialOrd for AlgebraicType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlgebraicType {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.rigid, &self.name, &self.arguments, &self.variants).cmp(&(
            other.rigid,
            &other.name,
            &other.arguments,
            &other.variants,
        ))
    }
}

impl From<CValue> for AlgebraicValue {
    fn from(value: CValue) -> Self {
        Self::C(value)
    }
}

impl AlgebraicValue {
    pub fn as_c_value(&self) -> Option<&CValue> {
        match self {
            Self::C(value) => Some(value),
            Self::Integer(_) => None,
            Self::Algebraic(_) => None,
        }
    }

    pub(in crate::kernel) fn value_type(&self) -> AlgebraicValueType {
        match self {
            Self::C(value) => AlgebraicValueType::C(value.c_type()),
            Self::Integer(_) => AlgebraicValueType::Integer,
            Self::Algebraic(value) => value.algebraic_type.value_type(),
        }
    }

    fn is_well_formed_for(
        &self,
        expected: &AlgebraicValueType,
        schemas: &AlgebraicSchemas,
    ) -> bool {
        if &self.value_type() != expected {
            return false;
        }
        match self {
            Self::C(_) => true,
            Self::Integer(_) => true,
            Self::Algebraic(value) => {
                (matches!(expected, AlgebraicValueType::Parameter(_))
                    || schemas
                        .get(expected)
                        .is_some_and(|variants| variants == &value.algebraic_type.variants))
                    && value.is_well_formed()
            }
        }
    }
}

impl PureFunctionArgument {
    fn is_well_formed(&self) -> bool {
        match self {
            Self::Value(_) => true,
            Self::Integer(_) => true,
            Self::Algebraic(term) => term.is_well_formed(),
            Self::ArrayRef {
                pointer,
                element_type,
                ..
            } => pointer.c_type().is_pointer() && *element_type != CType::Void,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecSequenceExpression {
    Literal(Vec<SpecExpression>),
    Concat(Box<SpecSequenceExpression>, Box<SpecSequenceExpression>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPredicateArgument {
    Value(SpecExpression),
    ArrayRef {
        memory: SpecMemory,
        pointer: SpecExpression,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecProposition {
    IntegerComparison {
        left: SpecIntegerExpression,
        operator: IntegerComparisonOperator,
        right: SpecIntegerExpression,
    },
    AlgebraicComparison {
        left: SpecAlgebraicExpression,
        equal: bool,
        right: SpecAlgebraicExpression,
    },
    SequenceMembership {
        element: SpecExpression,
        sequence: SpecSequenceExpression,
    },
    SequenceComparison {
        left: SpecSequenceExpression,
        equal: bool,
        right: SpecSequenceExpression,
    },
    Comparison {
        left: SpecExpression,
        operator: CComparisonOperator,
        right: SpecExpression,
    },
    FloatClassification {
        expression: SpecExpression,
        classification: CFloatClassification,
    },
    And(Box<SpecProposition>, Box<SpecProposition>),
    Or(Box<SpecProposition>, Box<SpecProposition>),
    Not(Box<SpecProposition>),
    Implies(Box<SpecProposition>, Box<SpecProposition>),
    ForAllInt32 {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ForAllInteger {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ForAllPointer {
        name: String,
        variable: Variable,
        c_type: CType,
        body: Box<SpecProposition>,
    },
    ExistsInt32 {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsInteger {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsPointer {
        name: String,
        variable: Variable,
        c_type: CType,
        body: Box<SpecProposition>,
    },
    Predicate {
        name: String,
        arguments: Vec<SpecPredicateArgument>,
    },
    ResourceSeparate {
        left: SpecResource,
        right: SpecResource,
    },
    ResourceContains {
        parent: SpecResource,
        child: SpecResource,
    },
    MemoryLoadable {
        memory: SpecMemory,
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
        element_width: u32,
    },
    Defined(SpecExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SequenceTerm {
    pub element_type: Option<CType>,
    pub node: std::sync::Arc<SequenceTermNode>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SequenceTermNode {
    Literal(std::sync::Arc<[CValue]>),
    Concat(SequenceTerm, SequenceTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecResource {
    Memory {
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
        element_width: u32,
    },
    Composite {
        name: String,
        arguments: Vec<SpecExpression>,
    },
    Token {
        name: String,
        arguments: Vec<SpecExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CSwitchCase {
    /// `None` is the default case; integer values are represented in the
    /// promoted int32 bit pattern used by C0.
    pub value: Option<u32>,
    pub body: Box<CStatement>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatement {
    Skip,
    Break,
    Continue,
    /// Internal lowering for a C `for` continue. The update clause is part
    /// of this atomic control transfer so source proofs still see one
    /// `continue` statement.
    ContinueWithStep {
        step: Box<CStatement>,
    },
    Declare {
        name: String,
        c_type: CType,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    /// Declare an address-backed scalar-only aggregate. Aggregate values are
    /// not runtime `CValue`s; their local binding exposes the block base so
    /// field lowering can continue to use typed memory accesses.
    DeclareAggregate {
        name: String,
        layout: CAggregateLayout,
    },
    /// Copy an address-backed aggregate, preserving typed views for any
    /// overlapping union members in its layout.
    CopyAggregate {
        target: CExpression,
        source: CExpression,
        layout: CAggregateLayout,
    },
    Assign {
        name: String,
        expression: CExpression,
    },
    CallAssign {
        target: String,
        function_name: String,
        arguments: Vec<CExpression>,
    },
    Call {
        function_name: String,
        arguments: Vec<CExpression>,
    },
    /// Allocate a runtime-sized heap block and assign either null or its fresh
    /// base pointer to `target`.
    HeapAllocate {
        target: String,
        bytes: CExpression,
        zeroed: bool,
    },
    /// End the heap allocation named by `pointer`. Null is a no-op.
    HeapFree {
        pointer: CExpression,
    },
    Assert {
        condition: CExpression,
        label: Option<String>,
    },
    /// Two statement regions whose immutable subtrees are shared by execution
    /// frontiers as they advance through a block.
    Seq(Arc<CStatement>, Arc<CStatement>),
    Return(CExpression),
    Store {
        pointer: CExpression,
        value: CExpression,
    },
    TypedStore {
        pointer: CExpression,
        value: CExpression,
        value_type: CType,
        /// See [`CExpression::TypedLoad::volatile`].
        volatile: bool,
    },
    /// Evaluate a compound-assignment or increment target as one lvalue,
    /// read it, apply the operator with the operand, and write the result back.
    Update {
        target: CExpression,
        operator: CUpdateOperator,
        operand: CExpression,
    },
    If {
        condition: CExpression,
        then_branch: Box<CStatement>,
        else_branch: Box<CStatement>,
    },
    While {
        condition: CExpression,
        invariant: Vec<Proposition>,
        invariant_checks: Vec<CLoopInvariantCheck>,
        effect_checks: Vec<CLoopEffectCheck>,
        /// Resources the loop declares for itself. An empty list means the
        /// body executes with the enclosing resource context; a declaration
        /// narrows that context to exactly these resources, with everything
        /// else the enclosing frame owns viewed rather than owned.
        resource_specs: Vec<CResourceSpec>,
        /// The loop's declared `decreases` components, in source order. An
        /// empty list means the loop is unranked. Each component is a scalar
        /// int32 C expression evaluated at the iteration entry and again at
        /// the back edge; the back-edge invariant bundle carries one
        /// nonnegativity obligation per component and one lexicographic
        /// decrease obligation over them.
        ranking_measures: Vec<CExpression>,
        /// Whether the body runs before the first condition check, as in C's
        /// `do ... while` statement.
        do_while: bool,
        body: Box<CStatement>,
    },
    Switch {
        expression: CExpression,
        cases: Vec<CSwitchCase>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopInvariantCheck {
    pub(super) proposition: SpecProposition,
    pub(super) entry_context: Option<String>,
    pub(super) preservation_context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopEffectCheck {
    pub(super) effect: CLoopEffect,
    pub(super) span: CLoopEffectSpan,
    pub(super) context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffect {
    Immutable,
    Mutable(Vec<CMemorySegment>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffectSpan {
    Whole,
    Step,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemorySegment {
    pub(super) base: CExpression,
    pub(super) start: CExpression,
    pub(super) end: CExpression,
    /// The ABI width of one logical range element. The compatibility
    /// constructor defaults to the historical int32 width; typed surface
    /// lowering preserves wider struct-array strides here.
    pub(super) element_width: u32,
    /// An optional entry-state condition guarding a contract footprint.
    /// Resource and loop segments are normally unconditional.
    pub(super) guard: Option<SpecProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemoryRange {
    pub(super) base: Pointer,
    pub(super) start: Bitvector32Term,
    pub(super) end: Bitvector32Term,
    /// The size in bytes of one logical element in `start..end`.
    ///
    /// Resource ranges remain expressed in logical element coordinates, but
    /// retaining this width lets kernel consumers derive their physical byte
    /// footprint without recovering the source C type.
    pub(super) element_width: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CParameter {
    pub(super) name: String,
    pub(super) c_type: CType,
    pub(super) aggregate_layout: Option<CAggregateLayout>,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

/// A linked file-scope scalar. Globals use one stable memory block across all
/// function frames; the initial value is installed when the first function
/// entry state is created.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobal {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) c_type: CType,
    pub(super) initial_value: CValue,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobalArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) element_type: CType,
    pub(super) length: u32,
    pub(super) initial_values: Vec<CValue>,
    pub(super) constant: bool,
}

/// A linked file-scope aggregate. The layout describes the typed leaf cells
/// that occupy the stable global block; aggregate values themselves have no
/// scalar `CValue` representation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobalAggregate {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

/// A linked file-scope array of supported struct aggregates. Initializer
/// offsets are relative to the complete array block; omitted cells are
/// zero-filled when the block is first materialized.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobalAggregateArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) length: u32,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticLocal {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) c_type: CType,
    pub(super) initial_value: CValue,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) element_type: CType,
    pub(super) length: u32,
    pub(super) initial_values: Vec<CValue>,
    pub(super) constant: bool,
}

/// A function-local aggregate with one stable function-qualified block.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticAggregate {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

/// A function-local static array of supported struct aggregates.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticAggregateArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) length: u32,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

/// Static-storage metadata shared by all copies of a function descriptor.
/// Keeping the collections behind the existing static-storage pointer avoids
/// increasing the size of the recursive `Proposition` enum's
/// function-execution variants.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CFunctionStaticStorage {
    pub(super) static_arrays: Vec<CStaticArray>,
    pub(super) global_aggregates: Vec<CGlobalAggregate>,
    pub(super) global_aggregate_arrays: Vec<CGlobalAggregateArray>,
    pub(super) static_aggregates: Vec<CStaticAggregate>,
    pub(super) static_aggregate_arrays: Vec<CStaticAggregateArray>,
}

/// A function's embedded C string constant. The bytes include the trailing
/// NUL and are installed in a stable read-only memory block at function entry.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStringLiteral {
    pub(super) name: String,
    pub(super) bytes: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateField {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) c_type: CType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateUnionField {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) c_type: CType,
}

impl CAggregateUnionField {
    pub fn new(name: impl Into<String>, offset_bytes: u32, c_type: CType) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            c_type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateUnion {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) size_bytes: u32,
    pub(super) fields: Vec<CAggregateUnionField>,
}

impl CAggregateUnion {
    pub fn new(
        name: impl Into<String>,
        offset_bytes: u32,
        size_bytes: u32,
        fields: Vec<CAggregateUnionField>,
    ) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            size_bytes,
            fields,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn fields(&self) -> &[CAggregateUnionField] {
        &self.fields
    }
}

impl CAggregateField {
    pub fn new(name: impl Into<String>, offset_bytes: u32, c_type: CType) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            c_type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }
}

/// One explicitly initialized scalar cell in a static-storage aggregate.
/// The aggregate materializer zero-fills the complete layout first, then
/// applies these entries at their ABI-relative offsets.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateInitializer {
    pub(super) offset_bytes: u32,
    pub(super) value: CValue,
}

impl CAggregateInitializer {
    pub fn new(offset_bytes: u32, value: CValue) -> Self {
        Self {
            offset_bytes,
            value,
        }
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn value(&self) -> &CValue {
        &self.value
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateLayout {
    pub(super) size_bytes: u32,
    pub(super) alignment_bytes: u32,
    pub(super) fields: Vec<CAggregateField>,
    pub(super) unions: Vec<CAggregateUnion>,
}

impl CAggregateLayout {
    pub fn new(size_bytes: u32, alignment_bytes: u32, fields: Vec<CAggregateField>) -> Self {
        assert!(alignment_bytes.is_power_of_two());
        Self {
            size_bytes,
            alignment_bytes,
            fields,
            unions: Vec::new(),
        }
    }

    pub fn with_unions(
        size_bytes: u32,
        alignment_bytes: u32,
        fields: Vec<CAggregateField>,
        unions: Vec<CAggregateUnion>,
    ) -> Self {
        assert!(alignment_bytes.is_power_of_two());
        Self {
            size_bytes,
            alignment_bytes,
            fields,
            unions,
        }
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub fn fields(&self) -> &[CAggregateField] {
        &self.fields
    }

    pub fn unions(&self) -> &[CAggregateUnion] {
        &self.unions
    }
}

/// The body-independent interface shared by every way Click can apply a
/// function contract.
///
/// A [`CFunction`] keeps the implementation body and storage alongside this
/// value, but all typed call parameters/result metadata, proof binders,
/// logical clauses, normalized resource terms, effect information, and source
/// provenance live here.  Keeping this carrier separate from the body is
/// important for opaque calls: applying a checked summary must not implicitly
/// execute (or even inspect) the concrete body.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionContractInterface {
    pub(crate) return_type: CType,
    pub(crate) return_pointee_constant: bool,
    pub(crate) return_aggregate_layout: Option<CAggregateLayout>,
    pub(crate) parameters: Vec<CParameter>,
    /// Explicit resource-instance binders introduced by a named contract.
    /// These are part of the application interface, not a body assumption.
    pub(crate) proof_parameters: std::sync::Arc<[CResourceSpec]>,
    pub(crate) resource_requires: Vec<CResourceSpec>,
    pub(crate) resource_ensures: Vec<CResourceSpec>,
    pub(crate) resource_constructors: Vec<CResourceSpec>,
    pub(crate) contract_requires: Vec<SpecProposition>,
    /// For each lowered contract requirement, the originating source
    /// `requires` clause, or `None` for a generated definedness clause.
    pub(super) contract_requirement_sources: ContractRequirementSources,
    pub(crate) contract_ensures: Vec<SpecProposition>,
    /// Checked effect information. Resource-derived frames deliberately share
    /// this carrier with explicit `Effect` frames, while retaining their
    /// distinct certification rule in `contract_effect_claim_required`.
    pub(crate) contract_mutable: Vec<CMemorySegment>,
    pub(crate) contract_effect_claim_required: bool,
    pub(crate) resource_derived_mutable_frame: bool,
    pub(crate) contract_claims: Vec<CFunctionContractClaim>,
    pub(crate) opaque_contract_supported: bool,
    pub(crate) composite_resource_definitions: Vec<CCompositeResourceDefinition>,
    /// Contract-local definitions for opaque Click predicate requirements.
    /// Both sides are instantiated at the exact function entry state.
    pub(crate) predicate_unfoldings: Vec<CPredicateUnfolding>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunction {
    pub(super) program_entry: bool,
    pub(super) name: String,
    /// Header-provided `static inline` or `static __always_inline` functions
    /// have a checked body but no
    /// Click contract. Calls to them execute that body at the call site
    /// instead of requiring an opaque verified-function rule.
    pub(super) inline_body: bool,
    pub(super) body: CStatement,
    pub(super) source_body: CStatement,
    pub(super) contract_interface: CFunctionContractInterface,
    pub(super) global_variables: Vec<CGlobal>,
    pub(super) global_arrays: Vec<CGlobalArray>,
    pub(super) static_variables: Vec<CStaticLocal>,
    pub(super) static_storage: std::sync::Arc<CFunctionStaticStorage>,
    pub(super) string_literals: Vec<CStringLiteral>,
}

/// Source provenance is planning metadata, not part of a function's checked
/// semantic identity. Its vector remains available through the function
/// accessor, while equality, hashing, and ordering stay neutral so adding a
/// source map cannot invalidate semantic caches or certificates.
#[derive(Clone, Debug, Default)]
pub(super) struct ContractRequirementSources(Vec<Option<usize>>);

impl ContractRequirementSources {
    pub(super) fn as_slice(&self) -> &[Option<usize>] {
        &self.0
    }
}

impl PartialEq for ContractRequirementSources {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for ContractRequirementSources {}

impl std::hash::Hash for ContractRequirementSources {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl PartialOrd for ContractRequirementSources {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ContractRequirementSources {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CPredicateUnfolding {
    pub(super) predicate: SpecProposition,
    pub(super) body: SpecProposition,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CCompositeResourceDefinition {
    pub(super) instance_schema: Option<ResourceFieldSchema>,
    pub(super) matched: Option<CResourceMatchBody>,
    pub(super) name: String,
    pub(super) parameters: Vec<CParameter>,
    /// Existential witnesses bound inside the body (`let next: T where P`).
    /// Each is bound like a parameter when the body is instantiated: to the
    /// recorded origin of the word its `where` fact relates it to, or to a
    /// fresh symbolic pointer when no origin is recorded yet.
    pub(super) witnesses: Vec<CParameter>,
    pub(super) condition: Option<SpecProposition>,
    pub(super) recursive: bool,
    pub(super) counted_population: bool,
    pub(super) contains: Vec<CResourceSpec>,
    pub(super) facts: Vec<SpecProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceMatchBody {
    pub field_index: usize,
    pub algebraic_type: AlgebraicType,
    pub arms: Vec<CResourceMatchArm>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    /// Kernel identities for mathematical Integer constructor bindings.
    /// C and algebraic bindings carry `None`; the identities are fresh
    /// lowering atoms that the selected constructor fields replace after the
    /// kernel has checked the arm schema.
    pub binding_variables: Vec<Option<Variable>>,
    pub contains: Vec<CResourceSpec>,
    pub facts: Vec<SpecProposition>,
    pub children: Vec<CResourceChildSpec>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceChildSpec {
    pub name: String,
    pub binding: Variable,
    pub arguments: Vec<CExpression>,
    /// Each field is an immediate constructor binding. The matched model
    /// field must be a proper submodel of the same algebraic type.
    pub field_bindings: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionContractClaimKey {
    BodySafety,
    Effect(usize),
    Ensure(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionContractClaim {
    pub(super) key: CFunctionContractClaimKey,
    pub(super) target: CFunctionContractClaimTarget,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionContractClaimTarget {
    BodySafety,
    Effect,
    EnsureProposition(usize),
    EnsureResource(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionSpecification {
    pub(super) state: CState,
    pub(super) arguments: Vec<CExpression>,
    pub(super) requires: Vec<Proposition>,
    pub(super) outcome: CFunctionOutcome,
}

/// One checked binder transport selected at an ordinary C call site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCallBinderTransport {
    /// The callee the step named. A call to any other function is refused.
    pub(crate) function: std::sync::Arc<str>,
    /// How many arguments the step wrote, checked against the call it selects.
    pub(crate) arity: usize,
    /// Every instance binder of that callee, mapped to the caller instance
    /// that supplies it. A `produces` binder maps to the fresh identity the
    /// caller's `let` introduced.
    pub(crate) bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
}

#[derive(Clone, Default)]
pub struct CExecutionEnvironment {
    // A proof-local rule choice. This is not installed in the project environment.
    pub(crate) selected_call_contract: Option<std::sync::Arc<str>>,
    pub(crate) selected_call_resource_arguments: Option<std::sync::Arc<[Variable]>>,
    /// A proof-local binder map for one ordinary C call: the callee named by
    /// the step, and one caller instance per instance binder the callee
    /// declares. Binding is a lookup per entry; nothing is searched for.
    pub(crate) selected_call_binders: Option<std::sync::Arc<CCallBinderTransport>>,
    pub(super) functions: std::sync::Arc<BTreeMap<String, CFunction>>,
    pub(super) function_contracts: std::sync::Arc<BTreeMap<String, CFunctionContract>>,
    pub(super) external_function_rules: std::sync::Arc<BTreeMap<String, CExternalFunctionRule>>,
    pub(super) verified_function_rules: std::sync::Arc<BTreeMap<String, CVerifiedFunctionRule>>,
    pub(super) verified_function_termination_rules:
        std::sync::Arc<BTreeMap<String, CVerifiedFunctionTerminationRule>>,
    pub(super) verified_loop_rules: std::sync::Arc<Vec<CVerifiedLoopRule>>,
    pub(super) variable_index: CExecutionEnvironmentVariableIndex,
}

impl std::fmt::Debug for CExecutionEnvironment {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CExecutionEnvironment")
            .field("selected_call_contract", &self.selected_call_contract)
            .field(
                "selected_call_resource_arguments",
                &self.selected_call_resource_arguments,
            )
            .field("selected_call_binders", &self.selected_call_binders)
            .field("functions", &self.functions)
            .field("function_contracts", &self.function_contracts)
            .field("external_function_rules", &self.external_function_rules)
            .field("verified_function_rules", &self.verified_function_rules)
            .field(
                "verified_function_termination_rules",
                &self.verified_function_termination_rules,
            )
            .field("verified_loop_rules", &self.verified_loop_rules)
            .finish()
    }
}

impl PartialEq for CExecutionEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.selected_call_contract == other.selected_call_contract
            && self.selected_call_resource_arguments == other.selected_call_resource_arguments
            && self.selected_call_binders == other.selected_call_binders
            && self.functions == other.functions
            && self.function_contracts == other.function_contracts
            && self.external_function_rules == other.external_function_rules
            && self.verified_function_rules == other.verified_function_rules
            && self.verified_function_termination_rules == other.verified_function_termination_rules
            && self.verified_loop_rules == other.verified_loop_rules
    }
}

impl Eq for CExecutionEnvironment {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CCallSemantics {
    ExecuteBodies,
    ApplyVerifiedRules,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CLoopSemantics {
    Verify,
    ApplyVerifiedRules,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CExecutionSemantics {
    pub calls: CCallSemantics,
    pub loops: CLoopSemantics,
}

impl CExecutionSemantics {
    pub const EXECUTE_BODIES: Self = Self {
        calls: CCallSemantics::ExecuteBodies,
        loops: CLoopSemantics::Verify,
    };

    pub const APPLY_VERIFIED_RULES: Self = Self {
        calls: CCallSemantics::ApplyVerifiedRules,
        loops: CLoopSemantics::ApplyVerifiedRules,
    };

    pub const APPLY_CALL_RULES_AND_VERIFY_LOOPS: Self = Self {
        calls: CCallSemantics::ApplyVerifiedRules,
        loops: CLoopSemantics::Verify,
    };
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionRule {
    pub(super) function: CFunction,
}

/// A nominal, body-independent behavioral interface for an indirect call.
///
/// Named contracts retain only their nominal name and this checked interface.
/// A source function may be used to build the interface, but its body, globals,
/// and static storage are not part of a callback contract and are discarded at
/// construction. This keeps indirect application independent of an arbitrary
/// source/template representation.
#[derive(Clone, Debug)]
pub struct CFunctionContract {
    pub(super) name: String,
    /// Source-name provenance retained only for diagnostics. It is not part
    /// of the contract identity and cannot alter callback behavior.
    pub(super) callee_name: String,
    pub(super) interface: CFunctionContractInterface,
}

impl PartialEq for CFunctionContract {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.interface == other.interface
    }
}

impl Eq for CFunctionContract {}

impl std::hash::Hash for CFunctionContract {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.interface.hash(state);
    }
}

impl PartialOrd for CFunctionContract {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CFunctionContract {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name
            .cmp(&other.name)
            .then_with(|| self.interface.cmp(&other.interface))
    }
}

/// A contract supplied for a C function whose implementation is outside the
/// verified source set. External rules are intentionally distinct from
/// [`CVerifiedFunctionRule`]: they are assumptions accepted at call sites,
/// not evidence that Click checked a function body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CExternalFunctionRule {
    pub(super) function: CFunction,
}

/// Kernel evidence that a partially-correct C function also returns.
///
/// Construction is deliberately separate from [`CVerifiedFunctionRule`], so
/// ordinary opaque calls never acquire a total-correctness assumption.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionTerminationRule {
    pub(super) function: CFunction,
}

/// An untrusted surface-language proposal for ranking the cycles in one C
/// function. The kernel checks every supplied index and expression against the
/// exact body before producing termination evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionTerminationPlan {
    pub(super) function_name: String,
    pub(super) recursive_measure: Option<CFunctionTerminationMeasure>,
    pub(super) loop_measures: BTreeMap<usize, Vec<CExpression>>,
}

impl CFunctionTerminationPlan {
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    pub fn extend_loop_measures(
        &mut self,
        measures: impl IntoIterator<Item = (usize, Vec<CExpression>)>,
    ) {
        self.loop_measures.extend(measures);
    }
}

/// An untrusted description of the function-level ranking candidate. The
/// termination checker resolves the selected parameter or exact contract
/// resource again against the verified function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CFunctionTerminationMeasure {
    NumericParameter(usize),
    ResourceRequirement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CTerminationError {
    pub(super) message: String,
}

impl CVerifiedFunctionTerminationRule {
    pub fn function_name(&self) -> &str {
        self.function.name()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionContractClaim {
    pub(super) function: CFunction,
    pub(super) key: CFunctionContractClaimKey,
    /// Exact load equalities consumed while checking this claim. Keeping the
    /// witnesses on the proof object makes contract finalization the owner of
    /// its equality decisions rather than relying on an ambient prover later.
    pub(super) load_equalities: Vec<super::CheckedLoadEquality>,
}

/// Kernel-checked evidence that a checked proof discharged one proposition at
/// one exact function outcome. Contract finalization matches this evidence to
/// the corresponding independently reconstructed path and contract claim;
/// the language layer cannot retarget it by changing surface metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CCheckedFunctionProposition {
    pub(super) function: CFunction,
    pub(super) specification: CFunctionSpecification,
    pub(super) proposition: Proposition,
}

impl CVerifiedFunctionContractClaim {
    pub fn key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedLoopRule {
    pub(super) symbolic_entry_state: CState,
    pub(super) loop_statement: CStatement,
    /// Source traversal index for the loop this rule certifies. The index is
    /// assigned by the proof driver after the kernel constructs the rule so
    /// termination checking can safely recover annotations from a nested
    /// frontier rule without changing the contract function's shape.
    pub(super) loop_index: Option<usize>,
    pub(super) required_assumptions: PureFactContext,
    pub(super) paths: Vec<CStatementExecutionPath>,
    pub(super) composite_resource_definitions: Vec<CCompositeResourceDefinition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUndefinedBehavior {
    SignedOverflow,
    PointerArithmetic,
    DivisionByZero,
    InvalidShift,
    InvalidMemory,
    UninitializedRead,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CInvalidFree {
    InteriorPointer,
    NonHeapPointer,
    DoubleFree,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    /// A pointer/integer cast outside the modeled LP64 conversions: the
    /// message names the rejected direction and what evidence it needed.
    PointerConversion(String),
    IndeterminatePointeeType,
    WrongArity {
        expected: usize,
        actual: usize,
    },
    MissingReturn,
    MissingResource {
        resource: CResourceFact,
    },
    MissingVerifiedFunctionRule(String),
    UnsupportedOpaqueFunctionContract(String),
    AbstractFunctionPointerCall(String),
    FunctionContract(String),
    InvalidFree(CInvalidFree),
    UnresolvedAllocationOutcome,
    LiveAllocationLeak {
        allocation: CResourceFact,
    },
    StaleResourceAfterFree {
        resource: CResourceFact,
    },
    DuplicateResource {
        resource: CResourceFact,
    },
    OverlappingOwnedMemoryResources {
        left: Box<CMemoryRange>,
        right: Box<CMemoryRange>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ExecutionLimit {
    Deadline,
    ExpressionSteps,
    StatementSteps,
    FunctionCalls,
    LoopUnrolls,
    Paths,
    UnsupportedIntegerExistentialBody,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionBudget {
    pub(super) expression_steps: usize,
    pub(super) statement_steps: usize,
    pub(super) function_calls: usize,
    pub(super) loop_unrolls: usize,
    pub(super) paths: usize,
    pub(super) next_opaque_call: u64,
    pub(super) next_kernel_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpressionOutcome {
    Value(CValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CConditionOutcome {
    Value(bool),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLValueOutcome {
    LValue(CLValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatementOutcome {
    Normal(CState),
    Break(CState),
    Continue(CState),
    Return {
        value: CValue,
        state: CState,
    },
    /// Internal to `CStatementVerifies`: the statement has no finite
    /// successor, but all of its finite prefixes have been checked.
    VerificationDiverges,
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionOutcome {
    Return {
        value: CValue,
        state: CState,
    },
    /// Internal to `CFunctionVerifies`: no return frontier exists, but the
    /// function's finite prefixes satisfy its safety proof.
    VerificationDiverges,
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLocalEnvironment {
    pub(super) bindings: std::sync::Arc<BTreeMap<String, CLocalBinding>>,
    pub(super) slots: std::sync::Arc<BTreeMap<Pointer, String>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLocalBinding {
    Object {
        value: CValue,
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    UninitializedObject {
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    GlobalObject {
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    ArrayObject {
        element_type: CType,
        length: u32,
        slot: Pointer,
        constant: bool,
    },
    AggregateObject {
        layout: CAggregateLayout,
        slot: Pointer,
        constant: bool,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CMemory {
    pub(super) blocks: std::sync::Arc<BTreeMap<PointerBlock, CBlock>>,
    pub(super) cells: std::sync::Arc<BTreeMap<Pointer, CValue>>,
    /// Typed views of address-overlapping union storage. A union member is
    /// keyed by its address and type rather than placed in `cells`, because
    /// two members at one address must remain independently readable after a
    /// by-value aggregate copy.
    pub(super) union_cells: std::sync::Arc<BTreeMap<(Pointer, CType), CValue>>,
    /// Automatic-storage blocks whose lifetimes have ended. Unlike removing
    /// the block alone, retaining this tombstone makes stale aliases invalid
    /// even when a later proof step forgets or rejoins ordinary cells.
    pub(super) ended_local_blocks: std::sync::Arc<BTreeSet<PointerBlock>>,
    pub(super) heap: std::sync::Arc<CHeapMemory>,
}

impl CMemory {
    /// O(1) diagnostic identity for a snapshot without interning or walking
    /// its contents. This is intentionally only an identity label; equal
    /// labels imply shared storage roots, not semantic inequality otherwise.
    pub(crate) fn diagnostic_identity(&self) -> (usize, usize, usize, usize, usize) {
        (
            std::sync::Arc::as_ptr(&self.blocks) as usize,
            std::sync::Arc::as_ptr(&self.cells) as usize,
            std::sync::Arc::as_ptr(&self.union_cells) as usize,
            std::sync::Arc::as_ptr(&self.ended_local_blocks) as usize,
            std::sync::Arc::as_ptr(&self.heap) as usize,
        )
    }
}

/// A pinned, shallow identity for the lifetime metadata relevant to a read.
/// Keeping the heap alive prevents allocation-address reuse in an index, and
/// the local-lifetime bit distinguishes a retired automatic block from a
/// snapshot where its block is still live.
#[derive(Clone)]
pub(in crate::kernel) struct ReadRegionIdentity {
    block_size: Option<Bitvector32Term>,
    local_lifetime_ended: bool,
    heap: Arc<CHeapMemory>,
}

impl ReadRegionIdentity {
    fn retirement_identity(&self) -> usize {
        if self.heap.deallocated_allocations.is_empty() {
            0
        } else {
            Arc::as_ptr(&self.heap) as usize
        }
    }
}

impl PartialEq for ReadRegionIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for ReadRegionIdentity {}
impl PartialOrd for ReadRegionIdentity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ReadRegionIdentity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.block_size
            .cmp(&other.block_size)
            .then_with(|| self.local_lifetime_ended.cmp(&other.local_lifetime_ended))
            .then_with(|| self.retirement_identity().cmp(&other.retirement_identity()))
    }
}

impl std::hash::Hash for CMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Keep the hash of memories without union overlays identical to the
        // pre-overlay representation. Memory-load identities are used inside
        // proof terms, so adding an empty auxiliary map must not perturb all
        // existing symbolic memory identities.
        self.blocks.hash(state);
        self.cells.hash(state);
        if !self.union_cells.is_empty() {
            self.union_cells.hash(state);
        }
        if !self.ended_local_blocks.is_empty() {
            std::hash::Hash::hash(&self.ended_local_blocks, state);
        }
        self.heap.hash(state);
    }
}

impl Ord for CMemory {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.blocks
            .cmp(&other.blocks)
            .then_with(|| self.cells.cmp(&other.cells))
            .then_with(|| self.union_cells.cmp(&other.union_cells))
            .then_with(|| self.ended_local_blocks.cmp(&other.ended_local_blocks))
            .then_with(|| self.heap.cmp(&other.heap))
    }
}

impl PartialOrd for CMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CPendingReallocation {
    pub(super) old_pointer: Pointer,
    pub(super) old_bytes: Bitvector32Term,
    /// Bytes at the start of the new block that retain calloc's guaranteed
    /// zero value. A prefix equal to the new allocation size means the whole
    /// block is zeroed; a shorter prefix leaves the grown tail uninitialized.
    pub(super) zeroed_prefix: Option<Bitvector32Term>,
    pub(super) copied_cells: Vec<(PointerOffsetTerm, CValue)>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct CHeapMemory {
    /// Live heap blocks are also present in `blocks`; this set distinguishes
    /// them from automatic storage and memory-havoc markers.
    pub(super) live_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// Heap identities are never reused within a proof. These are semantic
    /// tombstones for double-free and stale-pointer diagnostics, not
    /// resources or surviving allocation authority.
    pub(super) deallocated_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// A malloc result whose null/success outcome has not yet been refined by
    /// control flow or direct return. Pending allocations carry no authority
    /// until resolved.
    pub(super) pending_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// Successful malloc storage remains uninitialized until individual
    /// cells are written. Contract-imported allocations are not placed here.
    pub(super) uninitialized_allocations: BTreeSet<Pointer>,
    /// Successful calloc storage reads as zero until individual cells are
    /// written. The set is separate from `uninitialized_allocations` so the
    /// same heap-lifetime machinery can represent both APIs.
    pub(super) zeroed_allocations: BTreeSet<Pointer>,
    /// Successful reallocations of zeroed storage may preserve only a prefix
    /// of the old block. The remainder of a grown block is uninitialized.
    pub(super) zeroed_prefix_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// Pending calloc results whose null/success outcome has not yet been
    /// refined.
    pub(super) zeroed_pending_allocations: BTreeSet<Pointer>,
    /// Pending reallocations retain the old live block until their result is
    /// refined. Success then retires it and installs the copied prefix;
    /// failure simply resolves the new result to null.
    pub(super) pending_reallocations: BTreeMap<Pointer, CPendingReallocation>,
}

impl std::hash::Hash for CHeapMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Keep the hash of states without new heap-shape bookkeeping identical
        // to the pre-realloc heap shape. CMemory is used as a cache key by
        // proof search, and empty bookkeeping fields must not perturb the
        // search order for unrelated programs. Nonempty new state remains
        // part of the key and is tagged so it cannot alias the legacy shape.
        std::hash::Hash::hash(&self.live_allocations, state);
        std::hash::Hash::hash(&self.deallocated_allocations, state);
        std::hash::Hash::hash(&self.pending_allocations, state);
        std::hash::Hash::hash(&self.uninitialized_allocations, state);
        std::hash::Hash::hash(&self.zeroed_allocations, state);
        std::hash::Hash::hash(&self.zeroed_pending_allocations, state);
        if !self.pending_reallocations.is_empty() {
            std::hash::Hash::hash(&1u8, state);
            std::hash::Hash::hash(&self.pending_reallocations, state);
        }
        if !self.zeroed_prefix_allocations.is_empty() {
            std::hash::Hash::hash(&2u8, state);
            std::hash::Hash::hash(&self.zeroed_prefix_allocations, state);
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CBlock {
    pub(super) size: Bitvector32Term,
    pub(super) read_only: bool,
}

/// An interned, immutable memory snapshot for embedding inside terms.
///
/// Equality and hashing are O(1) via the arena identity and a precomputed
/// content hash; ordering keeps a same-identity fast path but falls back to
/// structural comparison so BTreeMap iteration order stays the structural
/// order (proof search is sensitive to iteration order, and arena-insertion
/// order would be nondeterministic across checks).
#[derive(Clone)]
pub struct SharedCMemory {
    arena: u32,
    id: u32,
    content_hash: u64,
    memory: std::sync::Arc<CMemory>,
}

impl SharedCMemory {
    /// How this snapshot was produced, when the arena that named it is this
    /// thread's and an edge producer recorded one.
    ///
    /// `None` is always a legitimate answer — for entry states, for
    /// snapshots built by paths that record no edge, and for handles that
    /// crossed a thread. Consumers fall back rather than conclude anything
    /// from the absence.
    pub(crate) fn derivation(&self) -> Option<std::sync::Arc<CMemoryDerivation>> {
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return None;
            }
            arena.1.derivations.get(self.id as usize).cloned().flatten()
        })
    }

    /// The arena id naming this snapshot, valid only against ids from the
    /// same arena. Strictly decreasing along `derivation().base()`, which is
    /// what makes DAG walks terminate.
    pub(crate) fn arena_id(&self) -> (u32, u32) {
        (self.arena, self.id)
    }

    pub(crate) fn memory(&self) -> &CMemory {
        &self.memory
    }
}

impl PartialEq for SharedCMemory {
    fn eq(&self, other: &Self) -> bool {
        if self.arena == other.arena {
            return self.id == other.id;
        }
        self.content_hash == other.content_hash && self.memory == other.memory
    }
}

impl Eq for SharedCMemory {}

impl std::hash::Hash for SharedCMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_hash);
    }
}

impl Ord for SharedCMemory {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.arena == other.arena && self.id == other.id {
            return std::cmp::Ordering::Equal;
        }
        self.memory.cmp(&other.memory)
    }
}

impl PartialOrd for SharedCMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Debug for SharedCMemory {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.memory.fmt(formatter)
    }
}

/// The compact identity of a memory snapshot at a retained proof frontier.
/// This only records the persistent-node pointers already held by `CMemory`;
/// it does not intern, clone, or scan the snapshot.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct CMemorySnapshotIdentity {
    shallow: CMemoryShallowIdentity,
}

#[cfg(test)]
thread_local! {
    static CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

impl CMemorySnapshotIdentity {
    pub(crate) fn of(memory: &CMemory) -> Self {
        Self {
            shallow: CMemoryShallowIdentity::of(memory),
        }
    }
}

/// The exact source-side identity needed to retry one unresolved call
/// requirement.  This is deliberately limited to the selected callee, its
/// source argument expressions, and the call's source snapshot identity; it
/// does not retain a C state or an ambient fact set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallRequirementSite {
    pub(crate) callee: String,
    pub(crate) interface: std::sync::Arc<str>,
    pub(crate) candidate_ordinal: usize,
    pub(crate) source_arguments: std::sync::Arc<Vec<CExpression>>,
    pub(crate) source_snapshot: CMemorySnapshotIdentity,
}

impl CallRequirementSite {
    pub(crate) fn for_requirement(
        callee: impl Into<String>,
        interface: &str,
        candidate_ordinal: usize,
        source_arguments: &[CExpression],
        source_memory: &CMemory,
    ) -> Self {
        #[cfg(test)]
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(|count| {
            count.set(count.get().saturating_add(1));
        });
        Self {
            callee: callee.into(),
            interface: std::sync::Arc::from(interface),
            candidate_ordinal,
            source_arguments: std::sync::Arc::new(source_arguments.to_vec()),
            source_snapshot: CMemorySnapshotIdentity::of(source_memory),
        }
    }

    #[cfg(test)]
    pub(crate) fn reset_test_construction_count() {
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(|count| count.set(0));
    }

    #[cfg(test)]
    pub(crate) fn test_construction_count() -> u64 {
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(std::cell::Cell::get)
    }
}

/// The selected top-level requirement attached to one unresolved call site.
/// The site identity is shared across requirements from that call, while the
/// ordinal remains specific to this requirement and its path obligations.
/// `None` denotes a generated clause or a kernel-built contract without a
/// source registry entry; ordinary callee source resolution is a later
/// planner concern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallRequirementSource {
    pub(crate) site: std::sync::Arc<CallRequirementSite>,
    pub(crate) requirement_ordinal: usize,
    pub(crate) source_requirement_ordinal: Option<usize>,
    /// Whether the complete selected source requirement is state independent.
    /// This is a capability of the top-level requirement, not of any one
    /// lowered leaf, so every obligation emitted from the requirement shares
    /// the same answer.
    pub(crate) source_requirement_is_state_independent: bool,
}

impl CallRequirementSource {
    pub(crate) fn new(
        site: std::sync::Arc<CallRequirementSite>,
        requirement_ordinal: usize,
        source_requirement_ordinal: Option<usize>,
        source_requirement_is_state_independent: bool,
    ) -> Self {
        Self {
            site,
            requirement_ordinal,
            source_requirement_ordinal,
            // Generated requirements and contracts without a source registry
            // must never advertise source-side capabilities.
            source_requirement_is_state_independent: source_requirement_ordinal.is_some()
                && source_requirement_is_state_independent,
        }
    }
}

impl std::ops::Deref for CallRequirementSource {
    type Target = CallRequirementSite;

    fn deref(&self) -> &Self::Target {
        &self.site
    }
}

impl std::ops::Deref for SharedCMemory {
    type Target = CMemory;

    fn deref(&self) -> &CMemory {
        &self.memory
    }
}

impl AsRef<CMemory> for SharedCMemory {
    fn as_ref(&self) -> &CMemory {
        &self.memory
    }
}

impl From<CMemory> for SharedCMemory {
    fn from(memory: CMemory) -> Self {
        intern_c_memory(memory)
    }
}

impl From<&CMemory> for SharedCMemory {
    fn from(memory: &CMemory) -> Self {
        intern_c_memory_ref(memory)
    }
}

/// How a memory snapshot was produced from an earlier one: the edges of the
/// named-memory-state DAG (`docs/internals/memory-dag.md`). Each
/// variant names its base snapshot, so following `base` walks backwards
/// through the write history that execution already knew when it built the
/// snapshot — instead of reconstructing that history at proof time from
/// recorded effect facts.
///
/// A derivation is **advisory**. It only ever states a true fact about how a
/// snapshot arose, so every consumer must fall back to its previous
/// reasoning when none is present; nothing may depend on one existing. That
/// is why a snapshot interned on another thread (the arena is thread-local)
/// is merely slower to reason about rather than wrong.
///
/// `LoopHavoc` is deliberately its own edge kind rather than a bulk store.
/// Interface havoc has no checked write set, so no load-preservation walk may
/// cross that form. Verified whole-loop effects may carry a checked write set;
/// those edges are crossed only with range-disjointness evidence. Enforcing
/// that at the edge is how havoc identity survives this arc by construction,
/// upstream of any snapshot comparison (see conventions.md's soundness trap).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CMemoryDerivation {
    /// `base` with one cell written. Aliasing between the written cell and
    /// a later load is decided in the querying proof context, never from
    /// facts captured on the edge: interning is first-wins on equal
    /// snapshots, so an edge can be shared by paths with different
    /// assumptions.
    Store {
        base: SharedCMemory,
        pointer: Pointer,
        value: CValue,
    },
    /// `base` with one block declared; no cell changes, so every load reads
    /// exactly what it read in `base`. This fourth edge kind was added after
    /// the initial DAG arc; without it, block declaration split the DAG into
    /// disjoint components ("arena identity is connected, arena derivations
    /// are not"). The havoc producers insert their marker
    /// blocks directly rather than through [`CMemory::with_block`], so this
    /// edge can never alias a havoc hop.
    BlockDeclared {
        base: SharedCMemory,
        block: PointerBlock,
    },
    /// `base` with one fresh, uninitialized heap block made live.
    HeapAllocated {
        base: SharedCMemory,
        block: PointerBlock,
        bytes: Bitvector32Term,
    },
    /// `base` with one unresolved allocation result registered. Pending
    /// metadata changes no program-observable memory, so every existing load
    /// is preserved across this edge.
    HeapAllocationPending {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with only the allocation claims imported from contracts
    /// changed. Consuming an input claim and installing an output claim do
    /// not write bytes, allocate storage, or free storage, so every load is
    /// preserved across this edge.
    ContractAllocationClaimsChanged { base: SharedCMemory },
    /// `base` with one complete heap allocation lifetime ended.
    ///
    /// `allocation_base` is kept rather than only its broad pointer block:
    /// allocations imported from contracts can be subranges of external
    /// memory, where retiring the whole `ExternalArgument` block would also
    /// deallocate unrelated objects.
    HeapFreed {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with some cached cell values forgotten at one program point:
    /// the write path narrows the cell map before storing
    /// (`without_possible_aliasing_cells`), which changes the form but
    /// not the state, so every load still reads exactly what it read in
    /// `base`. Recorded ONLY where forgetting is unconditional; the
    /// case-split prune in the load path (`without_cell` under an assumed
    /// distinctness branch) must never record one, because its two forms
    /// agree only under that branch's assumption. Havoc forgetting keeps its
    /// own never-crossed / guarded edge kinds, so this edge cannot launder a
    /// havoc (conventions.md's soundness trap).
    CellsForgotten { base: SharedCMemory },
    /// `base` after a loop body that may write anything it can reach.
    ///
    /// `mutable_ranges` is present only when the loop's whole-effect summary
    /// supplied a checked footprint. `None` remains an unconditional barrier;
    /// `Some(empty)` is a checked no-write footprint.
    LoopHavoc {
        base: SharedCMemory,
        variable: Variable,
        mutable_ranges: Option<Vec<CMemoryRange>>,
    },
    /// `base` after an automatic-storage object's lifetime ended. The block
    /// is named so the memory-DAG can preserve unrelated loads while stopping
    /// every load through an alias to this retired object.
    LocalLifetimeEnded {
        base: SharedCMemory,
        block: PointerBlock,
    },
    /// `base` after a call that may write only within `mutable_ranges`.
    ///
    /// Preservation of a load outside those ranges must be justified in the
    /// querying proof context. Two paths with different assumptions (for
    /// example `length == 0` and `length == 1`) can produce this exact
    /// snapshot, so no path's assumptions may be attached to the edge.
    CallHavoc {
        base: SharedCMemory,
        variable: Variable,
        mutable_ranges: Vec<CMemoryRange>,
    },
}

impl CMemoryDerivation {
    /// The snapshot this one was derived from.
    pub fn base(&self) -> &SharedCMemory {
        match self {
            Self::Store { base, .. }
            | Self::BlockDeclared { base, .. }
            | Self::HeapAllocated { base, .. }
            | Self::HeapAllocationPending { base, .. }
            | Self::ContractAllocationClaimsChanged { base }
            | Self::HeapFreed { base, .. }
            | Self::CellsForgotten { base }
            | Self::LocalLifetimeEnded { base, .. }
            | Self::LoopHavoc { base, .. }
            | Self::CallHavoc { base, .. } => base,
        }
    }
}

static NEXT_MEMORY_ARENA_TOKEN: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

#[derive(Default)]
struct CMemoryArena {
    identities: std::collections::HashMap<std::sync::Arc<CMemory>, (u32, u64)>,
    shallow_identities: std::collections::HashMap<CMemoryShallowIdentity, (u32, u64)>,
    memories: Vec<std::sync::Arc<CMemory>>,
    /// Indexed by arena id; `None` for entry states and for any snapshot
    /// whose first interning did not come from a recorded edge.
    derivations: Vec<Option<std::sync::Arc<CMemoryDerivation>>>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct CMemoryShallowIdentity {
    blocks: usize,
    cells: usize,
    union_cells: usize,
    ended_local_blocks: usize,
    heap: usize,
}

impl CMemoryShallowIdentity {
    fn of(memory: &CMemory) -> Self {
        Self {
            blocks: std::sync::Arc::as_ptr(&memory.blocks) as usize,
            cells: std::sync::Arc::as_ptr(&memory.cells) as usize,
            union_cells: std::sync::Arc::as_ptr(&memory.union_cells) as usize,
            ended_local_blocks: std::sync::Arc::as_ptr(&memory.ended_local_blocks) as usize,
            heap: std::sync::Arc::as_ptr(&memory.heap) as usize,
        }
    }
}

thread_local! {
    static C_MEMORY_ARENA: std::cell::RefCell<(u32, CMemoryArena)> = std::cell::RefCell::new((
        NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        CMemoryArena::default(),
    ));
    static C_MEMORY_DERIVATION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Replaces this thread's memory arena with an empty one under a fresh
/// token. Snapshots interned before keep comparing by content but lose
/// their derivations, so nothing recorded for an earlier verification can
/// answer a DAG walk in a later one. Called by [`super::VerificationSession`]
/// at the outermost verification entry; see its documentation.
pub(super) fn start_fresh_c_memory_arena() {
    C_MEMORY_ARENA.with(|arena| {
        *arena.borrow_mut() = (
            NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            CMemoryArena::default(),
        );
    });
}

/// Bumped every time a derivation slot is filled. Memo tables over DAG walks
/// key on this so an edge recorded later invalidates earlier "no path"
/// answers instead of leaving them stale.
pub(super) fn c_memory_derivation_generation() -> u64 {
    C_MEMORY_DERIVATION_GENERATION.with(std::cell::Cell::get)
}

/// Records that `result` is `derivation` applied to its base, unless
/// `result` already carries a derivation.
///
/// **First-wins is load-bearing, not a cache policy.** A derivation's base
/// must already be interned in order to be named, so it always holds a
/// strictly smaller arena id than a *newly* assigned one. Keeping the first
/// derivation therefore makes `base.id < derived.id` an arena-wide
/// invariant, and cycles unrepresentable rather than merely unlikely. Two
/// otherwise easy cycles are closed by exactly this: a store whose value
/// equals the cell already there (the result re-interns to its own base, so
/// `base.id == result.id` and the edge is dropped), and a store-then-store-
/// back pair (the second result re-interns to the earlier node and keeps
/// that node's older derivation). Callers may rely on any walk over `base`
/// terminating; a hop cap still depth-gates them, per conventions.md.
pub(crate) fn record_c_memory_derivation(result: &CMemory, derivation: CMemoryDerivation) {
    // Interning borrows the arena, so it has to finish before the write.
    let derived = intern_c_memory_ref(result);
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        if arena.0 != derived.arena || arena.0 != derivation.base().arena {
            return;
        }
        let arena = &mut arena.1;
        let Some(slot) = arena.derivations.get_mut(derived.id as usize) else {
            return;
        };
        if slot.is_some() || derivation.base().id >= derived.id {
            return;
        }
        *slot = Some(std::sync::Arc::new(derivation));
        C_MEMORY_DERIVATION_GENERATION.with(|generation| generation.set(generation.get() + 1));
    });
}

fn c_memory_content_hash(memory: &CMemory) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    hasher.finish()
}

fn record_c_memory_structural_lookup_work(memory: &CMemory) {
    crate::instrumentation::record_deterministic_work(
        memory.blocks.len()
            + memory.cells.len()
            + memory.union_cells.len()
            + memory.ended_local_blocks.len()
            + memory.heap.live_allocations.len()
            + memory.heap.deallocated_allocations.len()
            + memory.heap.pending_allocations.len()
            + memory.heap.uninitialized_allocations.len()
            + memory.heap.zeroed_allocations.len()
            + memory.heap.zeroed_prefix_allocations.len()
            + memory.heap.zeroed_pending_allocations.len()
            + memory.heap.pending_reallocations.len(),
    );
}

/// Interns a memory snapshot in the thread-local arena. Structurally equal
/// snapshots interned on the same thread share one allocation and identity;
/// snapshots that cross threads still compare correctly through the content
/// hash and structural fallback.
pub fn intern_c_memory(memory: CMemory) -> SharedCMemory {
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let (token, arena) = &mut *arena;
        let shallow_identity = CMemoryShallowIdentity::of(&memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_c_memory_structural_lookup_work(&memory);
        if let Some((stored, (id, content_hash))) = arena.identities.get_key_value(&memory) {
            return SharedCMemory {
                arena: *token,
                id: *id,
                content_hash: *content_hash,
                memory: stored.clone(),
            };
        }
        let id = u32::try_from(arena.identities.len()).expect("memory arena exhausted");
        let content_hash = c_memory_content_hash(&memory);
        let stored = std::sync::Arc::new(memory);
        arena.identities.insert(stored.clone(), (id, content_hash));
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: stored,
        }
    })
}

/// Interns by reference: an already-interned snapshot is found without
/// cloning it, so hot memoization lookups keyed by interned identity pay a
/// hash and comparison but no allocation.
pub fn intern_c_memory_ref(memory: &CMemory) -> SharedCMemory {
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let (token, arena) = &mut *arena;
        let shallow_identity = CMemoryShallowIdentity::of(memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_c_memory_structural_lookup_work(memory);
        if let Some((stored, (id, content_hash))) = arena.identities.get_key_value(memory) {
            return SharedCMemory {
                arena: *token,
                id: *id,
                content_hash: *content_hash,
                memory: stored.clone(),
            };
        }
        let id = u32::try_from(arena.identities.len()).expect("memory arena exhausted");
        let content_hash = c_memory_content_hash(memory);
        let stored = std::sync::Arc::new(memory.clone());
        arena.identities.insert(stored.clone(), (id, content_hash));
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: stored,
        }
    })
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CState {
    /// Lexical field values for scratch resource-body evaluation only.
    /// This is not ownership and is never populated by unfolding a resource.
    pub(super) instance_field_scope: ResourceContext,
    /// Call-local formal identities; the ledger retains actual caller identities.
    pub(super) resource_bindings: Option<std::sync::Arc<BTreeMap<Variable, Variable>>>,
    pub(super) locals: CLocalEnvironment,
    pub(super) memory: CMemory,
    pub(super) resources: ResourceContext,
    pub(super) counted_populations: std::sync::Arc<Vec<CCountedPopulation>>,
    /// Monotonic identity source for stack frames created by nested calls.
    /// Keeping this in the symbolic state makes frame identities deterministic
    /// and ensures recursive calls cannot reuse a caller's stack slots.
    pub(super) next_local_frame: u64,
    /// Monotonic identity source for automatic-storage objects whose
    /// declaration can be re-entered by a loop. This is path state so joins
    /// and nested calls cannot accidentally reuse an ended local block.
    pub(super) next_local_lifetime: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CCountedPopulation {
    pub(super) name: String,
    pub(super) arguments: ResourceArguments,
    pub(super) count: Bitvector32Term,
    /// Marks observation of a resource family even while its exact population
    /// is zero. Marker entries are not themselves resource populations.
    pub(super) family_observation_marker: bool,
}

type ResourceEntryId = u64;
type ResourceEntryIds = PersistentSet<ResourceEntryId>;

/// An immutable resource composition snapshot.
///
/// One pointer-sized storage root keeps recursive execution frames shallow.
/// Forks share that root; a local insertion or removal replaces only the
/// logarithmic paths in the fact store and affected indexes.
#[derive(Clone, Default)]
pub struct ResourceContext {
    pub(super) storage: std::sync::Arc<ResourceContextStorage>,
}

#[derive(Clone, Default)]
pub(super) struct ResourceContextStorage {
    /// Stable ordinals preserve insertion order without shifting surviving
    /// entries after a removal.
    pub(super) facts: PersistentMap<ResourceEntryId, CResourceFact>,
    pub(super) next_entry_id: ResourceEntryId,
    pub(super) index: ResourceContextIndex,
    /// Derived view entries name the exact owned resource that supports them.
    /// Ordinary entries are explicit and therefore absent from this map.
    pub(super) supported_by: PersistentMap<ResourceEntryId, CResourceFact>,
    /// Reverse support index used to remove only the projections of a
    /// consumed owned resource, without scanning the ambient context.
    pub(super) projections_by_support: PersistentMap<CResourceFact, ResourceEntryIds>,
    /// Certified, snapshot-stable owned expansions for folded resource
    /// generations. Reusing these avoids re-lowering the same body into
    /// fresh symbolic load identities at each later transition.
    pub(super) expansions_by_support:
        PersistentMap<CResourceFact, std::sync::Arc<Vec<CResourceFact>>>,
    /// Persistent mutation ancestry used by checked Proof joins. The origin
    /// distinguishes unrelated snapshots; the history names only exact facts
    /// whose multiplicity or representation changed.
    pub(super) origin: std::sync::Arc<()>,
    pub(super) history: Option<std::sync::Arc<ResourceContextChange>>,
    /// Legacy callers that explicitly enumerate every fact pay the
    /// output-sized materialization once per immutable snapshot.
    pub(super) materialized: std::sync::OnceLock<Vec<CResourceFact>>,
}

#[derive(Clone)]
pub(super) struct ResourceContextChange {
    pub(super) fact: CResourceFact,
    pub(super) parent: Option<std::sync::Arc<ResourceContextChange>>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct ResourceContextIndex {
    pub(super) instances: PersistentMap<Variable, ResourceEntryIds>,
    pub(super) exact: PersistentMap<CResourceFact, ResourceEntryIds>,
    pub(super) by_resource: PersistentMap<CResource, ResourceEntryIds>,
    pub(super) exact_shapes: PersistentMap<(ResourceFamily, String, usize), ResourceEntryIds>,
    pub(super) memory_by_block: PersistentMap<PointerBlock, ResourceEntryIds>,
    pub(super) owned_memory_by_block: PersistentMap<PointerBlock, ResourceEntryIds>,
    pub(super) memory_starts:
        PersistentMap<(PointerBlock, bool, Bitvector32Term), ResourceEntryIds>,
    pub(super) memory_ends: PersistentMap<(PointerBlock, bool, Bitvector32Term), ResourceEntryIds>,
    pub(super) concrete_memory: PersistentMap<(Pointer, bool, u32, u32), ResourceEntryIds>,
    pub(super) concrete_memory_by_base: PersistentMap<(Pointer, bool), usize>,
}

impl std::fmt::Debug for ResourceContext {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ResourceContext")
            .field("facts", &self.facts())
            .finish()
    }
}

impl PartialEq for ResourceContext {
    fn eq(&self, other: &Self) -> bool {
        if std::sync::Arc::ptr_eq(&self.storage, &other.storage) {
            return true;
        }
        self.facts() == other.facts()
            && self.storage.supported_by == other.storage.supported_by
            && self.storage.expansions_by_support == other.storage.expansions_by_support
    }
}

impl Eq for ResourceContext {}

impl std::hash::Hash for ResourceContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.facts().hash(state);
        for entry in self.storage.supported_by.iter() {
            entry.hash(state);
        }
        for entry in self.storage.expansions_by_support.iter() {
            entry.hash(state);
        }
    }
}

impl Ord for ResourceContext {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.facts()
            .cmp(other.facts())
            .then_with(|| {
                self.storage
                    .supported_by
                    .iter()
                    .cmp(other.storage.supported_by.iter())
            })
            .then_with(|| {
                self.storage
                    .expansions_by_support
                    .iter()
                    .cmp(other.storage.expansions_by_support.iter())
            })
    }
}

impl PartialOrd for ResourceContext {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceFact {
    Own(CResource, Box<Bitvector32Term>),
    View(CResource),
}

/// Immutable logical indices shared by resource snapshots and population keys.
/// Cloning a resource must not clone a recursive model stored in its indices.
pub type ResourceArguments = std::sync::Arc<[AlgebraicValue]>;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResource {
    Memory(CMemoryRange),
    Composite {
        name: String,
        arguments: ResourceArguments,
    },
    Token {
        name: String,
        arguments: ResourceArguments,
    },
    Instance(ResourceInstance),
}

/// A proof-only, exclusive resource instance. Identity is independent of its
/// field state; equal fields do not identify distinct instances. This is an
/// opaque ownership atom: its arguments and fields grant no memory authority.
/// Constructing an atom is not a proof that it is owned or that a resource
/// definition's body holds.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceInstance {
    pub(super) identity: Variable,
    pub(super) name: String,
    pub(super) arguments: ResourceArguments,
    pub(super) schema: ResourceFieldSchema,
    pub(super) fields: ResourceArguments,
}

impl ResourceInstance {
    pub fn new(
        identity: Variable,
        name: String,
        arguments: ResourceArguments,
        schema: ResourceFieldSchema,
        fields: ResourceArguments,
    ) -> Option<Self> {
        if schema.is_countable() || schema.fields().len() != fields.len() {
            return None;
        }
        for ((_, ty), value) in schema.fields().iter().zip(fields.iter()) {
            let valid = match (ty, value) {
                (ResourceFieldType::Integer, AlgebraicValue::Integer(_)) => true,
                (ResourceFieldType::C(ty), AlgebraicValue::C(value)) => *ty == value.c_type(),
                (ResourceFieldType::Algebraic(ty), AlgebraicValue::Algebraic(value)) => {
                    *ty == value.algebraic_type && value.is_well_formed()
                }
                _ => false,
            };
            if !valid {
                return None;
            }
        }
        Some(Self {
            identity,
            name,
            arguments,
            schema,
            fields,
        })
    }

    pub fn identity(&self) -> Variable {
        self.identity
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arguments(&self) -> &[AlgebraicValue] {
        &self.arguments
    }
    pub fn fields(&self) -> &[AlgebraicValue] {
        &self.fields
    }
    pub fn schema(&self) -> &ResourceFieldSchema {
        &self.schema
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceContextValidityError {
    InvalidInstanceAccess(CResourceFact),
    DuplicateOwnedResourceFact(CResourceFact),
    OverlappingOwnedMemoryResources {
        left: CMemoryRange,
        right: CMemoryRange,
    },
}

/// The result of consuming one available resource fact to satisfy a required
/// fact. Viewed facts are normally preserved; owned facts may be removed or
/// replaced by residual ownership.
pub(super) enum ResourceFactConsumption {
    Preserve,
    Replace(Vec<CResourceFact>),
}

/// The algebraic behavior supplied by one resource family.
///
/// `ResourceContext` provides state-level composition. Families define when
/// same-family facts are valid together, how one fact entails or satisfies
/// another, how consumed ownership leaves residues, how redundant facts are
/// normalized, and which facts are observable from a valid composition.
pub(super) trait ResourceFamilyAlgebra {
    fn family(&self) -> ResourceFamily;

    /// Checks the access/quantity envelope before a specification reaches a
    /// family operation.  The common normalized carrier delegates this check
    /// to the selected family rather than allowing its representational shape
    /// to broaden family semantics.
    fn validate_spec(&self, spec: &CResourceSpec) -> Result<(), CResourceSpecError> {
        if spec.term.family() != self.family() {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "resource term and family algebra disagree".into(),
            ));
        }
        match self.family() {
            ResourceFamily::Memory => {
                if !matches!(spec.quantity, CResourceQuantity::One) {
                    return Err(CResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Memory,
                        reason: "memory ranges have unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Instance => {
                if spec.access != CResourceAccessMode::Own {
                    return Err(CResourceSpecError::InvalidAccess {
                        family: ResourceFamily::Instance,
                        access: spec.access,
                    });
                }
                if !matches!(spec.quantity, CResourceQuantity::One) {
                    return Err(CResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Instance,
                        reason: "field-bearing instances have unit quantity".into(),
                    });
                }
                if !matches!(spec.term, CResourceTerm::Instance { ref resource, .. } if matches!(resource.as_ref(), CResourceTerm::Composite { .. }))
                {
                    return Err(CResourceSpecError::InvalidNestedTerm(
                        "field-bearing instances require a declared composite term".into(),
                    ));
                }
            }
            ResourceFamily::Composite | ResourceFamily::Token => {
                if matches!(spec.quantity, CResourceQuantity::Count(_))
                    && spec.access != CResourceAccessMode::Own
                {
                    return Err(CResourceSpecError::InvalidAccess {
                        family: self.family(),
                        access: spec.access,
                    });
                }
            }
        }
        Ok(())
    }

    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError>;

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> bool;

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption>;

    /// Returns one fact equivalent to composing this pair when the pair can be
    /// losslessly normalized. `None` leaves both facts in the resource state.
    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<CResourceFact>;

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact>;

    fn observable_facts(
        &self,
        facts: &[&CResourceFact],
        assumptions: &PureFactContext,
    ) -> Vec<Proposition>;
}

struct MemoryResourceAlgebra;
struct TokenResourceAlgebra;
/// The kernel algebra for a folded composite fact is exact-match ownership and
/// viewing. Source-declared body equivalences are applied as fold, unfold, and
/// observation laws by the Click proof layer.
struct CompositeResourceAlgebra;
struct InstanceResourceAlgebra;

static MEMORY_RESOURCE_ALGEBRA: MemoryResourceAlgebra = MemoryResourceAlgebra;
static TOKEN_RESOURCE_ALGEBRA: TokenResourceAlgebra = TokenResourceAlgebra;
static COMPOSITE_RESOURCE_ALGEBRA: CompositeResourceAlgebra = CompositeResourceAlgebra;
static INSTANCE_RESOURCE_ALGEBRA: InstanceResourceAlgebra = InstanceResourceAlgebra;

/// Primitive resource families. Adding a variant also requires registering one
/// `ResourceFamilyAlgebra` implementation in `resource_family_algebra`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFamily {
    Memory,
    Composite,
    Token,
    Instance,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceAccessMode {
    Own,
    View,
}

/// The resource term carried by a normalized specification.
///
/// Access is deliberately not part of this enum.  A memory range, declared
/// resource, and field-bearing instance all share the same representation
/// above the family algebra; the family still decides which access and
/// quantity combinations are valid.  An instance's inner term is retained so
/// its declaration identity and schema remain explicit without encoding them
/// in vector position or in a memory-only variant.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceTerm {
    Memory(CMemorySegment),
    Composite {
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    },
    Token {
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    },
    Instance {
        identity: Variable,
        /// The spelling the declaration gave this binder. The identity is the
        /// semantic key; this is the name a binder or proof-parameter map is
        /// written with, retained the same way [`CResourceChildSpec::name`]
        /// retains a child slot's spelling, so diagnostics can print the map
        /// the user has to write.
        ///
        /// The surface binding the clause carries is the single source for
        /// this spelling: lowering copies it here, and the parser copies the
        /// same name into its own per-callee binder index for the call maps it
        /// checks before lowering runs.
        binder: String,
        schema: ResourceFieldSchema,
        resource: Box<CResourceTerm>,
    },
}

/// Quantity is explicit in the normalized form.  `One` is the ordinary unit
/// quantity; `Count` is reserved for the existing counted composite/token
/// resources.  In particular, memory and exclusive instances cannot acquire a
/// quantity merely because a wrapper could represent one.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceQuantity {
    One,
    Count(CExpression),
}

/// The transfer operation associated with a normalized specification.
/// Resource vectors remain grouped by their source-level section for stable
/// ordering, but the semantic operation is carried on each element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceTransferRole {
    Borrow,
    Consume,
    Produce,
}

/// Which state supplies the resource term's address, arguments, or quantity.
/// Callers may still pass an explicitly selected state to the evaluator; this
/// metadata records the selection made by lowering and prevents entry/post
/// meaning from being inferred from a vector's position.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceSnapshot {
    Entry,
    Current,
    Post,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceSpec {
    term: CResourceTerm,
    access: CResourceAccessMode,
    quantity: CResourceQuantity,
    role: CResourceTransferRole,
    snapshot: CResourceSnapshot,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CResourceSpecError {
    InvalidAccess {
        family: ResourceFamily,
        access: CResourceAccessMode,
    },
    InvalidQuantity {
        family: ResourceFamily,
        reason: String,
    },
    InvalidNestedTerm(String),
}

impl std::fmt::Display for CResourceSpecError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidAccess { family, access } => {
                write!(
                    formatter,
                    "{family:?} resources do not permit {access:?} access"
                )
            }
            Self::InvalidQuantity { family, reason } => {
                write!(
                    formatter,
                    "{family:?} resource has invalid quantity: {reason}"
                )
            }
            Self::InvalidNestedTerm(reason) => formatter.write_str(reason),
        }
    }
}

impl std::error::Error for CResourceSpecError {}

impl CResourceTerm {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Memory(_) => ResourceFamily::Memory,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
            Self::Instance { .. } => ResourceFamily::Instance,
        }
    }

    pub fn memory_segment(&self) -> Option<&CMemorySegment> {
        match self {
            Self::Memory(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn instance_identity(&self) -> Option<Variable> {
        match self {
            Self::Instance { identity, .. } => Some(*identity),
            _ => None,
        }
    }

    pub fn instance_binder(&self) -> Option<&str> {
        match self {
            Self::Instance { binder, .. } => Some(binder),
            _ => None,
        }
    }

    pub fn instance_schema(&self) -> Option<&ResourceFieldSchema> {
        match self {
            Self::Instance { schema, .. } => Some(schema),
            _ => None,
        }
    }

    pub fn instance_resource(&self) -> Option<&CResourceTerm> {
        match self {
            Self::Instance { resource, .. } => Some(resource),
            _ => None,
        }
    }

    pub fn declared_name(&self) -> Option<&str> {
        match self {
            Self::Composite { name, .. } | Self::Token { name, .. } => Some(name),
            _ => None,
        }
    }

    pub fn declared_arguments(&self) -> Option<&[CExpression]> {
        match self {
            Self::Composite { arguments, .. } | Self::Token { arguments, .. } => Some(arguments),
            _ => None,
        }
    }

    pub fn declared_parameter_types(&self) -> Option<&[CType]> {
        match self {
            Self::Composite {
                parameter_types, ..
            }
            | Self::Token {
                parameter_types, ..
            } => Some(parameter_types),
            _ => None,
        }
    }
}

impl CResourceSpec {
    pub fn new(
        term: CResourceTerm,
        access: CResourceAccessMode,
        quantity: CResourceQuantity,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        let spec = Self {
            term,
            access,
            quantity,
            role,
            snapshot,
        };
        spec.validate()?;
        Ok(spec)
    }

    pub fn memory(
        segment: CMemorySegment,
        access: CResourceAccessMode,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Self {
        Self::new(
            CResourceTerm::Memory(segment),
            access,
            CResourceQuantity::One,
            role,
            snapshot,
        )
        .expect("unit memory terms are valid by construction")
    }

    /// Constructors for kernel callers that do not have a surrounding
    /// transfer section.  Surface lowering uses the fully annotated
    /// constructor below; these defaults describe the caller-selected
    /// current state, with the transfer role made explicit as `Consume`.
    pub fn viewed_memory(segment: CMemorySegment) -> Self {
        Self::memory(
            segment,
            CResourceAccessMode::View,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Current,
        )
    }

    pub fn owned_memory(segment: CMemorySegment) -> Self {
        Self::memory(
            segment,
            CResourceAccessMode::Own,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
    }

    pub fn declared(
        family: ResourceFamily,
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        let term = match family {
            ResourceFamily::Composite => CResourceTerm::Composite {
                name,
                arguments,
                parameter_types,
            },
            ResourceFamily::Token => CResourceTerm::Token {
                name,
                arguments,
                parameter_types,
            },
            ResourceFamily::Memory | ResourceFamily::Instance => {
                return Err(CResourceSpecError::InvalidNestedTerm(
                    "only composite and token families have declared resource terms".into(),
                ));
            }
        };
        Self::new(term, access, CResourceQuantity::One, role, snapshot)
    }

    pub fn instance(
        identity: Variable,
        binder: String,
        schema: ResourceFieldSchema,
        resource: CResourceSpec,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        if resource.access != CResourceAccessMode::Own
            || resource.quantity != CResourceQuantity::One
            || !matches!(resource.term, CResourceTerm::Composite { .. })
        {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "named resource instances require an owned unit composite term".into(),
            ));
        }
        Self::new(
            CResourceTerm::Instance {
                identity,
                binder,
                schema,
                resource: Box::new(resource.term),
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            role,
            snapshot,
        )
    }

    pub fn quantified(
        quantity: CExpression,
        resource: CResourceSpec,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        if resource.access != CResourceAccessMode::Own {
            return Err(CResourceSpecError::InvalidAccess {
                family: resource.family(),
                access: resource.access,
            });
        }
        if resource.quantity != CResourceQuantity::One {
            return Err(CResourceSpecError::InvalidQuantity {
                family: resource.family(),
                reason: "a counted resource must wrap a unit term".into(),
            });
        }
        if matches!(
            resource.family(),
            ResourceFamily::Memory | ResourceFamily::Instance
        ) {
            return Err(CResourceSpecError::InvalidQuantity {
                family: resource.family(),
                reason: "this resource family does not support quantities".into(),
            });
        }
        if !matches!(
            resource.term,
            CResourceTerm::Composite { .. } | CResourceTerm::Token { .. }
        ) {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "quantities require an owned unit composite or token term".into(),
            ));
        }
        Self::new(
            resource.term,
            CResourceAccessMode::Own,
            CResourceQuantity::Count(quantity),
            role,
            snapshot,
        )
    }

    pub fn term(&self) -> &CResourceTerm {
        &self.term
    }

    pub fn access(&self) -> CResourceAccessMode {
        self.access
    }

    pub fn quantity(&self) -> &CResourceQuantity {
        &self.quantity
    }

    pub fn role(&self) -> CResourceTransferRole {
        self.role
    }

    pub fn snapshot(&self) -> CResourceSnapshot {
        self.snapshot
    }

    pub fn family(&self) -> ResourceFamily {
        self.term.family()
    }

    pub fn is_view(&self) -> bool {
        self.access == CResourceAccessMode::View
    }

    pub fn is_instance(&self) -> bool {
        matches!(self.term, CResourceTerm::Instance { .. })
    }

    pub fn instance_identity(&self) -> Option<Variable> {
        self.term.instance_identity()
    }

    pub fn instance_binder(&self) -> Option<&str> {
        self.term.instance_binder()
    }

    pub fn instance_schema(&self) -> Option<&ResourceFieldSchema> {
        self.term.instance_schema()
    }

    pub fn instance_resource(&self) -> Option<CResourceTerm> {
        self.term.instance_resource().cloned()
    }

    pub fn instance_resource_spec(&self) -> Option<Self> {
        let resource = self.instance_resource()?;
        Some(
            Self::new(
                resource,
                CResourceAccessMode::Own,
                CResourceQuantity::One,
                self.role,
                self.snapshot,
            )
            .expect("validated instance terms have valid owned unit bodies"),
        )
    }

    pub fn memory_segment(&self) -> Option<&CMemorySegment> {
        self.term.memory_segment()
    }

    pub fn memory_segment_mut(&mut self) -> Option<&mut CMemorySegment> {
        match &mut self.term {
            CResourceTerm::Memory(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn declared_name(&self) -> Option<&str> {
        self.term.declared_name()
    }

    pub fn declared_arguments(&self) -> Option<&[CExpression]> {
        self.term.declared_arguments()
    }

    pub fn declared_parameter_types(&self) -> Option<&[CType]> {
        self.term.declared_parameter_types()
    }

    pub fn composite(
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    ) -> Self {
        Self::declared(
            ResourceFamily::Composite,
            access,
            name,
            arguments,
            parameter_types,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
        .expect("composite resource terms are valid by construction")
    }

    pub fn token(
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    ) -> Self {
        Self::declared(
            ResourceFamily::Token,
            access,
            name,
            arguments,
            parameter_types,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
        .expect("token resource terms are valid by construction")
    }

    pub fn with_role(mut self, role: CResourceTransferRole) -> Self {
        self.role = role;
        self
    }

    pub fn with_snapshot(mut self, snapshot: CResourceSnapshot) -> Self {
        self.snapshot = snapshot;
        self
    }

    fn validate(&self) -> Result<(), CResourceSpecError> {
        crate::kernel::primitives::resource_algebra::validate_resource_spec(self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    Condition(ConditionTerm),
    Bitvector32(Bitvector32Term),
    Integer(IntegerTerm),
    PointerOffset(PointerOffsetTerm),
    CValue(CValue),
    Sequence(SequenceTerm),
    Algebraic(AlgebraicTerm),
    CExpressionOutcome(CExpressionOutcome),
    CStatementOutcome(CStatementOutcome),
    CFunctionOutcome(CFunctionOutcome),
    CMemory(CMemory),
    CState(CState),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Proposition {
    Equal(Term, Term),
    ConditionIs(ConditionTerm, bool),
    Predicate {
        name: String,
        arguments: Vec<Term>,
    },
    CExpressionEvaluates {
        state: CState,
        expression: CExpression,
        outcome: CExpressionOutcome,
    },
    CConditionEvaluates {
        state: CState,
        condition: CExpression,
        outcome: CConditionOutcome,
    },
    CStatementExecutes {
        state: CState,
        statement: CStatement,
        outcome: CStatementOutcome,
    },
    /// An abstract verification transition. Unlike `CStatementExecutes`, this
    /// does not assert that the represented outcome is concretely reachable.
    CStatementVerifies {
        state: CState,
        statement: CStatement,
        outcome: CStatementOutcome,
    },
    CFunctionExecutes {
        state: CState,
        function: CFunction,
        arguments: Vec<CExpression>,
        outcome: CFunctionOutcome,
    },
    /// A return branch admitted by modular verification. This is conditional
    /// on the function returning and is not a termination or reachability
    /// theorem.
    CFunctionVerifies {
        state: CState,
        function: CFunction,
        arguments: Vec<CExpression>,
        outcome: CFunctionOutcome,
    },
    CFunctionSatisfiesSpecification {
        function: CFunction,
        specification: CFunctionSpecification,
    },
    /// The specification describes one allowed return branch and makes no
    /// claim that the branch is reachable or that the function terminates.
    CFunctionPartiallySatisfiesSpecification {
        function: CFunction,
        specification: CFunctionSpecification,
    },
    CMemoryLoads {
        memory: CMemory,
        pointer: Pointer,
        outcome: CExpressionOutcome,
    },
    CMemoryCanStore {
        memory: CMemory,
        pointer: Pointer,
        byte_width: u32,
    },
    CMemoryLoadable {
        memory: CMemory,
        base: Pointer,
        bytes: Bitvector32Term,
    },
    CMemoryDisjoint {
        left_base: Pointer,
        left_start: Bitvector32Term,
        left_end: Bitvector32Term,
        right_base: Pointer,
        right_start: Bitvector32Term,
        right_end: Bitvector32Term,
    },
    CResourceSeparate {
        left: CResource,
        right: CResource,
    },
    /// Internal carrier for an already-validated resource composition.
    /// PureFactContext store this as indexed kernel authority rather than as an
    /// ambient proposition visible to proof search.
    CResourceComposition(ResourceContext),
    CResourceContains {
        parent: CResource,
        child: CResource,
    },
    CMemoryMutatesOnly {
        before: CMemory,
        after: CMemory,
        pointers: Vec<Pointer>,
    },
    CMemoryEffectSummary {
        before: CMemory,
        after: CMemory,
        mutable_ranges: Vec<CMemoryRange>,
    },
    CHeapAllocationFreed {
        before: CMemory,
        after: CMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Not(Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    ForAll {
        var: Variable,
        sort: Sort,
        body: Box<Proposition>,
    },
    Exists {
        name: String,
        var: Variable,
        sort: Sort,
        body: Box<Proposition>,
    },
}

/// An abstract proven proposition produced by kernel axioms.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Theorem {
    pub(super) proposition: std::sync::Arc<Proposition>,
}

/// Kernel-issued authority for a closed pure theorem that may be used during
/// whole-contract certification. The private field prevents the Click layer
/// from promoting an arbitrary proposition or unrelated theorem object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedPureTheorem {
    pub(super) theorem: Theorem,
}

/// A local, symbolic contract-refinement problem opened by a pure theorem.
///
/// Construction is kernel-owned. The refining interface is either a verified
/// or explicitly external concrete function, or another exact named contract
/// fact for the same symbolic pointer. Both interfaces are instantiated with
/// the same fresh arguments. The surface proof may inspect the argument
/// bindings and entry state only to lower explicit logical case splits; it
/// cannot manufacture a refinement authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionContractRefinementContext {
    pub(super) contract: CFunctionContract,
    /// The implementation side of refinement is an interface judgment too;
    /// concrete body evidence is checked before this context is opened and is
    /// not needed to lower the symbolic relation.
    pub(super) function_interface: CFunctionContractInterface,
    pub(super) function_name: String,
    pub(super) pointer: CPointerValue,
    pub(super) source_contract: Option<CFunctionContract>,
    pub(super) argument_values: Vec<CValue>,
    pub(super) result_variable: Variable,
    pub(super) next_kernel_variable: u64,
}

/// Kernel-generated sufficient logical obligations for one contract relation.
/// The states and proposition cannot be supplied by the language layer.
pub struct CFunctionContractRefinementObligations {
    pub(super) entry: CState,
    pub(super) post: CState,
    pub(super) proposition: Proposition,
}

/// A proof tree produced by contextual proposition reasoning.
///
/// Smart reasoning may search for this tree. Check only checks the selected
/// rule and its explicit children; it never searches for an alternative proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PropositionDerivation {
    pub(super) conclusion: Proposition,
    pub(super) rule: PropositionDerivationRule,
}

/// One exact signed-order edge retained by an atomic derivation.
///
/// The edge is oriented from `lower` to `upper`; `strict` distinguishes `<`
/// from `<=`. Certificate consumers can write this ordered path directly
/// instead of rediscovering it from an unordered premise set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedOrderDerivationStep {
    pub(super) lower: Bitvector32Term,
    pub(super) upper: Bitvector32Term,
    pub(super) strict: bool,
    pub(super) premise: Proposition,
}

/// The base-alignment fact an atomic pointer-alignment decision rested on.
/// `None` means the base is a heap allocation, whose alignment is intrinsic
/// to the LP64 allocator profile and needs no context fact.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PointerAlignmentEvidence {
    pub(super) premise: Option<Proposition>,
}

/// The exact facts a pointer-word equality decision rested on: recorded
/// address forms of words, base alignments, tag bounds, and pointer
/// equalities. Checking the decision from exactly these facts re-derives
/// the same value.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PointerWordEvidence {
    pub(super) premises: Vec<Proposition>,
}

/// One exact ground-int32 equality edge retained in the orientation selected
/// by an atomic derivation. `premise` is the exact context proposition; the
/// source/target orientation may be the reverse of its written equality.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitvectorEqualityDerivationStep {
    pub(super) source: Bitvector32Term,
    pub(super) target: Bitvector32Term,
    pub(super) premise: Proposition,
}

/// Target-directed evidence that two pointer offsets are equal by structural
/// congruence and exact ground-int32 equality premises.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PointerOffsetCongruenceEvidence {
    Exact,
    ExactPremise(Box<Proposition>),
    Add {
        first: Box<PointerOffsetCongruenceEvidence>,
        second: Box<PointerOffsetCongruenceEvidence>,
        swapped: bool,
    },
    Int32Scaled {
        byte_width: i64,
        path: Vec<BitvectorEqualityDerivationStep>,
    },
    Int32ScaledDerived {
        byte_width: i64,
        equality: DirectBitvectorEqualityEvidence,
    },
    Int64Scaled {
        byte_width: i64,
        unsigned: bool,
        path: Vec<BitvectorEqualityDerivationStep>,
    },
    ElementIndex {
        byte_width: u32,
        path: Vec<BitvectorEqualityDerivationStep>,
    },
    ElementIndexDerived {
        byte_width: u32,
        equality: DirectBitvectorEqualityEvidence,
    },
}

/// A finite, target-directed equality path used inside retained pointer
/// congruence. Each variant names exact equality or order evidence; the
/// checker follows that path without proposition search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DirectBitvectorEqualityEvidence {
    AdditiveCancellation {
        left: Bitvector32Term,
        right: Bitvector32Term,
        equality: Box<DirectBitvectorEqualityEvidence>,
    },
    EqualSignedConstants {
        value: i64,
        left: SignedConstantEvidence,
        right: SignedConstantEvidence,
    },
    LeAndNotLt(Box<Int32LeAndNotLtEqualityEvidence>),
    GeAndNotGt(Box<Int32GeAndNotGtEqualityEvidence>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SignedConstantEvidence {
    Constant,
    SingletonBounds {
        variable: Variable,
        lower: IndexedSignedOrderBoundEvidence,
        upper: IndexedSignedOrderBoundEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IndexedSignedOrderBoundEvidence {
    pub(in crate::kernel) endpoint: Bitvector32Term,
    pub(in crate::kernel) other: Bitvector32Term,
    pub(in crate::kernel) strict: bool,
    pub(in crate::kernel) forward: bool,
    pub(in crate::kernel) source: Box<Proposition>,
}

/// Evidence that two load variables name one cell because their
/// registered origins have the same memory epoch and block and congruent
/// offsets. The original variables remain distinct context-free names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoadAddressCongruenceEvidence {
    pub(super) left_pointer: Pointer,
    pub(super) right_pointer: Pointer,
    pub(super) offset: PointerOffsetCongruenceEvidence,
}

/// The premises a retained evidence leaf names.
///
/// Evidence records propositions, never a context. A `PureFactContext`
/// carries every derived index and grows with the ambient proof state, so
/// embedding one makes a leaf's size a function of the whole proof rather
/// than of what it actually cited, and `context_premises` had to
/// materialize that index to answer at all. See the "Retained evidence
/// names premises, never a context" rule in `docs/internals/proof-objects.md`.
///
/// Checking a leaf rebuilds a context from exactly these propositions, so
/// the check can never consult more than the evidence names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RetainedPremises {
    propositions: std::sync::Arc<Vec<Proposition>>,
}

impl RetainedPremises {
    pub(crate) fn from_context(context: &PureFactContext) -> Self {
        Self {
            propositions: std::sync::Arc::new(context.pure_facts()),
        }
    }

    /// The propositions this leaf cites, in a deterministic order.
    pub(crate) fn named(&self) -> &[Proposition] {
        &self.propositions
    }

    /// A context holding exactly the cited propositions and nothing else.
    pub(crate) fn context(&self) -> PureFactContext {
        self.propositions
            .iter()
            .fold(PureFactContext::new(), |context, premise| {
                context.assume_proposition(premise.clone())
            })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PropositionDerivationRule {
    ContextFree,
    ContextualAtomic {
        premises: RetainedPremises,
        premises_id: u64,
        for_simp: bool,
        evidence: AtomicPropositionDerivationEvidence,
    },
    Explosion {
        premises: RetainedPremises,
    },
    And {
        left: Box<PropositionDerivation>,
        right: Box<PropositionDerivation>,
    },
    /// Constructor congruence: equal corresponding fields make two
    /// applications of the same constructor equal.
    AlgebraicConstructorCongruence {
        fields: Vec<PropositionDerivation>,
    },
    /// Constructor injectivity: an exact equality between two applications
    /// of one constructor entails equality of the selected fields.
    AlgebraicConstructorInjectivity {
        source: Proposition,
        field_index: usize,
    },
    OrLeft(Box<PropositionDerivation>),
    OrRight(Box<PropositionDerivation>),
    DoubleNegation(Box<PropositionDerivation>),
    Implies {
        antecedent: Proposition,
        body: Box<PropositionDerivation>,
    },
    ImpliesFalseAntecedent(Box<PropositionDerivation>),
    ForAllBody(Box<PropositionDerivation>),
    /// Prove an existential by selecting the bound variable from an exact
    /// existential fact and checking the target body under that witness's
    /// conjuncts.
    ExistsFromFact {
        source: Proposition,
        body: Box<PropositionDerivation>,
    },
    /// Prove an existential by selecting a free witness term and checking the
    /// substituted body against the current context.
    ExistsFromWitness {
        witness: Bitvector32Term,
        body: Box<PropositionDerivation>,
    },
    /// Prove an in-range one-byte loadability universal from one exact wider
    /// loadability range and the universal body's guard premises.
    ForAllLoadableRange {
        source: Proposition,
    },
    /// Prove an existential one-byte loadability fact by selecting the
    /// constant zero index from one exact wider range.
    ExistsLoadableRange {
        source: Proposition,
        witness: Bitvector32Term,
    },
    FiniteForAll {
        instances: Vec<PropositionDerivation>,
    },
    /// Substitute a variable pinned to one signed value by two exact order
    /// bounds, then check the proof of the resulting proposition.
    SingletonSubstitution {
        variable: Variable,
        value: i64,
        equality: DirectBitvectorEqualityEvidence,
        body: Box<PropositionDerivation>,
    },
    DisjunctionCases {
        disjunction: Proposition,
        cases: Vec<PropositionDerivation>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32IncrementBoundsEvidence {
    pub(super) lower_bound: SignedOrderDerivationStep,
    pub(super) upper_bound: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32PredecessorUpperBoundEvidence {
    pub(super) nonnegative: SignedOrderDerivationStep,
    pub(super) upper_bound: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Int32OneLeEvidence {
    Direct(Box<SignedOrderDerivationStep>),
    EqualOne(Vec<BitvectorEqualityDerivationStep>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32NonnegativeAddWithinMaxEvidence {
    pub(super) amount_nonnegative: SignedOrderDerivationStep,
    pub(super) within_headroom: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32NonnegativeSubtractWithinValueEvidence {
    pub(super) amount_nonnegative: SignedOrderDerivationStep,
    pub(super) within_value: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32LeAndNotLtEqualityEvidence {
    pub(super) less_equal: Proposition,
    pub(super) not_less_than: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32GeAndNotGtEqualityEvidence {
    pub(super) greater_equal: Proposition,
    pub(super) not_greater_than: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32LeAndNeqStrictEvidence {
    pub(super) less_equal: Proposition,
    pub(super) not_equal: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForallInt32InstantiationEvidence {
    pub(crate) quantified: Proposition,
    pub(crate) argument: Bitvector32Term,
    pub(crate) guard_premises: Vec<Proposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AtomicPropositionDerivationEvidence {
    MemoryDag(Box<AtomicMemoryLoadEqualityEvidence>),
    LoadAddressCongruence(Box<LoadAddressCongruenceEvidence>),
    PointerOffsetMemoryDag(Box<PointerOffsetEqualityEvidence>),
    BitvectorEqualityPath(Vec<BitvectorEqualityDerivationStep>),
    ForallInt32Instantiation(Box<ForallInt32InstantiationEvidence>),
    SignedOrderPath(Vec<SignedOrderDerivationStep>),
    Int32IncrementUpperBound(Box<SignedOrderDerivationStep>),
    Int32IncrementConstantUpperBound(Box<SignedOrderDerivationStep>),
    Int32IncrementStrictlyIncreases(Box<SignedOrderDerivationStep>),
    Int32IncrementBelowMaxIsDefined(Box<SignedOrderDerivationStep>),
    Int32OnePlusBelowMaxIsDefined(Box<SignedOrderDerivationStep>),
    Int32OnePlusStrictlyIncreases(Box<SignedOrderDerivationStep>),
    Int32NonnegativeAddWithinMaxIsDefined(Box<Int32NonnegativeAddWithinMaxEvidence>),
    Int32NonnegativeSubtractWithinValueIsDefined(Box<Int32NonnegativeSubtractWithinValueEvidence>),
    Int32IncrementLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementGreaterEqualLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementStrictGreaterLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementStrictGreaterFromStrictLower(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementPreservesOrder(Box<Int32IncrementBoundsEvidence>),
    Int32PositiveIsNonnegative(Box<SignedOrderDerivationStep>),
    Int32StrictlyPositiveIsNonnegative(Box<SignedOrderDerivationStep>),
    Int32SuccessorLeImpliesLt(Box<SignedOrderDerivationStep>),
    Int32ConstantLowerBoundWeakening(Box<SignedOrderDerivationStep>),
    Int32NegatedStrictSuccessorBound(Box<SignedOrderDerivationStep>),
    Int32PositivePredecessorIsNonnegative(Box<SignedOrderDerivationStep>),
    Int32PositivePredecessorStrictlyDecreases(Box<SignedOrderDerivationStep>),
    Int32NonnegativePredecessorUpperBound(Box<Int32PredecessorUpperBoundEvidence>),
    Int32OneLePredecessorIsNonnegative(Int32OneLeEvidence),
    Int32OneLePredecessorStrictlyDecreases(Int32OneLeEvidence),
    Int32EqualOnePredecessorIsZero(Vec<BitvectorEqualityDerivationStep>),
    Int32LeAndNeqImpliesStrict(Box<Int32LeAndNeqStrictEvidence>),
    Int32LeAndNotLtImpliesEquality(Box<Int32LeAndNotLtEqualityEvidence>),
    Int32GeAndNotGtImpliesEquality(Box<Int32GeAndNotGtEqualityEvidence>),
    PointerAlignment(Box<PointerAlignmentEvidence>),
    PointerWord(Box<PointerWordEvidence>),
    Legacy,
}

#[derive(Clone, Debug, Default)]
pub struct PureFactContext {
    /// True 64-bit equalities as an undirected adjacency map, derived
    /// incrementally from `condition_facts`. Unchanged branches share it;
    /// inserting an equality updates only its two endpoints.
    pub(super) bitvector64_equality_facts: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<Bitvector32Term, ConditionTerm>,
    >,
    pub(super) condition_facts: crate::persistent::PersistentMap<ConditionTerm, bool>,
    /// Exact signed-order bounds keyed by either endpoint — under the term
    /// the fact wrote and, when different, its canonical form as an alias.
    /// Each entry carries the fact's own endpoint term first, so evidence
    /// found through the alias can still cite the exact fact. Counts
    /// preserve equivalent condition terms when one source fact is replaced.
    pub(super) signed_order_bounds: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<(Bitvector32Term, Bitvector32Term, bool, bool), usize>,
    >,
    /// Condition facts containing a memory-load atom, indexed by the loaded
    /// pointer's snapshot-blind structural fingerprint. This is derived from
    /// `condition_facts`; it narrows snapshot-aware load-form checks
    /// without deciding them.
    pub(super) memory_load_condition_facts:
        std::sync::Arc<std::sync::OnceLock<BTreeMap<(PointerBlock, u64), BTreeSet<ConditionTerm>>>>,
    /// True bitvector and int32-scaled pointer-offset equalities, indexed as
    /// an undirected adjacency graph whose edges retain one exact source
    /// proposition. Memory-load vertices use their
    /// assumption-free canonical memory-load term. Derived lazily from
    /// `condition_facts` and shared by unchanged clones.
    pub(super) bitvector_equality_facts: std::sync::Arc<
        std::sync::OnceLock<BTreeMap<Bitvector32Term, BTreeMap<Bitvector32Term, Proposition>>>,
    >,
    pub(super) prop_facts: std::sync::Arc<BTreeSet<Proposition>>,
    /// Alpha/load identity index for propositions that may be stated as a
    /// call requirement.  The key retains memory epochs and canonicalizes
    /// only binders; the persistent buckets keep updates local to one key.
    pub(super) stated_proposition_index: crate::persistent::PersistentMap<
        crate::kernel::proof::PropositionIdentityKey,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Nominal function-contract witnesses keyed by the exact pointer value.
    /// This keeps indirect-call lookup proportional to contracts explicitly
    /// known for that pointer, never to project-wide declarations.
    pub(super) function_contract_facts:
        std::sync::Arc<BTreeMap<Pointer, BTreeMap<String, Proposition>>>,
    /// Exact equalities between two applications of one algebraic
    /// constructor, indexed by each field equality they entail. Both levels
    /// are persistent so adding one proof fact changes logarithmically many
    /// nodes instead of cloning an ambient fact table.
    pub(super) algebraic_constructor_field_equalities: crate::persistent::PersistentMap<
        Proposition,
        crate::persistent::PersistentMap<(Proposition, usize), ()>,
    >,
    /// Exact equalities between distinct checked constructors. Any such fact
    /// makes the context inconsistent by constructor disjointness.
    pub(super) algebraic_constructor_conflicts: crate::persistent::PersistentMap<Proposition, ()>,
    /// Direct constructor evidence indexed by the symbolic value it describes.
    pub(super) algebraic_variable_constructors: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<Proposition, AlgebraicTerm>,
    >,
    /// Exact disjunctive proposition facts. This derived index keeps bounded
    /// case search proportional to possible case splits rather than every
    /// unrelated proposition in the context.
    pub(super) disjunction_facts: std::sync::Arc<BTreeSet<Proposition>>,
    pub(super) resource_compositions: std::sync::Arc<BTreeSet<ResourceContext>>,
    pub(super) memory_loadable_facts: std::sync::Arc<BTreeMap<PointerBlock, BTreeSet<Proposition>>>,
    pub(super) memory_loadable_shape_facts:
        std::sync::Arc<std::sync::OnceLock<BTreeMap<(PointerBlock, u64), BTreeSet<Proposition>>>>,
    pub(super) memory_separation_facts: std::sync::Arc<
        BTreeMap<(PointerBlock, PointerBlock), Vec<(Proposition, CMemoryRange, CMemoryRange)>>,
    >,
    /// Separation facts the block-pair index cannot serve: at least one
    /// side is a non-memory resource whose containment may still entail a
    /// memory separation through its body. Kept small and scanned
    /// linearly; memory-memory facts live in the index above instead.
    pub(super) nonmemory_separation_facts: std::sync::Arc<Vec<Proposition>>,
    /// Same-block separation candidates projected from the compact resource
    /// compositions, keyed and maintained incrementally like
    /// `memory_separation_facts`. Two owned facts of one valid composition
    /// are separate by the composition law, so these entries carry the same
    /// authority the formerly materialized pair propositions did, without
    /// living in any ambient proposition set. Each projection retains its
    /// owning shared context so checked consumers can name the logical
    /// authority without scanning all ambient compositions.
    pub(super) composition_separation_facts: std::sync::Arc<
        BTreeMap<
            (PointerBlock, PointerBlock),
            Vec<(Proposition, CMemoryRange, CMemoryRange, ResourceContext)>,
        >,
    >,
    pub(super) content_fingerprint: u64,
    pub(super) defer_non_exact_loadability_obligations: bool,
    pub(super) defer_non_exact_condition_reasoning: bool,
    pub(super) prefer_symbolic_external_loads: bool,
    pub(super) force_symbolic_external_loads: bool,
    pub(super) allow_symbolic_contract_loads: bool,
    pub(super) require_owned_expression_loads: bool,
    pub(super) transport_memory_load_condition_facts: bool,
    /// Proof-side specification lowering keeps an unresolved load as one
    /// symbolic term. Executable invariant checking leaves this false so it
    /// can still enumerate alias cases.
    pub(super) keep_spec_loads_symbolic: bool,
}

impl PartialEq for PureFactContext {
    fn eq(&self, other: &Self) -> bool {
        self.content_fingerprint == other.content_fingerprint
            && self.condition_facts == other.condition_facts
            && self.prop_facts == other.prop_facts
            && self.resource_compositions == other.resource_compositions
            && self.defer_non_exact_loadability_obligations
                == other.defer_non_exact_loadability_obligations
            && self.defer_non_exact_condition_reasoning == other.defer_non_exact_condition_reasoning
            && self.prefer_symbolic_external_loads == other.prefer_symbolic_external_loads
            && self.force_symbolic_external_loads == other.force_symbolic_external_loads
            && self.allow_symbolic_contract_loads == other.allow_symbolic_contract_loads
            && self.transport_memory_load_condition_facts
                == other.transport_memory_load_condition_facts
            && self.keep_spec_loads_symbolic == other.keep_spec_loads_symbolic
    }
}

impl Eq for PureFactContext {}

impl std::hash::Hash for PureFactContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_fingerprint);
    }
}

#[derive(Clone, Debug)]
pub struct ProofObligation {
    pub(super) proposition: Proposition,
    pub(super) context: Option<String>,
    pub(super) assumable: bool,
    /// Source identity for a required call precondition, when this
    /// obligation was emitted while applying a selected callee contract.
    /// This is planning metadata only and is excluded from obligation
    /// equality, hashing, and ordering just like lowering introductions.
    pub(super) call_requirement_site: Option<std::sync::Arc<CallRequirementSource>>,
    /// The head chain the lowering that built `proposition` recorded for it,
    /// outermost first, when the kernel built this obligation from a lowered
    /// specification proposition.
    ///
    /// Lowering wraps an obligation in `Implies` nodes that no Surface
    /// connective wrote. A consumer that introduces the head of this
    /// obligation reads the chain instead of guessing from the shape the
    /// written syntax happens to share. `None` is the unrecorded state: an
    /// obligation the kernel built with no lowering of its own.
    pub(super) introductions: Option<Arc<super::LoweringIntroductions>>,
}

/// Provenance describes the proposition; it never distinguishes two
/// obligations. Comparison, ordering, and hashing therefore read the
/// checked fields only, so an obligation carrying a recorded chain still
/// deduplicates against the same obligation built without one.
impl PartialEq for ProofObligation {
    fn eq(&self, other: &Self) -> bool {
        self.proposition == other.proposition
            && self.context == other.context
            && self.assumable == other.assumable
    }
}

impl Eq for ProofObligation {}

impl Hash for ProofObligation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.proposition.hash(state);
        self.context.hash(state);
        self.assumable.hash(state);
    }
}

impl Ord for ProofObligation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.proposition
            .cmp(&other.proposition)
            .then_with(|| self.context.cmp(&other.context))
            .then_with(|| self.assumable.cmp(&other.assumable))
    }
}

impl PartialOrd for ProofObligation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ExecutionPureFact {
    pub(super) proposition: Proposition,
    pub(super) public: bool,
    pub(super) certified: bool,
    pub(super) certified_store: Option<CertifiedMemoryStore>,
    pub(super) transport: Option<CertifiedExecutionFactTransport>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CertifiedExecutionFactTransport {
    pub(super) source: Proposition,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CertifiedMemoryStore {
    pub(super) before: CMemory,
    pub(super) after: CMemory,
    pub(super) pointer: Pointer,
    pub(super) value: CValue,
    pub(super) authorized_range: Option<CMemoryRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    pub(super) paths: Vec<SymbolicCExecutionPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

/// One complete path set contract certification may judge a claim over: a
/// checked execution reused at the contract's entry, the union of two
/// complementary entry partitions, or the kernel's own execution when no
/// artifact was supplied. Its paths jointly cover the function from the
/// entry they name, so a claim that holds on every one of them holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CContractPathSet {
    pub(super) paths: Vec<SymbolicCExecutionPath>,
    /// The caller state the reused artifact's proof ran at, when its paths
    /// were rebased onto this contract's caller state. A claim the proof
    /// completed at that state certifies the rebased path: the rebase
    /// checked the two entry representations definitionally equal.
    pub(super) completion_origin_state: Option<CState>,
}

/// A complete function frontier produced from only the exact function's
/// contract entry state and requirements.
///
/// Unlike [`SymbolicCExecution`], this type is accepted as evidence when
/// certifying an opaque function rule. Its fields are kernel-private so callers
/// cannot turn an execution performed under arbitrary assumptions into
/// contract evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionContractExecution {
    /// One entry per resource-guard case of the contract, each listing every
    /// path set available for that case. A claim holds when, in every case,
    /// one path set certifies it on all of its paths: each set is a complete
    /// execution of the function under the case, so any one is authority for
    /// it. The sets differ only in how the proofs that produced them
    /// structured the paths (a proof that joins two arms publishes the
    /// joined path; another publishes each arm), and a claim completed on
    /// one proof's outcome is matched against that proof's paths.
    pub(super) cases: Vec<Vec<CContractPathSet>>,
    /// Why certification produced no paths: either no supplied checked
    /// artifact could be reused, or the contract entry context itself could
    /// not be built. Callers report it; it carries no authority.
    pub(super) reuse_diagnostic: Option<String>,
    pub(super) checked_call_events: super::proof::CheckedCallEvents,
}

/// A kernel-created record of one exact whole-function execution judgment.
///
/// Callers may retain and present this artifact, but cannot manufacture or
/// alter its execution metadata. Contract certification revalidates the
/// boundary assumptions before reusing its checked frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCheckedFunctionExecution {
    pub(super) state: CState,
    pub(super) function: CFunction,
    pub(super) arguments: Vec<CExpression>,
    pub(super) assumptions: PureFactContext,
    pub(super) environment: CExecutionEnvironment,
    pub(super) execution_semantics: CExecutionSemantics,
    pub(super) mode: CFunctionContractExecutionMode,
    pub(super) execution: SymbolicCExecution,
    /// Original contract caller state when a kernel-checked proof entered C
    /// execution through a definitionally equal resource representation.
    pub(super) entry_representation_origin: Option<CState>,
    pub(super) checked_call_events: super::proof::CheckedCallEvents,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CFunctionContractExecutionMode {
    VerifyLoops,
    ExecuteLoops,
}

impl CFunctionContractExecution {
    /// An empty certification that carries why it produced no paths. A
    /// diagnostic is not authority: the result is still empty and certifies
    /// nothing.
    pub(crate) fn failed(diagnostic: String) -> Self {
        Self {
            cases: Vec::new(),
            reuse_diagnostic: Some(diagnostic),
            checked_call_events: Default::default(),
        }
    }

    /// Every path across every case and path set.
    pub fn path_count(&self) -> usize {
        self.cases.iter().flatten().map(|set| set.paths.len()).sum()
    }

    /// Whether every resource-guard case has a path set to judge claims
    /// over.
    pub(crate) fn is_complete(&self) -> bool {
        !self.cases.is_empty()
            && self
                .cases
                .iter()
                .all(|alternatives| !alternatives.is_empty())
    }

    pub(crate) fn cases(&self) -> &[Vec<CContractPathSet>] {
        &self.cases
    }

    /// Why certification produced no paths although checked artifacts were
    /// supplied: the premise kind or entry-state component that blocked
    /// reuse.
    pub fn reuse_diagnostic(&self) -> Option<&str> {
        self.reuse_diagnostic.as_deref()
    }
}

impl CCheckedFunctionExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        self.execution.paths()
    }

    /// Whether two checked executions are the same, naming the first
    /// difference otherwise. Path theorems are compared premise by premise
    /// rather than through the derived equality, whose recursion over a long
    /// implication chain can exhaust a verification thread's stack.
    pub fn agrees_with(&self, other: &Self) -> Result<(), String> {
        fn same_proposition(left: &Proposition, right: &Proposition) -> Result<(), String> {
            let (mut left, mut right) = (left, right);
            let mut index = 0;
            loop {
                match (left, right) {
                    (
                        Proposition::Implies(left_premise, left_body),
                        Proposition::Implies(right_premise, right_body),
                    ) => {
                        if left_premise != right_premise {
                            return Err(format!(
                                "premise {index} differs: {left_premise:?} versus {right_premise:?}"
                            ));
                        }
                        index += 1;
                        left = left_body;
                        right = right_body;
                    }
                    (Proposition::Implies(..), _) | (_, Proposition::Implies(..)) => {
                        return Err(format!(
                            "the theorems have different premise counts at {index}"
                        ));
                    }
                    (left, right) => {
                        return (left == right)
                            .then_some(())
                            .ok_or_else(|| "the theorem bodies differ".to_string());
                    }
                }
            }
        }
        if self.state != other.state {
            return Err("the caller states differ".to_string());
        }
        if self.function != other.function {
            return Err("the functions differ".to_string());
        }
        if self.arguments != other.arguments {
            return Err("the arguments differ".to_string());
        }
        if self.assumptions != other.assumptions {
            return Err("the assumptions differ".to_string());
        }
        if self.environment != other.environment {
            return Err("the environments differ".to_string());
        }
        if self.execution_semantics != other.execution_semantics || self.mode != other.mode {
            return Err("the execution semantics or modes differ".to_string());
        }
        if self.execution.limit != other.execution.limit {
            return Err("the limits differ".to_string());
        }
        if self.entry_representation_origin != other.entry_representation_origin {
            return Err(format!(
                "the entry representation origins differ: {} versus {}",
                self.entry_representation_origin.is_some(),
                other.entry_representation_origin.is_some()
            ));
        }
        if self.execution.paths.len() != other.execution.paths.len() {
            return Err(format!(
                "path counts differ: {} versus {}",
                self.execution.paths.len(),
                other.execution.paths.len()
            ));
        }
        for (index, (left, right)) in self
            .execution
            .paths
            .iter()
            .zip(&other.execution.paths)
            .enumerate()
        {
            if left.assumptions != right.assumptions {
                return Err(format!("path {index}: the assumptions differ"));
            }
            if left.facts != right.facts {
                let missing = right
                    .facts
                    .iter()
                    .filter(|fact| !left.facts.contains(fact))
                    .map(|fact| format!("{:?}", fact.proposition()))
                    .collect::<Vec<_>>();
                let extra = left
                    .facts
                    .iter()
                    .filter(|fact| !right.facts.contains(fact))
                    .map(|fact| format!("{:?}", fact.proposition()))
                    .collect::<Vec<_>>();
                return Err(format!(
                    "path {index}: the facts differ; missing {missing:?}, extra {extra:?}"
                ));
            }
            if left.effect_facts != right.effect_facts {
                return Err(format!("path {index}: the effect facts differ"));
            }
            if left.obligations != right.obligations {
                return Err(format!("path {index}: the obligations differ"));
            }
            same_proposition(left.theorem.proposition(), right.theorem.proposition())
                .map_err(|difference| format!("path {index}: {difference}"))?;
        }
        Ok(())
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.execution.limit()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    pub(super) assumptions: PureFactContext,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) effect_facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

/// An untrusted collection of checked function outcomes.
///
/// Candidates deliberately carry no [`Theorem`]. They become useful as proof
/// evidence only after a checked kernel execution independently reproduces the
/// same complete path frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionExecutionCandidates {
    pub(super) state: CState,
    pub(super) function: CFunction,
    pub(super) arguments: Vec<CExpression>,
    pub(super) paths: Vec<CFunctionExecutionCandidate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionExecutionCandidate {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) effect_facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCConditionEvaluation {
    pub(super) paths: Vec<SymbolicCConditionEvaluationPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCConditionEvaluationPath {
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CExpressionPath {
    pub(super) outcome: CExpressionOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CLValuePath {
    pub(super) outcome: CLValueOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CStatementExecutionPath {
    pub(super) outcome: CStatementOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CFunctionPath {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CArgumentsPath {
    pub(super) values: Vec<CValue>,
    pub(super) outcome: Option<CFunctionOutcome>,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct KernelVariableGenerator {
    pub(super) next: u64,
    reserved: BTreeSet<Variable>,
    shared_reserved: Option<Arc<BTreeSet<Variable>>>,
}

impl KernelVariableGenerator {
    /// Build the deterministic fresh-name stream used by both planning and
    /// certificate validation. Given the same lower bound and reserved set, the
    /// first available identifier and every successor are identical; callers
    /// carry `next` across proof steps so a check never relies on accidental
    /// equality with an independently chosen symbolic name.
    pub(super) fn fresh_for(lower_bound: u64, existing: BTreeSet<Variable>) -> Self {
        Self {
            next: lower_bound,
            reserved: existing,
            shared_reserved: None,
        }
    }

    pub(super) fn fresh_for_with_shared_reservations(
        lower_bound: u64,
        existing: BTreeSet<Variable>,
        shared_reserved: Arc<BTreeSet<Variable>>,
    ) -> Self {
        Self {
            next: lower_bound,
            reserved: existing,
            shared_reserved: Some(shared_reserved),
        }
    }

    pub(super) fn next(&mut self) -> Variable {
        let start = self.next;
        loop {
            let variable = Variable(self.next);
            self.next = self.next.wrapping_add(1);
            let shared_contains = self
                .shared_reserved
                .as_ref()
                .is_some_and(|reserved| reserved.contains(&variable));
            if !shared_contains && self.reserved.insert(variable) {
                return variable;
            }
            assert!(
                self.next != start,
                "all symbolic variable identifiers are already reserved"
            );
        }
    }
}
