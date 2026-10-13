//! The arithmetic shape of a [`Bitvector32Term`]: which operator a node
//! applies and to which operands. Traversals that rebuild or describe every
//! node keep their own arms for the variants they treat specially and handle
//! the uniform arithmetic variants through this split and its rebuild.

use super::*;

/// A two-operand arithmetic [`Bitvector32Term`] operator.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum BitvectorBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    UnsignedDivide,
    Remainder,
    UnsignedRemainder,
    ShiftLeft,
    ArithmeticShiftRight,
    LogicalShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    Int64Add,
    Int64Subtract,
    Int64Multiply,
    Int64Divide,
    Int64Remainder,
    Int64ShiftLeft,
    Int64ArithmeticShiftRight,
    Int64BitwiseAnd,
    Int64BitwiseOr,
    Int64BitwiseXor,
    UInt64Add,
    UInt64Subtract,
    UInt64Multiply,
    UInt64Divide,
    UInt64Remainder,
    UInt64ShiftLeft,
    UInt64LogicalShiftRight,
    UInt64BitwiseAnd,
    UInt64BitwiseOr,
    UInt64BitwiseXor,
    Float32(CFloatBinaryOperator),
    Float64(CFloatBinaryOperator),
}

/// A one-operand arithmetic [`Bitvector32Term`] operator or conversion.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum BitvectorUnaryOp {
    BitwiseNot,
    Int64BitwiseNot,
    UInt64BitwiseNot,
    Int64From32,
    UInt64From32,
    UInt32From64,
    Int64FromUInt32,
    UInt64FromInt32,
    UInt64FromInt64,
    Float32Negate,
    Float64Negate,
    MachineIntegerCast {
        source: MachineIntegerType,
        destination: MachineIntegerType,
    },
}

impl Bitvector32Term {
    /// The operator and operands of a two-operand arithmetic node, or `None`
    /// for every other variant.
    pub(crate) fn as_binary(&self) -> Option<(BitvectorBinaryOp, &Self, &Self)> {
        match self {
            Self::Add(left, right) => Some((BitvectorBinaryOp::Add, left, right)),
            Self::Subtract(left, right) => Some((BitvectorBinaryOp::Subtract, left, right)),
            Self::Multiply(left, right) => Some((BitvectorBinaryOp::Multiply, left, right)),
            Self::Divide(left, right) => Some((BitvectorBinaryOp::Divide, left, right)),
            Self::UnsignedDivide(left, right) => {
                Some((BitvectorBinaryOp::UnsignedDivide, left, right))
            }
            Self::Remainder(left, right) => Some((BitvectorBinaryOp::Remainder, left, right)),
            Self::UnsignedRemainder(left, right) => {
                Some((BitvectorBinaryOp::UnsignedRemainder, left, right))
            }
            Self::ShiftLeft(left, right) => Some((BitvectorBinaryOp::ShiftLeft, left, right)),
            Self::ArithmeticShiftRight(left, right) => {
                Some((BitvectorBinaryOp::ArithmeticShiftRight, left, right))
            }
            Self::LogicalShiftRight(left, right) => {
                Some((BitvectorBinaryOp::LogicalShiftRight, left, right))
            }
            Self::BitwiseAnd(left, right) => Some((BitvectorBinaryOp::BitwiseAnd, left, right)),
            Self::BitwiseOr(left, right) => Some((BitvectorBinaryOp::BitwiseOr, left, right)),
            Self::BitwiseXor(left, right) => Some((BitvectorBinaryOp::BitwiseXor, left, right)),
            Self::Int64Add(left, right) => Some((BitvectorBinaryOp::Int64Add, left, right)),
            Self::Int64Subtract(left, right) => {
                Some((BitvectorBinaryOp::Int64Subtract, left, right))
            }
            Self::Int64Multiply(left, right) => {
                Some((BitvectorBinaryOp::Int64Multiply, left, right))
            }
            Self::Int64Divide(left, right) => Some((BitvectorBinaryOp::Int64Divide, left, right)),
            Self::Int64Remainder(left, right) => {
                Some((BitvectorBinaryOp::Int64Remainder, left, right))
            }
            Self::Int64ShiftLeft(left, right) => {
                Some((BitvectorBinaryOp::Int64ShiftLeft, left, right))
            }
            Self::Int64ArithmeticShiftRight(left, right) => {
                Some((BitvectorBinaryOp::Int64ArithmeticShiftRight, left, right))
            }
            Self::Int64BitwiseAnd(left, right) => {
                Some((BitvectorBinaryOp::Int64BitwiseAnd, left, right))
            }
            Self::Int64BitwiseOr(left, right) => {
                Some((BitvectorBinaryOp::Int64BitwiseOr, left, right))
            }
            Self::Int64BitwiseXor(left, right) => {
                Some((BitvectorBinaryOp::Int64BitwiseXor, left, right))
            }
            Self::UInt64Add(left, right) => Some((BitvectorBinaryOp::UInt64Add, left, right)),
            Self::UInt64Subtract(left, right) => {
                Some((BitvectorBinaryOp::UInt64Subtract, left, right))
            }
            Self::UInt64Multiply(left, right) => {
                Some((BitvectorBinaryOp::UInt64Multiply, left, right))
            }
            Self::UInt64Divide(left, right) => Some((BitvectorBinaryOp::UInt64Divide, left, right)),
            Self::UInt64Remainder(left, right) => {
                Some((BitvectorBinaryOp::UInt64Remainder, left, right))
            }
            Self::UInt64ShiftLeft(left, right) => {
                Some((BitvectorBinaryOp::UInt64ShiftLeft, left, right))
            }
            Self::UInt64LogicalShiftRight(left, right) => {
                Some((BitvectorBinaryOp::UInt64LogicalShiftRight, left, right))
            }
            Self::UInt64BitwiseAnd(left, right) => {
                Some((BitvectorBinaryOp::UInt64BitwiseAnd, left, right))
            }
            Self::UInt64BitwiseOr(left, right) => {
                Some((BitvectorBinaryOp::UInt64BitwiseOr, left, right))
            }
            Self::UInt64BitwiseXor(left, right) => {
                Some((BitvectorBinaryOp::UInt64BitwiseXor, left, right))
            }
            Self::Float32Binary {
                operator,
                left,
                right,
            } => Some((BitvectorBinaryOp::Float32(*operator), left, right)),
            Self::Float64Binary {
                operator,
                left,
                right,
            } => Some((BitvectorBinaryOp::Float64(*operator), left, right)),
            Self::Constant(_)
            | Self::Int64Constant(_)
            | Self::UInt64Constant(_)
            | Self::MachineIntegerConstant(_)
            | Self::Variable(_)
            | Self::If { .. }
            | Self::RangeFold { .. }
            | Self::PureFunctionApplication { .. }
            | Self::ClickFunctionApplication { .. }
            | Self::AlgebraicMatch { .. }
            | Self::MemoryLoad(..)
            | Self::PointerAddress(_)
            | Self::IntegerToMachine { .. }
            | Self::BitwiseNot(_)
            | Self::Int64BitwiseNot(_)
            | Self::UInt64BitwiseNot(_)
            | Self::Int64From32(_)
            | Self::UInt64From32(_)
            | Self::UInt32From64(_)
            | Self::Int64FromUInt32(_)
            | Self::UInt64FromInt32(_)
            | Self::UInt64FromInt64(_)
            | Self::Float32Negate(_)
            | Self::Float64Negate(_)
            | Self::MachineIntegerCast { .. } => None,
        }
    }

    /// The operator and operand of a one-operand arithmetic node or
    /// conversion, or `None` for every other variant.
    pub(crate) fn as_unary(&self) -> Option<(BitvectorUnaryOp, &Self)> {
        match self {
            Self::BitwiseNot(value) => Some((BitvectorUnaryOp::BitwiseNot, value)),
            Self::Int64BitwiseNot(value) => Some((BitvectorUnaryOp::Int64BitwiseNot, value)),
            Self::UInt64BitwiseNot(value) => Some((BitvectorUnaryOp::UInt64BitwiseNot, value)),
            Self::Int64From32(value) => Some((BitvectorUnaryOp::Int64From32, value)),
            Self::UInt64From32(value) => Some((BitvectorUnaryOp::UInt64From32, value)),
            Self::UInt32From64(value) => Some((BitvectorUnaryOp::UInt32From64, value)),
            Self::Int64FromUInt32(value) => Some((BitvectorUnaryOp::Int64FromUInt32, value)),
            Self::UInt64FromInt32(value) => Some((BitvectorUnaryOp::UInt64FromInt32, value)),
            Self::UInt64FromInt64(value) => Some((BitvectorUnaryOp::UInt64FromInt64, value)),
            Self::Float32Negate(value) => Some((BitvectorUnaryOp::Float32Negate, value)),
            Self::Float64Negate(value) => Some((BitvectorUnaryOp::Float64Negate, value)),
            Self::MachineIntegerCast {
                value,
                source,
                destination,
            } => Some((
                BitvectorUnaryOp::MachineIntegerCast {
                    source: *source,
                    destination: *destination,
                },
                value,
            )),
            Self::Constant(_)
            | Self::Int64Constant(_)
            | Self::UInt64Constant(_)
            | Self::MachineIntegerConstant(_)
            | Self::Variable(_)
            | Self::If { .. }
            | Self::RangeFold { .. }
            | Self::PureFunctionApplication { .. }
            | Self::ClickFunctionApplication { .. }
            | Self::AlgebraicMatch { .. }
            | Self::MemoryLoad(..)
            | Self::PointerAddress(_)
            | Self::IntegerToMachine { .. }
            | crate::kernel::binary_machine_term!(_, _)
            | Self::Float32Binary { .. }
            | Self::Float64Binary { .. } => None,
        }
    }
}

impl BitvectorBinaryOp {
    /// The C spelling of the operator. Signed and unsigned forms of one
    /// operation share a spelling.
    pub(crate) fn c_symbol(self) -> &'static str {
        match self {
            Self::Add
            | Self::Int64Add
            | Self::UInt64Add
            | Self::Float32(CFloatBinaryOperator::Add)
            | Self::Float64(CFloatBinaryOperator::Add) => "+",
            Self::Subtract
            | Self::Int64Subtract
            | Self::UInt64Subtract
            | Self::Float32(CFloatBinaryOperator::Subtract)
            | Self::Float64(CFloatBinaryOperator::Subtract) => "-",
            Self::Multiply
            | Self::Int64Multiply
            | Self::UInt64Multiply
            | Self::Float32(CFloatBinaryOperator::Multiply)
            | Self::Float64(CFloatBinaryOperator::Multiply) => "*",
            Self::Divide
            | Self::UnsignedDivide
            | Self::Int64Divide
            | Self::UInt64Divide
            | Self::Float32(CFloatBinaryOperator::Divide)
            | Self::Float64(CFloatBinaryOperator::Divide) => "/",
            Self::Remainder
            | Self::UnsignedRemainder
            | Self::Int64Remainder
            | Self::UInt64Remainder => "%",
            Self::ShiftLeft | Self::Int64ShiftLeft | Self::UInt64ShiftLeft => "<<",
            Self::ArithmeticShiftRight
            | Self::LogicalShiftRight
            | Self::Int64ArithmeticShiftRight
            | Self::UInt64LogicalShiftRight => ">>",
            Self::BitwiseAnd | Self::Int64BitwiseAnd | Self::UInt64BitwiseAnd => "&",
            Self::BitwiseOr | Self::Int64BitwiseOr | Self::UInt64BitwiseOr => "|",
            Self::BitwiseXor | Self::Int64BitwiseXor | Self::UInt64BitwiseXor => "^",
        }
    }

    /// Whether the operator is a float operation.
    pub(crate) fn is_float(self) -> bool {
        matches!(self, Self::Float32(_) | Self::Float64(_))
    }

    /// Whether the operator is one of the original 32-bit word operators.
    /// Some traversals rebuild exactly these as bare nodes.
    pub(crate) fn is_bitvector32(self) -> bool {
        matches!(
            self,
            Self::Add
                | Self::Subtract
                | Self::Multiply
                | Self::Divide
                | Self::UnsignedDivide
                | Self::Remainder
                | Self::UnsignedRemainder
                | Self::ShiftLeft
                | Self::ArithmeticShiftRight
                | Self::LogicalShiftRight
                | Self::BitwiseAnd
                | Self::BitwiseOr
                | Self::BitwiseXor
        )
    }

    /// Applies the operator through its smart constructor.
    pub(crate) fn build(self, left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
        match self {
            Self::Add => Bitvector32Term::add(left, right),
            Self::Subtract => Bitvector32Term::subtract(left, right),
            Self::Multiply => Bitvector32Term::multiply(left, right),
            Self::Divide => Bitvector32Term::divide(left, right),
            Self::UnsignedDivide => Bitvector32Term::unsigned_divide(left, right),
            Self::Remainder => Bitvector32Term::remainder(left, right),
            Self::UnsignedRemainder => Bitvector32Term::unsigned_remainder(left, right),
            Self::ShiftLeft => Bitvector32Term::shift_left(left, right),
            Self::ArithmeticShiftRight => Bitvector32Term::arithmetic_shift_right(left, right),
            Self::LogicalShiftRight => Bitvector32Term::logical_shift_right(left, right),
            Self::BitwiseAnd => Bitvector32Term::bitwise_and(left, right),
            Self::BitwiseOr => Bitvector32Term::bitwise_or(left, right),
            Self::BitwiseXor => Bitvector32Term::bitwise_xor(left, right),
            Self::Int64Add => Bitvector32Term::int64_add(left, right),
            Self::Int64Subtract => Bitvector32Term::int64_subtract(left, right),
            Self::Int64Multiply => Bitvector32Term::int64_multiply(left, right),
            Self::Int64Divide => Bitvector32Term::int64_divide(left, right),
            Self::Int64Remainder => Bitvector32Term::int64_remainder(left, right),
            Self::Int64ShiftLeft => Bitvector32Term::int64_shift_left(left, right),
            Self::Int64ArithmeticShiftRight => {
                Bitvector32Term::int64_arithmetic_shift_right(left, right)
            }
            Self::Int64BitwiseAnd => Bitvector32Term::int64_bitwise_and(left, right),
            Self::Int64BitwiseOr => Bitvector32Term::int64_bitwise_or(left, right),
            Self::Int64BitwiseXor => Bitvector32Term::int64_bitwise_xor(left, right),
            Self::UInt64Add => Bitvector32Term::uint64_add(left, right),
            Self::UInt64Subtract => Bitvector32Term::uint64_subtract(left, right),
            Self::UInt64Multiply => Bitvector32Term::uint64_multiply(left, right),
            Self::UInt64Divide => Bitvector32Term::uint64_divide(left, right),
            Self::UInt64Remainder => Bitvector32Term::uint64_remainder(left, right),
            Self::UInt64ShiftLeft => Bitvector32Term::uint64_shift_left(left, right),
            Self::UInt64LogicalShiftRight => {
                Bitvector32Term::uint64_logical_shift_right(left, right)
            }
            Self::UInt64BitwiseAnd => Bitvector32Term::uint64_bitwise_and(left, right),
            Self::UInt64BitwiseOr => Bitvector32Term::uint64_bitwise_or(left, right),
            Self::UInt64BitwiseXor => Bitvector32Term::uint64_bitwise_xor(left, right),
            Self::Float32(operator) => Bitvector32Term::float32_binary(left, right, operator),
            Self::Float64(operator) => Bitvector32Term::float64_binary(left, right, operator),
        }
    }

    /// Applies the operator as the bare node, without folding or
    /// normalization.
    pub(crate) fn build_raw(
        self,
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Bitvector32Term {
        let (left, right) = (Box::new(left), Box::new(right));
        match self {
            Self::Add => Bitvector32Term::Add(left, right),
            Self::Subtract => Bitvector32Term::Subtract(left, right),
            Self::Multiply => Bitvector32Term::Multiply(left, right),
            Self::Divide => Bitvector32Term::Divide(left, right),
            Self::UnsignedDivide => Bitvector32Term::UnsignedDivide(left, right),
            Self::Remainder => Bitvector32Term::Remainder(left, right),
            Self::UnsignedRemainder => Bitvector32Term::UnsignedRemainder(left, right),
            Self::ShiftLeft => Bitvector32Term::ShiftLeft(left, right),
            Self::ArithmeticShiftRight => Bitvector32Term::ArithmeticShiftRight(left, right),
            Self::LogicalShiftRight => Bitvector32Term::LogicalShiftRight(left, right),
            Self::BitwiseAnd => Bitvector32Term::BitwiseAnd(left, right),
            Self::BitwiseOr => Bitvector32Term::BitwiseOr(left, right),
            Self::BitwiseXor => Bitvector32Term::BitwiseXor(left, right),
            Self::Int64Add => Bitvector32Term::Int64Add(left, right),
            Self::Int64Subtract => Bitvector32Term::Int64Subtract(left, right),
            Self::Int64Multiply => Bitvector32Term::Int64Multiply(left, right),
            Self::Int64Divide => Bitvector32Term::Int64Divide(left, right),
            Self::Int64Remainder => Bitvector32Term::Int64Remainder(left, right),
            Self::Int64ShiftLeft => Bitvector32Term::Int64ShiftLeft(left, right),
            Self::Int64ArithmeticShiftRight => {
                Bitvector32Term::Int64ArithmeticShiftRight(left, right)
            }
            Self::Int64BitwiseAnd => Bitvector32Term::Int64BitwiseAnd(left, right),
            Self::Int64BitwiseOr => Bitvector32Term::Int64BitwiseOr(left, right),
            Self::Int64BitwiseXor => Bitvector32Term::Int64BitwiseXor(left, right),
            Self::UInt64Add => Bitvector32Term::UInt64Add(left, right),
            Self::UInt64Subtract => Bitvector32Term::UInt64Subtract(left, right),
            Self::UInt64Multiply => Bitvector32Term::UInt64Multiply(left, right),
            Self::UInt64Divide => Bitvector32Term::UInt64Divide(left, right),
            Self::UInt64Remainder => Bitvector32Term::UInt64Remainder(left, right),
            Self::UInt64ShiftLeft => Bitvector32Term::UInt64ShiftLeft(left, right),
            Self::UInt64LogicalShiftRight => Bitvector32Term::UInt64LogicalShiftRight(left, right),
            Self::UInt64BitwiseAnd => Bitvector32Term::UInt64BitwiseAnd(left, right),
            Self::UInt64BitwiseOr => Bitvector32Term::UInt64BitwiseOr(left, right),
            Self::UInt64BitwiseXor => Bitvector32Term::UInt64BitwiseXor(left, right),
            Self::Float32(operator) => Bitvector32Term::Float32Binary {
                operator,
                left,
                right,
            },
            Self::Float64(operator) => Bitvector32Term::Float64Binary {
                operator,
                left,
                right,
            },
        }
    }
}

impl BitvectorUnaryOp {
    /// Whether the operator is a float negation.
    pub(crate) fn is_float(self) -> bool {
        matches!(self, Self::Float32Negate | Self::Float64Negate)
    }

    /// Whether the operator is the original 32-bit word complement. Some
    /// traversals rebuild exactly the 32-bit word operators as bare nodes.
    pub(crate) fn is_bitvector32(self) -> bool {
        self == Self::BitwiseNot
    }

    /// Applies the operator through its smart constructor.
    pub(crate) fn build(self, value: Bitvector32Term) -> Bitvector32Term {
        match self {
            Self::BitwiseNot => Bitvector32Term::bitwise_not(value),
            Self::Int64BitwiseNot => Bitvector32Term::int64_bitwise_not(value),
            Self::UInt64BitwiseNot => Bitvector32Term::uint64_bitwise_not(value),
            Self::Int64From32 => Bitvector32Term::int64_from_32(value),
            Self::UInt64From32 => Bitvector32Term::uint64_from_32(value),
            Self::UInt32From64 => Bitvector32Term::uint32_from_64(value),
            Self::Int64FromUInt32 => Bitvector32Term::int64_from_uint32(value),
            Self::UInt64FromInt32 => Bitvector32Term::uint64_from_int32(value),
            Self::UInt64FromInt64 => Bitvector32Term::uint64_from_int64(value),
            Self::Float32Negate => Bitvector32Term::float32_negate(value),
            Self::Float64Negate => Bitvector32Term::float64_negate(value),
            Self::MachineIntegerCast {
                source,
                destination,
            } => Bitvector32Term::machine_integer_cast(source, destination, value),
        }
    }

    /// Applies the operator as the bare node, without folding or
    /// normalization.
    pub(crate) fn build_raw(self, value: Bitvector32Term) -> Bitvector32Term {
        let value = Box::new(value);
        match self {
            Self::BitwiseNot => Bitvector32Term::BitwiseNot(value),
            Self::Int64BitwiseNot => Bitvector32Term::Int64BitwiseNot(value),
            Self::UInt64BitwiseNot => Bitvector32Term::UInt64BitwiseNot(value),
            Self::Int64From32 => Bitvector32Term::Int64From32(value),
            Self::UInt64From32 => Bitvector32Term::UInt64From32(value),
            Self::UInt32From64 => Bitvector32Term::UInt32From64(value),
            Self::Int64FromUInt32 => Bitvector32Term::Int64FromUInt32(value),
            Self::UInt64FromInt32 => Bitvector32Term::UInt64FromInt32(value),
            Self::UInt64FromInt64 => Bitvector32Term::UInt64FromInt64(value),
            Self::Float32Negate => Bitvector32Term::Float32Negate(value),
            Self::Float64Negate => Bitvector32Term::Float64Negate(value),
            Self::MachineIntegerCast {
                source,
                destination,
            } => Bitvector32Term::MachineIntegerCast {
                value,
                source,
                destination,
            },
        }
    }
}

/// A comparison or overflow test of two bitvector operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum BitvectorComparisonOp {
    Bitvector32SignedLessThan,
    Bitvector32SignedLessEqual,
    Bitvector32SignedGreaterThan,
    Bitvector32SignedGreaterEqual,
    Bitvector32Equal,
    Bitvector32SignedAddOverflows,
    Bitvector32SignedSubtractOverflows,
    Bitvector32SignedMultiplyOverflows,
    Bitvector32SignedDivideOverflows,
    Bitvector32SignedShiftLeftOverflows,
    Bitvector64SignedLessThan,
    Bitvector64SignedLessEqual,
    Bitvector64SignedGreaterThan,
    Bitvector64SignedGreaterEqual,
    Bitvector64UnsignedLessThan,
    Bitvector64UnsignedLessEqual,
    Bitvector64UnsignedGreaterThan,
    Bitvector64UnsignedGreaterEqual,
    Bitvector64Equal,
    Bitvector64SignedAddOverflows,
    Bitvector64SignedSubtractOverflows,
    Bitvector64SignedMultiplyOverflows,
    Bitvector64SignedDivideOverflows,
    Bitvector64SignedShiftLeftOverflows,
}

impl ConditionTerm {
    /// The operator and operands of a bitvector comparison or overflow test,
    /// or `None` for every other condition.
    pub(crate) fn as_bitvector_comparison(
        &self,
    ) -> Option<(BitvectorComparisonOp, &Bitvector32Term, &Bitvector32Term)> {
        match self {
            Self::Bitvector32SignedLessThan(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedLessThan,
                left,
                right,
            )),
            Self::Bitvector32SignedLessEqual(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedLessEqual,
                left,
                right,
            )),
            Self::Bitvector32SignedGreaterThan(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedGreaterThan,
                left,
                right,
            )),
            Self::Bitvector32SignedGreaterEqual(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedGreaterEqual,
                left,
                right,
            )),
            Self::Bitvector32Equal(left, right) => {
                Some((BitvectorComparisonOp::Bitvector32Equal, left, right))
            }
            Self::Bitvector32SignedAddOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedAddOverflows,
                left,
                right,
            )),
            Self::Bitvector32SignedSubtractOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedSubtractOverflows,
                left,
                right,
            )),
            Self::Bitvector32SignedMultiplyOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedMultiplyOverflows,
                left,
                right,
            )),
            Self::Bitvector32SignedDivideOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedDivideOverflows,
                left,
                right,
            )),
            Self::Bitvector32SignedShiftLeftOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector32SignedShiftLeftOverflows,
                left,
                right,
            )),
            Self::Bitvector64SignedLessThan(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedLessThan,
                left,
                right,
            )),
            Self::Bitvector64SignedLessEqual(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedLessEqual,
                left,
                right,
            )),
            Self::Bitvector64SignedGreaterThan(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedGreaterThan,
                left,
                right,
            )),
            Self::Bitvector64SignedGreaterEqual(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedGreaterEqual,
                left,
                right,
            )),
            Self::Bitvector64UnsignedLessThan(left, right) => Some((
                BitvectorComparisonOp::Bitvector64UnsignedLessThan,
                left,
                right,
            )),
            Self::Bitvector64UnsignedLessEqual(left, right) => Some((
                BitvectorComparisonOp::Bitvector64UnsignedLessEqual,
                left,
                right,
            )),
            Self::Bitvector64UnsignedGreaterThan(left, right) => Some((
                BitvectorComparisonOp::Bitvector64UnsignedGreaterThan,
                left,
                right,
            )),
            Self::Bitvector64UnsignedGreaterEqual(left, right) => Some((
                BitvectorComparisonOp::Bitvector64UnsignedGreaterEqual,
                left,
                right,
            )),
            Self::Bitvector64Equal(left, right) => {
                Some((BitvectorComparisonOp::Bitvector64Equal, left, right))
            }
            Self::Bitvector64SignedAddOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedAddOverflows,
                left,
                right,
            )),
            Self::Bitvector64SignedSubtractOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedSubtractOverflows,
                left,
                right,
            )),
            Self::Bitvector64SignedMultiplyOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedMultiplyOverflows,
                left,
                right,
            )),
            Self::Bitvector64SignedDivideOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedDivideOverflows,
                left,
                right,
            )),
            Self::Bitvector64SignedShiftLeftOverflows(left, right) => Some((
                BitvectorComparisonOp::Bitvector64SignedShiftLeftOverflows,
                left,
                right,
            )),
            Self::Constant(_)
            | Self::Variable(_)
            | Self::AlgebraicEqual(..)
            | Self::Float32(_)
            | Self::Float64(_)
            | Self::PointerOffsetEqual(..)
            | Self::PointerEqual(..)
            | crate::kernel::integer_comparison_condition!(_, _) => None,
        }
    }
}

impl BitvectorComparisonOp {
    /// The C spelling of the comparison, or of the operation an overflow test
    /// guards. Signed and unsigned forms share a spelling.
    pub(crate) fn c_symbol(self) -> &'static str {
        match self {
            Self::Bitvector32SignedLessThan
            | Self::Bitvector64SignedLessThan
            | Self::Bitvector64UnsignedLessThan => "<",
            Self::Bitvector32SignedLessEqual
            | Self::Bitvector64SignedLessEqual
            | Self::Bitvector64UnsignedLessEqual => "<=",
            Self::Bitvector32SignedGreaterThan
            | Self::Bitvector64SignedGreaterThan
            | Self::Bitvector64UnsignedGreaterThan => ">",
            Self::Bitvector32SignedGreaterEqual
            | Self::Bitvector64SignedGreaterEqual
            | Self::Bitvector64UnsignedGreaterEqual => ">=",
            Self::Bitvector32Equal | Self::Bitvector64Equal => "==",
            Self::Bitvector32SignedAddOverflows | Self::Bitvector64SignedAddOverflows => "+",
            Self::Bitvector32SignedSubtractOverflows | Self::Bitvector64SignedSubtractOverflows => {
                "-"
            }
            Self::Bitvector32SignedMultiplyOverflows | Self::Bitvector64SignedMultiplyOverflows => {
                "*"
            }
            Self::Bitvector32SignedDivideOverflows | Self::Bitvector64SignedDivideOverflows => "/",
            Self::Bitvector32SignedShiftLeftOverflows
            | Self::Bitvector64SignedShiftLeftOverflows => "<<",
        }
    }

    /// Whether the condition is an overflow test of the operation
    /// [`Self::c_symbol`] spells, rather than a comparison.
    pub(crate) fn is_overflow(self) -> bool {
        matches!(
            self,
            Self::Bitvector32SignedAddOverflows
                | Self::Bitvector32SignedSubtractOverflows
                | Self::Bitvector32SignedMultiplyOverflows
                | Self::Bitvector32SignedDivideOverflows
                | Self::Bitvector32SignedShiftLeftOverflows
                | Self::Bitvector64SignedAddOverflows
                | Self::Bitvector64SignedSubtractOverflows
                | Self::Bitvector64SignedMultiplyOverflows
                | Self::Bitvector64SignedDivideOverflows
                | Self::Bitvector64SignedShiftLeftOverflows
        )
    }

    /// The machine type the operands are read as. 64-bit equality ignores
    /// signedness, so it reads its operands as bare 64-bit words.
    pub(crate) fn operand_type(self) -> &'static str {
        match self {
            Self::Bitvector32SignedLessThan
            | Self::Bitvector32SignedLessEqual
            | Self::Bitvector32SignedGreaterThan
            | Self::Bitvector32SignedGreaterEqual
            | Self::Bitvector32Equal
            | Self::Bitvector32SignedAddOverflows
            | Self::Bitvector32SignedSubtractOverflows
            | Self::Bitvector32SignedMultiplyOverflows
            | Self::Bitvector32SignedDivideOverflows
            | Self::Bitvector32SignedShiftLeftOverflows => "int32",
            Self::Bitvector64SignedLessThan
            | Self::Bitvector64SignedLessEqual
            | Self::Bitvector64SignedGreaterThan
            | Self::Bitvector64SignedGreaterEqual
            | Self::Bitvector64SignedAddOverflows
            | Self::Bitvector64SignedSubtractOverflows
            | Self::Bitvector64SignedMultiplyOverflows
            | Self::Bitvector64SignedDivideOverflows
            | Self::Bitvector64SignedShiftLeftOverflows => "int64",
            Self::Bitvector64UnsignedLessThan
            | Self::Bitvector64UnsignedLessEqual
            | Self::Bitvector64UnsignedGreaterThan
            | Self::Bitvector64UnsignedGreaterEqual => "uint64",
            Self::Bitvector64Equal => "bits64",
        }
    }

    /// Applies the comparison through its smart constructor.
    pub(crate) fn build(self, left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
        match self {
            Self::Bitvector32SignedLessThan => ConditionTerm::signed_less_than(left, right),
            Self::Bitvector32SignedLessEqual => ConditionTerm::signed_less_equal(left, right),
            Self::Bitvector32SignedGreaterThan => ConditionTerm::signed_greater_than(left, right),
            Self::Bitvector32SignedGreaterEqual => ConditionTerm::signed_greater_equal(left, right),
            Self::Bitvector32Equal => ConditionTerm::equal(left, right),
            Self::Bitvector32SignedAddOverflows => ConditionTerm::signed_add_overflows(left, right),
            Self::Bitvector32SignedSubtractOverflows => {
                ConditionTerm::signed_subtract_overflows(left, right)
            }
            Self::Bitvector32SignedMultiplyOverflows => {
                ConditionTerm::signed_multiply_overflows(left, right)
            }
            Self::Bitvector32SignedDivideOverflows => {
                ConditionTerm::signed_divide_overflows(left, right)
            }
            Self::Bitvector32SignedShiftLeftOverflows => {
                ConditionTerm::signed_shift_left_overflows(left, right)
            }
            Self::Bitvector64SignedLessThan => ConditionTerm::int64_signed_less_than(left, right),
            Self::Bitvector64SignedLessEqual => ConditionTerm::int64_signed_less_equal(left, right),
            Self::Bitvector64SignedGreaterThan => {
                ConditionTerm::int64_signed_greater_than(left, right)
            }
            Self::Bitvector64SignedGreaterEqual => {
                ConditionTerm::int64_signed_greater_equal(left, right)
            }
            Self::Bitvector64UnsignedLessThan => ConditionTerm::uint64_less_than(left, right),
            Self::Bitvector64UnsignedLessEqual => ConditionTerm::uint64_less_equal(left, right),
            Self::Bitvector64UnsignedGreaterThan => ConditionTerm::uint64_greater_than(left, right),
            Self::Bitvector64UnsignedGreaterEqual => {
                ConditionTerm::uint64_greater_equal(left, right)
            }
            Self::Bitvector64Equal => ConditionTerm::int64_equal(left, right),
            Self::Bitvector64SignedAddOverflows => {
                ConditionTerm::int64_signed_add_overflows(left, right)
            }
            Self::Bitvector64SignedSubtractOverflows => {
                ConditionTerm::int64_signed_subtract_overflows(left, right)
            }
            Self::Bitvector64SignedMultiplyOverflows => {
                ConditionTerm::int64_signed_multiply_overflows(left, right)
            }
            Self::Bitvector64SignedDivideOverflows => {
                ConditionTerm::int64_signed_divide_overflows(left, right)
            }
            Self::Bitvector64SignedShiftLeftOverflows => {
                ConditionTerm::int64_signed_shift_left_overflows(left, right)
            }
        }
    }

    /// Applies the comparison as the bare node, without folding or
    /// normalization.
    pub(crate) fn build_raw(self, left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
        let (left, right) = (Box::new(left), Box::new(right));
        match self {
            Self::Bitvector32SignedLessThan => {
                ConditionTerm::Bitvector32SignedLessThan(left, right)
            }
            Self::Bitvector32SignedLessEqual => {
                ConditionTerm::Bitvector32SignedLessEqual(left, right)
            }
            Self::Bitvector32SignedGreaterThan => {
                ConditionTerm::Bitvector32SignedGreaterThan(left, right)
            }
            Self::Bitvector32SignedGreaterEqual => {
                ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
            }
            Self::Bitvector32Equal => ConditionTerm::Bitvector32Equal(left, right),
            Self::Bitvector32SignedAddOverflows => {
                ConditionTerm::Bitvector32SignedAddOverflows(left, right)
            }
            Self::Bitvector32SignedSubtractOverflows => {
                ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
            }
            Self::Bitvector32SignedMultiplyOverflows => {
                ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
            }
            Self::Bitvector32SignedDivideOverflows => {
                ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
            }
            Self::Bitvector32SignedShiftLeftOverflows => {
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
            }
            Self::Bitvector64SignedLessThan => {
                ConditionTerm::Bitvector64SignedLessThan(left, right)
            }
            Self::Bitvector64SignedLessEqual => {
                ConditionTerm::Bitvector64SignedLessEqual(left, right)
            }
            Self::Bitvector64SignedGreaterThan => {
                ConditionTerm::Bitvector64SignedGreaterThan(left, right)
            }
            Self::Bitvector64SignedGreaterEqual => {
                ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
            }
            Self::Bitvector64UnsignedLessThan => {
                ConditionTerm::Bitvector64UnsignedLessThan(left, right)
            }
            Self::Bitvector64UnsignedLessEqual => {
                ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
            }
            Self::Bitvector64UnsignedGreaterThan => {
                ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
            }
            Self::Bitvector64UnsignedGreaterEqual => {
                ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
            }
            Self::Bitvector64Equal => ConditionTerm::Bitvector64Equal(left, right),
            Self::Bitvector64SignedAddOverflows => {
                ConditionTerm::Bitvector64SignedAddOverflows(left, right)
            }
            Self::Bitvector64SignedSubtractOverflows => {
                ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
            }
            Self::Bitvector64SignedMultiplyOverflows => {
                ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
            }
            Self::Bitvector64SignedDivideOverflows => {
                ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
            }
            Self::Bitvector64SignedShiftLeftOverflows => {
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FLOAT_OPERATORS: [CFloatBinaryOperator; 4] = [
        CFloatBinaryOperator::Add,
        CFloatBinaryOperator::Subtract,
        CFloatBinaryOperator::Multiply,
        CFloatBinaryOperator::Divide,
    ];

    fn binary_ops() -> Vec<BitvectorBinaryOp> {
        let mut ops = vec![
            BitvectorBinaryOp::Add,
            BitvectorBinaryOp::Subtract,
            BitvectorBinaryOp::Multiply,
            BitvectorBinaryOp::Divide,
            BitvectorBinaryOp::UnsignedDivide,
            BitvectorBinaryOp::Remainder,
            BitvectorBinaryOp::UnsignedRemainder,
            BitvectorBinaryOp::ShiftLeft,
            BitvectorBinaryOp::ArithmeticShiftRight,
            BitvectorBinaryOp::LogicalShiftRight,
            BitvectorBinaryOp::BitwiseAnd,
            BitvectorBinaryOp::BitwiseOr,
            BitvectorBinaryOp::BitwiseXor,
            BitvectorBinaryOp::Int64Add,
            BitvectorBinaryOp::Int64Subtract,
            BitvectorBinaryOp::Int64Multiply,
            BitvectorBinaryOp::Int64Divide,
            BitvectorBinaryOp::Int64Remainder,
            BitvectorBinaryOp::Int64ShiftLeft,
            BitvectorBinaryOp::Int64ArithmeticShiftRight,
            BitvectorBinaryOp::Int64BitwiseAnd,
            BitvectorBinaryOp::Int64BitwiseOr,
            BitvectorBinaryOp::Int64BitwiseXor,
            BitvectorBinaryOp::UInt64Add,
            BitvectorBinaryOp::UInt64Subtract,
            BitvectorBinaryOp::UInt64Multiply,
            BitvectorBinaryOp::UInt64Divide,
            BitvectorBinaryOp::UInt64Remainder,
            BitvectorBinaryOp::UInt64ShiftLeft,
            BitvectorBinaryOp::UInt64LogicalShiftRight,
            BitvectorBinaryOp::UInt64BitwiseAnd,
            BitvectorBinaryOp::UInt64BitwiseOr,
            BitvectorBinaryOp::UInt64BitwiseXor,
        ];
        for operator in FLOAT_OPERATORS {
            ops.push(BitvectorBinaryOp::Float32(operator));
            ops.push(BitvectorBinaryOp::Float64(operator));
        }
        ops
    }

    fn unary_ops() -> Vec<BitvectorUnaryOp> {
        vec![
            BitvectorUnaryOp::BitwiseNot,
            BitvectorUnaryOp::Int64BitwiseNot,
            BitvectorUnaryOp::UInt64BitwiseNot,
            BitvectorUnaryOp::Int64From32,
            BitvectorUnaryOp::UInt64From32,
            BitvectorUnaryOp::UInt32From64,
            BitvectorUnaryOp::Int64FromUInt32,
            BitvectorUnaryOp::UInt64FromInt32,
            BitvectorUnaryOp::UInt64FromInt64,
            BitvectorUnaryOp::Float32Negate,
            BitvectorUnaryOp::Float64Negate,
            BitvectorUnaryOp::MachineIntegerCast {
                source: MachineIntegerType::Int32,
                destination: MachineIntegerType::UInt64,
            },
        ]
    }

    fn variable(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    #[test]
    fn every_binary_operator_splits_back_from_its_bare_node() {
        for op in binary_ops() {
            let node = op.build_raw(variable(1), variable(2));
            assert_eq!(
                node.as_binary(),
                Some((op, &variable(1), &variable(2))),
                "{op:?}"
            );
            assert_eq!(node.as_unary(), None, "{op:?}");
        }
    }

    #[test]
    fn every_unary_operator_splits_back_from_its_bare_node() {
        for op in unary_ops() {
            let node = op.build_raw(variable(1));
            assert_eq!(node.as_unary(), Some((op, &variable(1))), "{op:?}");
            assert_eq!(node.as_binary(), None, "{op:?}");
        }
    }

    /// The split covers exactly the arithmetic variants: one per binary
    /// machine operator, the two float binaries, and every unary operator
    /// and conversion. Any other variant must be handled by a traversal's
    /// own arm.
    #[test]
    fn the_split_covers_exactly_the_arithmetic_variants() {
        let others = [
            Bitvector32Term::Constant(1),
            Bitvector32Term::Int64Constant(1),
            Bitvector32Term::UInt64Constant(1),
            variable(1),
            Bitvector32Term::If {
                condition: Box::new(ConditionTerm::Constant(true)),
                then_term: Box::new(variable(1)),
                else_term: Box::new(variable(2)),
            },
            Bitvector32Term::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![variable(1)],
            },
        ];
        for term in others {
            assert_eq!(term.as_binary(), None, "{term:?}");
            assert_eq!(term.as_unary(), None, "{term:?}");
        }
        assert_eq!(binary_ops().len(), 33 + 2 * FLOAT_OPERATORS.len());
        assert_eq!(unary_ops().len(), 12);
    }

    /// `build` is the operator's smart constructor: on symbolic operands that
    /// no rule folds, it produces the same node as `build_raw`.
    #[test]
    fn smart_build_agrees_with_the_bare_node_on_unfoldable_operands() {
        for op in binary_ops() {
            let smart = op.build(variable(1), variable(2));
            let split = smart.as_binary().map(|(split_op, _, _)| split_op);
            assert_eq!(split, Some(op), "{op:?} built {smart:?}");
        }
        for op in unary_ops() {
            let smart = op.build(variable(1));
            let split = smart.as_unary().map(|(split_op, _)| split_op);
            assert_eq!(split, Some(op), "{op:?} built {smart:?}");
        }
    }

    /// Exactly the original 32-bit word operators count as 32-bit: the 13
    /// two-operand word operators and the word complement.
    #[test]
    fn the_32_bit_word_operators_are_exactly_the_original_word_variants() {
        let word_binaries = binary_ops()
            .into_iter()
            .filter(|op| op.is_bitvector32())
            .collect::<Vec<_>>();
        assert_eq!(word_binaries, binary_ops()[..13].to_vec());
        let word_unaries = unary_ops()
            .into_iter()
            .filter(|op| op.is_bitvector32())
            .collect::<Vec<_>>();
        assert_eq!(word_unaries, vec![BitvectorUnaryOp::BitwiseNot]);
    }

    fn comparison_ops() -> Vec<BitvectorComparisonOp> {
        vec![
            BitvectorComparisonOp::Bitvector32SignedLessThan,
            BitvectorComparisonOp::Bitvector32SignedLessEqual,
            BitvectorComparisonOp::Bitvector32SignedGreaterThan,
            BitvectorComparisonOp::Bitvector32SignedGreaterEqual,
            BitvectorComparisonOp::Bitvector32Equal,
            BitvectorComparisonOp::Bitvector32SignedAddOverflows,
            BitvectorComparisonOp::Bitvector32SignedSubtractOverflows,
            BitvectorComparisonOp::Bitvector32SignedMultiplyOverflows,
            BitvectorComparisonOp::Bitvector32SignedDivideOverflows,
            BitvectorComparisonOp::Bitvector32SignedShiftLeftOverflows,
            BitvectorComparisonOp::Bitvector64SignedLessThan,
            BitvectorComparisonOp::Bitvector64SignedLessEqual,
            BitvectorComparisonOp::Bitvector64SignedGreaterThan,
            BitvectorComparisonOp::Bitvector64SignedGreaterEqual,
            BitvectorComparisonOp::Bitvector64UnsignedLessThan,
            BitvectorComparisonOp::Bitvector64UnsignedLessEqual,
            BitvectorComparisonOp::Bitvector64UnsignedGreaterThan,
            BitvectorComparisonOp::Bitvector64UnsignedGreaterEqual,
            BitvectorComparisonOp::Bitvector64Equal,
            BitvectorComparisonOp::Bitvector64SignedAddOverflows,
            BitvectorComparisonOp::Bitvector64SignedSubtractOverflows,
            BitvectorComparisonOp::Bitvector64SignedMultiplyOverflows,
            BitvectorComparisonOp::Bitvector64SignedDivideOverflows,
            BitvectorComparisonOp::Bitvector64SignedShiftLeftOverflows,
        ]
    }

    #[test]
    fn every_comparison_splits_back_from_its_bare_node() {
        for op in comparison_ops() {
            let node = op.build_raw(variable(1), variable(2));
            assert_eq!(
                node.as_bitvector_comparison(),
                Some((op, &variable(1), &variable(2))),
                "{op:?}"
            );
        }
        assert_eq!(comparison_ops().len(), 24);
        assert_eq!(
            ConditionTerm::Constant(true).as_bitvector_comparison(),
            None
        );
    }
}
