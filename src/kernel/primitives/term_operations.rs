use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineBinaryOp, MachineUnaryOp, OverflowOperation};
use crate::kernel::{MachineCastSpelling, MachineTerm, cast_term};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint64_constant,
};

// Operands here have already undergone the language's scalar promotions.
// Keep both constant-folding entry points on the shared format semantics.
fn checked_machine_div_rem_const(
    ty: MachineIntegerType,
    left: u128,
    right: u128,
) -> Option<(u128, u128)> {
    let left = MachineIntegerConstant::from_bits(ty.format(), left)?;
    let right = MachineIntegerConstant::from_bits(ty.format(), right)?;
    let (quotient, remainder) = left.truncating_div_rem(right).ok()?;
    Some((quotient.bits(), remainder.bits()))
}

fn checked_signed_divide_const(left: u32, right: u32) -> Option<u32> {
    checked_machine_div_rem_const(MachineIntegerType::Int32, left.into(), right.into())
        .map(|(quotient, _)| quotient as u32)
}

fn checked_signed_remainder_const(left: u32, right: u32) -> Option<u32> {
    checked_machine_div_rem_const(MachineIntegerType::Int32, left.into(), right.into())
        .map(|(_, remainder)| remainder as u32)
}

fn checked_unsigned_divide_const(left: u32, right: u32) -> Option<u32> {
    checked_machine_div_rem_const(MachineIntegerType::UInt32, left.into(), right.into())
        .map(|(quotient, _)| quotient as u32)
}

fn checked_unsigned_remainder_const(left: u32, right: u32) -> Option<u32> {
    checked_machine_div_rem_const(MachineIntegerType::UInt32, left.into(), right.into())
        .map(|(_, remainder)| remainder as u32)
}

fn checked_int64_divide_const(left: i64, right: i64) -> Option<i64> {
    checked_machine_div_rem_const(
        MachineIntegerType::Int64,
        left as u64 as u128,
        right as u64 as u128,
    )
    .map(|(quotient, _)| quotient as i64)
}

fn checked_int64_remainder_const(left: i64, right: i64) -> Option<i64> {
    checked_machine_div_rem_const(
        MachineIntegerType::Int64,
        left as u64 as u128,
        right as u64 as u128,
    )
    .map(|(_, remainder)| remainder as i64)
}

fn checked_uint64_divide_const(left: u64, right: u64) -> Option<u64> {
    checked_machine_div_rem_const(MachineIntegerType::UInt64, left.into(), right.into())
        .map(|(quotient, _)| quotient as u64)
}

fn checked_uint64_remainder_const(left: u64, right: u64) -> Option<u64> {
    checked_machine_div_rem_const(MachineIntegerType::UInt64, left.into(), right.into())
        .map(|(_, remainder)| remainder as u64)
}

fn checked_shift_count_const(count: u32) -> Option<u32> {
    let count = count as i32;
    (0..32).contains(&count).then_some(count as u32)
}

fn checked_signed_shift_left_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    let left = left as i32;
    if left < 0 {
        return None;
    }
    let shifted = (left as i64) << count;
    (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
}

fn checked_arithmetic_shift_right_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    Some(((left as i32) >> count) as u32)
}

fn checked_logical_shift_right_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    Some(left >> count)
}

fn signed_shift_left_overflows_const(left: u32, right: u32) -> Option<bool> {
    let count = checked_shift_count_const(right)?;
    let left = left as i32;
    if left < 0 {
        return Some(false);
    }
    Some(((left as i64) << count) > i64::from(i32::MAX))
}

/// Whether every sum of an `int64` value in `left` and one in `right` is a
/// representable `int64`. An unknown interval never fits.
pub(in crate::kernel) fn int64_add_interval_fits(
    left: Option<(i64, i64)>,
    right: Option<(i64, i64)>,
) -> bool {
    let (Some((left_lower, left_upper)), Some((right_lower, right_upper))) = (left, right) else {
        return false;
    };
    int64_interval_fits(
        i128::from(left_lower) + i128::from(right_lower),
        i128::from(left_upper) + i128::from(right_upper),
    )
}

/// Whether every difference `left - right` of values in the two intervals is
/// a representable `int64`. An unknown interval never fits.
pub(in crate::kernel) fn int64_subtract_interval_fits(
    left: Option<(i64, i64)>,
    right: Option<(i64, i64)>,
) -> bool {
    let (Some((left_lower, left_upper)), Some((right_lower, right_upper))) = (left, right) else {
        return false;
    };
    int64_interval_fits(
        i128::from(left_lower) - i128::from(right_upper),
        i128::from(left_upper) - i128::from(right_lower),
    )
}

/// Decides a signed `int64` order from its operands' root ranges alone, when
/// every pair of values in those ranges gives the same answer: `cast64(x) >
/// 9223372036854775807` is false for an `int` `x`, as is `t > INT64_MAX` for
/// any `t`. A root without a narrower range has the whole `int64` range.
fn int64_signed_order_by_width(
    left: &MachineTerm,
    right: &MachineTerm,
    holds: impl Fn(i64, i64) -> bool,
) -> Option<bool> {
    int64_signed_order_by_width_views(
        MachineOperandView::Legacy(left),
        MachineOperandView::Legacy(right),
        holds,
    )
}

pub(in crate::kernel) fn int64_signed_order_by_width_views(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
    holds: impl Fn(i64, i64) -> bool,
) -> Option<bool> {
    let whole = (i64::MIN, i64::MAX);
    let (left_lower, left_upper) = left.int64_width_interval().unwrap_or(whole);
    let (right_lower, right_upper) = right.int64_width_interval().unwrap_or(whole);
    // The order is monotone in each operand, so it holds for every pair iff
    // it holds at the corner least favourable to it, and fails for every
    // pair iff it fails at the most favourable one. For `<` and `<=` the
    // least favourable corner is the left maximum against the right minimum.
    let (worst, best) = if holds(i64::MIN, i64::MAX) {
        (
            holds(left_upper, right_lower),
            holds(left_lower, right_upper),
        )
    } else {
        (
            holds(left_lower, right_upper),
            holds(left_upper, right_lower),
        )
    };
    if worst {
        Some(true)
    } else if !best {
        Some(false)
    } else {
        None
    }
}

fn int64_interval_fits(lower: i128, upper: i128) -> bool {
    lower >= i128::from(i64::MIN) && upper <= i128::from(i64::MAX)
}

impl MachineTerm {
    /// The `int32` constant whose bits are `bits`, the format of every
    /// kernel-internal constant. See [`MachineTerm::Constant`].
    pub const fn constant(bits: u32) -> Self {
        Self::Constant {
            format: MachineIntegerType::Int32,
            bits: bits as u128,
        }
    }

    /// The `uint32` constant whose bits are `bits`.
    pub const fn uint32_constant(bits: u32) -> Self {
        Self::Constant {
            format: MachineIntegerType::UInt32,
            bits: bits as u128,
        }
    }

    /// The `int64` constant `value`.
    pub const fn int64_constant(value: i64) -> Self {
        Self::Constant {
            format: MachineIntegerType::Int64,
            bits: value as u64 as u128,
        }
    }

    /// The `uint64` constant `value`.
    pub const fn uint64_constant(value: u64) -> Self {
        Self::Constant {
            format: MachineIntegerType::UInt64,
            bits: value as u128,
        }
    }

    /// The constant `value`, at its own format.
    pub fn machine_constant(value: MachineIntegerConstant) -> Self {
        Self::Constant {
            format: MachineIntegerType::of_format(value.format()),
            bits: value.bits(),
        }
    }

    /// A root constant as a checked [`MachineIntegerConstant`] of its
    /// format, if this term is one. One match on the root; it charges no
    /// work, as matching the constant's node does not.
    pub(crate) fn as_machine_constant(&self) -> Option<MachineIntegerConstant> {
        match self {
            Self::Constant { format, bits } => Some(MachineIntegerConstant::from_term_bits(
                format.format(),
                *bits,
            )),
            _ => None,
        }
    }
}

impl MachineTerm {
    /// Keep pointer-to-integer casts canonical when checked rewriting turns
    /// a symbolic pointer into null, just as C cast evaluation does.
    pub(crate) fn integer_address(pointer: Address) -> Self {
        if let Some(bits) = pointer.integer_address_bits() {
            return bits.clone();
        }
        if pointer == Address::null() {
            Self::uint64_constant(0)
        } else {
            Self::IntegerAddress(Box::new(pointer), crate::kernel::AddressObjectClass::NONE)
        }
    }

    pub(crate) fn object_pointer_address(
        pointer: Address,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        if pointer == Address::null() {
            Self::uint64_constant(0)
        } else {
            Self::IntegerAddress(
                Box::new(pointer),
                crate::kernel::AddressObjectClass::new(class),
            )
        }
    }

    pub(crate) fn address_pointer(&self) -> Option<&Address> {
        match self {
            Self::IntegerAddress(pointer, _) => Some(pointer),
            _ => None,
        }
    }

    /// The range an `int64` term has from its own root constructor alone: a
    /// constant is itself, and a value widened from a 32-bit source lies in
    /// that source type's range. This inspects only the root, never
    /// assumptions or subterms, so a constructor may call it for free.
    pub(in crate::kernel) fn int64_width_interval(&self) -> Option<(i64, i64)> {
        crate::kernel::MachineOperandView::Legacy(self).int64_width_interval()
    }

    // Local structural bounds only: do not search assumptions or traverse an
    // unrelated expression tree to establish a shift-count bound.
    fn unsigned32_upper_bound(&self) -> u32 {
        crate::kernel::MachineOperandView::Legacy(self).unsigned32_upper_bound()
    }

    pub(crate) fn opaque_conversion(name: impl Into<String>, value: Self) -> Self {
        Self::rebuild_pure_application(name.into(), vec![value])
    }

    pub(crate) fn float32_as_const(&self) -> Option<u32> {
        float32_bits_as_const(self)
    }

    pub(crate) fn float64_as_const(&self) -> Option<u64> {
        float64_bits_as_const(self)
    }

    pub(crate) fn float32_negate(value: Self) -> Self {
        match float32_bits_as_const(&value) {
            Some(value) => Self::constant(value ^ 0x8000_0000),
            None => Self::Float32Negate(Box::new(value)),
        }
    }

    pub(crate) fn float64_negate(value: Self) -> Self {
        match float64_bits_as_const(&value) {
            Some(value) => Self::uint64_constant(value ^ 0x8000_0000_0000_0000),
            None => Self::Float64Negate(Box::new(value)),
        }
    }

    pub(crate) fn float32_binary(left: Self, right: Self, operator: FloatBinaryOperator) -> Self {
        match (float32_bits_as_const(&left), float32_bits_as_const(&right)) {
            (Some(left), Some(right)) => {
                Self::constant(
                    float_binary_bits(u64::from(left), u64::from(right), 8, 23, operator) as u32,
                )
            }
            _ => Self::Float32Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn float64_binary(left: Self, right: Self, operator: FloatBinaryOperator) -> Self {
        match (float64_bits_as_const(&left), float64_bits_as_const(&right)) {
            (Some(left), Some(right)) => {
                Self::uint64_constant(float_binary_bits(left, right, 11, 52, operator))
            }
            _ => Self::Float64Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub fn var(var: Variable) -> Self {
        Self::Variable(var)
    }

    pub(crate) fn as_const(&self) -> Option<u32> {
        match self {
            Self::ThreadHandle(_) => None,
            Self::Cast {
                spelling: MachineCastSpelling::Generic,
                ..
            }
            | Self::BoolCast { .. } => None,

            native_constant!(_, _) => None,

            bits32_constant!(value) => Some(constant_u32(*value)),
            Self::Variable(_)
            | Self::MemoryLoad(_, _, _)
            | Self::IntegerAddress(_, _)
            | Self::IntegerToMachine { .. }
            | Self::PureFunctionApplication { .. }
            | Self::ClickFunctionApplication { .. }
            | Self::AlgebraicMatch { .. }
            | int64_constant!(_)
            | uint64_constant!(_)
            | cast_term!(Int64From32, _)
            | cast_term!(Int64FromUInt32, _)
            | cast_term!(UInt64From32, _)
            | cast_term!(UInt32From64, _)
            | cast_term!(UInt64FromInt32, _)
            | cast_term!(UInt64FromInt64, _)
            | crate::kernel::binary_wide_term!(..)
            | crate::kernel::unary_wide_term!(..)
            | Self::Float32Negate(_)
            | Self::Float32Binary { .. }
            | Self::Float64Negate(_)
            | Self::Float64Binary { .. } => None,
            binary_term!(Bits32, Add, left, right) => {
                Some(left.as_const()?.wrapping_add(right.as_const()?))
            }
            binary_term!(Bits32, Subtract, left, right) => {
                Some(left.as_const()?.wrapping_sub(right.as_const()?))
            }
            binary_term!(Bits32, Multiply, left, right) => {
                Some(left.as_const()?.wrapping_mul(right.as_const()?))
            }
            binary_term!(Int32, Divide, left, right) => {
                checked_signed_divide_const(left.as_const()?, right.as_const()?)
            }
            binary_term!(UInt32, Divide, left, right) => {
                checked_unsigned_divide_const(left.as_const()?, right.as_const()?)
            }
            binary_term!(Int32, Remainder, left, right) => {
                checked_signed_remainder_const(left.as_const()?, right.as_const()?)
            }
            binary_term!(UInt32, Remainder, left, right) => {
                checked_unsigned_remainder_const(left.as_const()?, right.as_const()?)
            }
            binary_term!(Bits32, ShiftLeft, left, right) => {
                // This untyped term denotes the shifted 32-bit pattern.
                // Signed C overflow is a separate expression obligation.
                Some(
                    left.as_const()?
                        .wrapping_shl(checked_shift_count_const(right.as_const()?)?),
                )
            }
            binary_term!(Int32, ShiftRight, left, right) => {
                checked_arithmetic_shift_right_const(left.as_const()?, right.as_const()?)
            }
            binary_term!(UInt32, ShiftRight, left, right) => {
                checked_logical_shift_right_const(left.as_const()?, right.as_const()?)
            }
            binary_term!(Bits32, BitwiseAnd, left, right) => {
                Some(left.as_const()? & right.as_const()?)
            }
            binary_term!(Bits32, BitwiseOr, left, right) => {
                Some(left.as_const()? | right.as_const()?)
            }
            binary_term!(Bits32, BitwiseXor, left, right) => {
                Some(left.as_const()? ^ right.as_const()?)
            }
            unary_term!(Bits32, BitwiseNot, value) => Some(!value.as_const()?),
            Self::If {
                condition,
                then_term,
                else_term,
            } => match condition.as_ref() {
                ConditionTerm::Constant(true) => then_term.as_const(),
                ConditionTerm::Constant(false) => else_term.as_const(),
                _ => None,
            },
            Self::RangeFold { .. } => None,
        }
    }

    pub(in crate::kernel) fn subtract_one_base(&self) -> Option<Self> {
        match self {
            binary_term!(Int32, Subtract, left, right) if right.as_ref() == &Self::constant(1) => {
                Some(left.as_ref().clone())
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn is_subtract_one(&self) -> bool {
        self.subtract_one_base().is_some()
    }

    pub(in crate::kernel) fn add_const_base(&self, value: u32) -> Option<Self> {
        match self {
            binary_term!(Int32, Add, left, right) if right.as_ref() == &Self::constant(value) => {
                Some(left.as_ref().clone())
            }
            binary_term!(Int32, Add, left, right) if left.as_ref() == &Self::constant(value) => {
                Some(right.as_ref().clone())
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn add_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            binary_term!(Int32, Add, left, right) => match (left.as_ref(), right.as_ref()) {
                (base, int32_constant!(value)) => Some((base.clone(), constant_u32(*value))),
                (int32_constant!(value), base) => Some((base.clone(), constant_u32(*value))),
                _ => None,
            },
            _ => None,
        }
    }

    /// `left + right` at `int32`, folded (`Self::add_at`).
    pub(crate) fn add(left: Self, right: Self) -> Self {
        Self::add_at(MachineIntegerType::Int32, left, right)
    }

    /// An operand of a 32-bit operator at `format`: its word (σ and a narrow
    /// widening name their operand's word, rules K1 and K8), with a root
    /// constant in `format` (`design/machine-integers.md`, "Every
    /// format its own nodes").
    pub(crate) fn operand32(format: MachineIntegerType, term: Self) -> Self {
        match (format, term.into_word32()) {
            (MachineIntegerType::UInt32, int32_constant!(value)) => {
                Self::uint32_constant(constant_u32(value))
            }
            (_, word) => word,
        }
    }

    /// `self` with a root 32-bit constant spelled in `format`; any other
    /// term unchanged.
    pub(crate) fn constant_in32(self, format: MachineIntegerType) -> Self {
        match self.word_constant() {
            Some(value) => Self::constant_at32(format, value),
            None => self,
        }
    }

    /// The constant `value` in `format`'s spelling.
    pub(crate) fn constant_at32(format: MachineIntegerType, value: u32) -> Self {
        match format {
            MachineIntegerType::UInt32 => Self::uint32_constant(value),
            _ => Self::constant(value),
        }
    }

    /// The bits of a root 32-bit constant, either spelling.
    fn word_constant(&self) -> Option<u32> {
        match self {
            bits32_constant!(value) => Some(constant_u32(*value)),
            _ => None,
        }
    }

    /// The 32-bit operator node `left op right` at `format`, unfolded.
    fn node32(format: MachineIntegerType, op: MachineBinaryOp, left: Self, right: Self) -> Self {
        Self::Binary {
            op,
            format,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// `left + right` at the 32-bit `format`, folded: constants, `x + 0`,
    /// and the cancellations `x + (y - x)`, `(y - x) + x`, `(0 - x) + (x + y)`
    /// and their mirrors, matching operands of `format` only.
    pub(crate) fn add_at(format: MachineIntegerType, left: Self, right: Self) -> Self {
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        let subtraction = |term: &Self| match term {
            binary_term!(Bits32 @ found, Subtract, base, subtrahend) if *found == format => {
                Some((base.as_ref().clone(), subtrahend.as_ref().clone()))
            }
            _ => None,
        };
        let addition = |term: &Self| match term {
            binary_term!(Bits32 @ found, Add, base, addend) if *found == format => {
                Some((base.as_ref().clone(), addend.as_ref().clone()))
            }
            _ => None,
        };
        if let (Some(left), Some(right)) = (left.word_constant(), right.word_constant()) {
            return Self::constant_at32(format, left.wrapping_add(right));
        }
        if let Some((base, subtrahend)) = subtraction(&right)
            && subtrahend == left
        {
            return base;
        }
        if let Some((base, subtrahend)) = subtraction(&left)
            && subtrahend == right
        {
            return base;
        }
        for (negation, sum) in [(&left, &right), (&right, &left)] {
            if let (Some((zero, subtrahend)), Some((first, second))) =
                (subtraction(negation), addition(sum))
                && zero.word_constant() == Some(0)
            {
                if subtrahend == first {
                    return second;
                }
                if subtrahend == second {
                    return first;
                }
            }
        }
        if right.word_constant() == Some(0) {
            return left;
        }
        if left.word_constant() == Some(0) {
            return right;
        }
        Self::node32(format, MachineBinaryOp::Add, left, right)
    }

    /// `left - right` at `int32`, folded (`Self::subtract_at`).
    pub(in crate::kernel) fn subtract(left: Self, right: Self) -> Self {
        Self::subtract_at(MachineIntegerType::Int32, left, right)
    }

    /// `left - right` at the 32-bit `format`, folded: constants, `x - 0`,
    /// `x - x`, and the cancellation of a shared addend of two sums or of a
    /// sum and one of its addends, matching operands of `format` only.
    pub(crate) fn subtract_at(format: MachineIntegerType, left: Self, right: Self) -> Self {
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        let addition = |term: &Self| match term {
            binary_term!(Bits32 @ found, Add, base, addend) if *found == format => {
                Some((base.as_ref().clone(), addend.as_ref().clone()))
            }
            _ => None,
        };
        if let (Some(left), Some(right)) = (left.word_constant(), right.word_constant()) {
            return Self::constant_at32(format, left.wrapping_sub(right));
        }
        if right.word_constant() == Some(0) {
            return left;
        }
        if left == right {
            return Self::constant_at32(format, 0);
        }
        let zero = || Self::constant_at32(format, 0);
        if let (Some((left_base, left_addend)), Some((right_base, right_addend))) =
            (addition(&left), addition(&right))
        {
            if left_base == right_base {
                return Self::subtract_at(format, left_addend, right_addend);
            }
            if left_base == right_addend {
                return Self::subtract_at(format, left_addend, right_base);
            }
            if left_addend == right_base {
                return Self::subtract_at(format, left_base, right_addend);
            }
            if left_addend == right_addend {
                return Self::subtract_at(format, left_base, right_base);
            }
        }
        if let Some((left_base, left_addend)) = addition(&left) {
            if left_base == right {
                return left_addend;
            }
            if left_addend == right {
                return left_base;
            }
        }
        if let Some((right_base, right_addend)) = addition(&right) {
            if left == right_base {
                return Self::subtract_at(format, zero(), right_addend);
            }
            if left == right_addend {
                return Self::subtract_at(format, zero(), right_base);
            }
        }
        Self::node32(format, MachineBinaryOp::Subtract, left, right)
    }

    /// `left * right` at `int32`, folded (`Self::multiply_at`).
    pub(crate) fn multiply(left: Self, right: Self) -> Self {
        Self::multiply_at(MachineIntegerType::Int32, left, right)
    }

    /// `left * right` at the 32-bit `format`, folded: constants, `x * 1`
    /// and `x * 0`.
    pub(crate) fn multiply_at(format: MachineIntegerType, left: Self, right: Self) -> Self {
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(left), Some(right)) => Self::constant_at32(format, left.wrapping_mul(right)),
            (_, Some(1)) => left,
            (Some(1), _) => right,
            (_, Some(0)) | (Some(0), _) => Self::constant_at32(format, 0),
            _ => Self::node32(format, MachineBinaryOp::Multiply, left, right),
        }
    }

    pub(in crate::kernel) fn divide(left: Self, right: Self) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (&left, &right) {
            (int32_constant!(left), int32_constant!(right)) => {
                match checked_signed_divide_const(constant_u32(*left), constant_u32(*right)) {
                    Some(value) => Self::constant(value),
                    None => binary_node!(
                        Int32,
                        Divide,
                        Box::new(Self::constant(constant_u32(*left))),
                        Box::new(Self::constant(constant_u32(*right))),
                    ),
                }
            }
            (_, int32_constant!(1)) => left,
            _ => binary_node!(Int32, Divide, Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn unsigned_divide(left: Self, right: Self) -> Self {
        let format = MachineIntegerType::UInt32;
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(left_bits), Some(right_bits)) => {
                match checked_unsigned_divide_const(left_bits, right_bits) {
                    Some(value) => Self::constant_at32(format, value),
                    None => Self::node32(format, MachineBinaryOp::Divide, left, right),
                }
            }
            (_, Some(1)) => left,
            _ => Self::node32(format, MachineBinaryOp::Divide, left, right),
        }
    }

    pub(in crate::kernel) fn remainder(left: Self, right: Self) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (&left, &right) {
            (int32_constant!(left), int32_constant!(right)) => {
                match checked_signed_remainder_const(constant_u32(*left), constant_u32(*right)) {
                    Some(value) => Self::constant(value),
                    None => binary_node!(
                        Int32,
                        Remainder,
                        Box::new(Self::constant(constant_u32(*left))),
                        Box::new(Self::constant(constant_u32(*right))),
                    ),
                }
            }
            _ => binary_node!(Int32, Remainder, Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn unsigned_remainder(left: Self, right: Self) -> Self {
        let format = MachineIntegerType::UInt32;
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(left_bits), Some(right_bits)) => {
                match checked_unsigned_remainder_const(left_bits, right_bits) {
                    Some(value) => Self::constant_at32(format, value),
                    None => Self::node32(format, MachineBinaryOp::Remainder, left, right),
                }
            }
            _ => Self::node32(format, MachineBinaryOp::Remainder, left, right),
        }
    }

    pub(in crate::kernel) fn shift_left(left: Self, right: Self) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (&left, &right) {
            (int32_constant!(left), int32_constant!(right)) => {
                match checked_signed_shift_left_const(constant_u32(*left), constant_u32(*right)) {
                    Some(value) => Self::constant(value),
                    None => binary_node!(
                        Int32,
                        ShiftLeft,
                        Box::new(Self::constant(constant_u32(*left))),
                        Box::new(Self::constant(constant_u32(*right))),
                    ),
                }
            }
            _ => binary_node!(Int32, ShiftLeft, Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn unsigned_shift_left(left: Self, right: Self) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (&left, &right) {
            (int32_constant!(left), int32_constant!(right)) => {
                match checked_shift_count_const(constant_u32(*right)) {
                    Some(count) => Self::constant(constant_u32(*left).wrapping_shl(count)),
                    None => binary_node!(
                        Int32,
                        ShiftLeft,
                        Box::new(Self::constant(constant_u32(*left))),
                        Box::new(Self::constant(constant_u32(*right))),
                    ),
                }
            }
            (_, int32_constant!(0)) => left,
            _ => binary_node!(Int32, ShiftLeft, Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn arithmetic_shift_right(left: Self, right: Self) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (&left, &right) {
            (int32_constant!(left), int32_constant!(right)) => {
                match checked_arithmetic_shift_right_const(
                    constant_u32(*left),
                    constant_u32(*right),
                ) {
                    Some(value) => Self::constant(value),
                    None => binary_node!(
                        Int32,
                        ShiftRight,
                        Box::new(Self::constant(constant_u32(*left))),
                        Box::new(Self::constant(constant_u32(*right))),
                    ),
                }
            }
            (_, int32_constant!(0)) => left,
            _ => binary_node!(Int32, ShiftRight, Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn logical_shift_right(left: Self, right: Self) -> Self {
        let format = MachineIntegerType::UInt32;
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(left_bits), Some(right_bits)) => {
                match checked_logical_shift_right_const(left_bits, right_bits) {
                    Some(value) => Self::constant_at32(format, value),
                    None => Self::node32(format, MachineBinaryOp::ShiftRight, left, right),
                }
            }
            (_, Some(0)) => left,
            _ => Self::node32(format, MachineBinaryOp::ShiftRight, left, right),
        }
    }

    pub(in crate::kernel) fn bitwise_and(left: Self, right: Self) -> Self {
        Self::bitwise_and_at(MachineIntegerType::Int32, left, right)
    }

    /// `left & right` at the 32-bit `format`, folded.
    pub(crate) fn bitwise_and_at(format: MachineIntegerType, left: Self, right: Self) -> Self {
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(left), Some(right)) => Self::constant_at32(format, left & right),
            (_, Some(u32::MAX)) => left,
            (Some(u32::MAX), _) => right,
            (_, Some(0)) | (Some(0), _) => Self::constant_at32(format, 0),
            _ if left == right => left,
            _ => Self::node32(format, MachineBinaryOp::BitwiseAnd, left, right),
        }
    }

    pub(in crate::kernel) fn bitwise_or(left: Self, right: Self) -> Self {
        Self::bitwise_or_at(MachineIntegerType::Int32, left, right)
    }

    /// `left | right` at the 32-bit `format`, folded.
    pub(crate) fn bitwise_or_at(format: MachineIntegerType, left: Self, right: Self) -> Self {
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(left), Some(right)) => Self::constant_at32(format, left | right),
            (_, Some(0)) => left,
            (Some(0), _) => right,
            (_, Some(u32::MAX)) | (Some(u32::MAX), _) => Self::constant_at32(format, u32::MAX),
            _ if left == right => left,
            _ => Self::node32(format, MachineBinaryOp::BitwiseOr, left, right),
        }
    }

    pub(in crate::kernel) fn bitwise_xor(left: Self, right: Self) -> Self {
        Self::bitwise_xor_at(MachineIntegerType::Int32, left, right)
    }

    /// `left ^ right` at the 32-bit `format`, normalized: the operands of a
    /// chain of `format`'s `^` are sorted, pairs cancel, and the constants
    /// fold into one.
    pub(crate) fn bitwise_xor_at(format: MachineIntegerType, left: Self, right: Self) -> Self {
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        fn flatten(
            format: MachineIntegerType,
            term: MachineTerm,
            constant: &mut u32,
            terms: &mut Vec<MachineTerm>,
        ) {
            match term {
                bits32_constant!(value) => *constant ^= constant_u32(value),
                MachineTerm::Binary {
                    op: MachineBinaryOp::BitwiseXor,
                    format: found,
                    left,
                    right,
                } if found == format => {
                    flatten(format, *left, constant, terms);
                    flatten(format, *right, constant, terms);
                }
                term => terms.push(term),
            }
        }

        let mut constant = 0;
        let mut terms = Vec::new();
        flatten(format, left, &mut constant, &mut terms);
        flatten(format, right, &mut constant, &mut terms);
        terms.sort();

        let mut normalized = Vec::new();
        let mut index = 0;
        while index < terms.len() {
            let mut end = index + 1;
            while end < terms.len() && terms[end] == terms[index] {
                end += 1;
            }
            if (end - index) % 2 == 1 {
                normalized.push(terms[index].clone());
            }
            index = end;
        }
        if constant != 0 {
            normalized.push(Self::constant_at32(format, constant));
            normalized.sort();
        }

        normalized
            .into_iter()
            .reduce(|left, right| Self::node32(format, MachineBinaryOp::BitwiseXor, left, right))
            .unwrap_or(Self::constant_at32(format, 0))
    }

    pub(in crate::kernel) fn bitwise_not(value: Self) -> Self {
        Self::bitwise_not_at(MachineIntegerType::Int32, value)
    }

    /// `~value` at the 32-bit `format`, folded.
    pub(crate) fn bitwise_not_at(format: MachineIntegerType, value: Self) -> Self {
        let value = Self::operand32(format, value);
        if let Some(bits) = value.word_constant() {
            return Self::constant_at32(format, !bits);
        }
        match value {
            Self::Unary {
                format: found,
                op: MachineUnaryOp::BitwiseNot,
                operand,
            } if found == format => *operand,
            value => Self::Unary {
                format,
                op: MachineUnaryOp::BitwiseNot,
                operand: Box::new(value),
            },
        }
    }

    /// `left << right` at `uint32`: the bits shifted, a constant count below
    /// 32 folding a constant operand, a zero count the operand itself.
    pub(crate) fn uint32_shift_left(left: Self, right: Self) -> Self {
        let format = MachineIntegerType::UInt32;
        let (left, right) = (
            Self::operand32(format, left),
            Self::operand32(format, right),
        );
        match (left.word_constant(), right.word_constant()) {
            (Some(bits), Some(count)) if checked_shift_count_const(count).is_some() => {
                Self::constant_at32(format, bits.wrapping_shl(count))
            }
            (_, Some(0)) => left,
            _ => Self::node32(format, MachineBinaryOp::ShiftLeft, left, right),
        }
    }

    pub fn if_then_else(condition: ConditionTerm, then_term: Self, else_term: Self) -> Self {
        match condition {
            ConditionTerm::Constant(true) => then_term,
            ConditionTerm::Constant(false) => else_term,
            _ if then_term == else_term => then_term,
            condition => Self::If {
                condition: Box::new(condition),
                then_term: Box::new(then_term),
                else_term: Box::new(else_term),
            },
        }
    }

    pub fn range_fold(
        start: Self,
        end: Self,
        initial: Self,
        accumulator: Variable,
        item: Variable,
        body: Self,
    ) -> Self {
        if start == end {
            return initial;
        }

        // No one-step shortcut above the endpoint check. The fold's carrier is
        // the signed `int32` range its empty and append laws certify
        // (`prove_integer_range_fold_empty` guards with the signed order,
        // `prove_integer_range_fold_append` adds the non-wrapping
        // `end < i32::MAX` premise), so only a *signed* one-element range may
        // unroll. `Self::add` wraps in `2^32`, so `add(start, 1) == end` also
        // holds for `i32::MAX .. i32::MIN`, whose signed range is empty and
        // whose certified value is `initial` — unrolling it here would return
        // a step where the laws return `initial`. The concrete path below
        // decides exact one-element ranges (4 .. 5 unrolls once, `i32::MAX ..
        // i32::MIN` stays empty), and a symbolic pair that is one element
        // apart under one value of the start is opaque until an assumption
        // prefers a value, which is exactly what the laws' guards track.

        if let (Some(start_value), Some(end_value)) = (
            signed_bitvector_constant(&start),
            signed_bitvector_constant(&end),
        ) {
            let length = end_value - start_value;
            if length <= 0 {
                return initial;
            }
            // A concrete range unrolls step by step: the steps are the
            // range's own length, charged as deterministic work, never cut
            // by a count.
            crate::instrumentation::record_deterministic_work(
                usize::try_from(length).unwrap_or(usize::MAX),
            );
            let mut value = initial;
            for index in start_value..end_value {
                value = instantiate_range_fold_step(
                    &body,
                    accumulator,
                    &value,
                    item,
                    &signed_i64_bitvector_constant(index),
                );
            }
            return value;
        }

        Self::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        }
    }
}

// The original term type is retained as the shared arena for both machine
// widths.  These helpers use dedicated constructors and constants for 64-bit
// values, so a 64-bit value can never be mistaken for a wrapped 32-bit one by
// the existing C paths.
fn int64_constant(term: &MachineTerm) -> Option<i64> {
    match term {
        int64_constant!(value) => Some(constant_i64(*value)),
        cast_term!(Int64From32, value) => match value.as_ref() {
            bits32_constant!(value) => Some(i64::from(constant_u32(*value) as i32)),
            _ => int64_constant(value),
        },
        cast_term!(Int64FromUInt32, value) => match value.as_ref() {
            bits32_constant!(value) => Some(i64::from(constant_u32(*value))),
            _ => int64_constant(value),
        },
        MachineTerm::Binary {
            format: MachineIntegerType::Int64,
            op,
            left,
            right,
        } => {
            let left = int64_constant(left)?;
            match op {
                MachineBinaryOp::Add => left.checked_add(int64_constant(right)?),
                MachineBinaryOp::Subtract => left.checked_sub(int64_constant(right)?),
                MachineBinaryOp::Multiply => left.checked_mul(int64_constant(right)?),
                MachineBinaryOp::Divide => checked_int64_divide_const(left, int64_constant(right)?),
                MachineBinaryOp::Remainder => {
                    checked_int64_remainder_const(left, int64_constant(right)?)
                }
                MachineBinaryOp::ShiftLeft => {
                    let count = int64_shift_count_constant(right)?;
                    (left >= 0 && count < 64)
                        .then_some(left.checked_shl(count)?)
                        .filter(|value| *value >= 0)
                }
                MachineBinaryOp::ShiftRight => {
                    let count = int64_shift_count_constant(right)?;
                    (count < 64).then(|| left >> count)
                }
                MachineBinaryOp::BitwiseAnd => Some(left & int64_constant(right)?),
                MachineBinaryOp::BitwiseOr => Some(left | int64_constant(right)?),
                MachineBinaryOp::BitwiseXor => Some(left ^ int64_constant(right)?),
            }
        }
        MachineTerm::Unary {
            format: MachineIntegerType::Int64,
            op: MachineUnaryOp::BitwiseNot,
            operand,
        } => Some(!int64_constant(operand)?),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => match condition.as_ref() {
            ConditionTerm::Constant(true) => int64_constant(then_term),
            ConditionTerm::Constant(false) => int64_constant(else_term),
            _ => None,
        },
        _ => uint64_constant(term).map(|bits| bits as i64),
    }
}

fn uint64_constant(term: &MachineTerm) -> Option<u64> {
    match term {
        uint64_constant!(value) => Some(constant_u64(*value)),
        // Null converts to the integer zero, exactly as evaluating the C
        // cast `(uint64)p` yields it. The address term reaches a proof only
        // when a pointer proved null is substituted into `(uint64)p`.
        MachineTerm::IntegerAddress(pointer, _) if **pointer == Address::null() => Some(0),
        cast_term!(UInt64From32, value) => match value.as_ref() {
            bits32_constant!(value) => Some(u64::from(constant_u32(*value))),
            _ => uint64_constant(value),
        },
        cast_term!(UInt64FromInt32, value) => match value.as_ref() {
            bits32_constant!(value) => Some((constant_u32(*value) as i32 as i64) as u64),
            _ => uint64_constant(value),
        },
        cast_term!(UInt64FromInt64, value) => match value.as_ref() {
            int64_constant!(value) => Some(constant_i64(*value) as u64),
            _ => uint64_constant(value),
        },
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op,
            left,
            right,
        } => {
            let left = uint64_constant(left)?;
            match op {
                MachineBinaryOp::Add => Some(left.wrapping_add(uint64_constant(right)?)),
                MachineBinaryOp::Subtract => Some(left.wrapping_sub(uint64_constant(right)?)),
                MachineBinaryOp::Multiply => Some(left.wrapping_mul(uint64_constant(right)?)),
                MachineBinaryOp::Divide => {
                    checked_uint64_divide_const(left, uint64_constant(right)?)
                }
                MachineBinaryOp::Remainder => {
                    checked_uint64_remainder_const(left, uint64_constant(right)?)
                }
                MachineBinaryOp::ShiftLeft => {
                    let count = int64_shift_count_constant(right)?;
                    (count < 64).then_some(left.wrapping_shl(count))
                }
                MachineBinaryOp::ShiftRight => {
                    let count = int64_shift_count_constant(right)?;
                    if count >= 64 {
                        None
                    } else {
                        Some(left >> count)
                    }
                }
                MachineBinaryOp::BitwiseAnd => Some(left & uint64_constant(right)?),
                MachineBinaryOp::BitwiseOr => Some(left | uint64_constant(right)?),
                MachineBinaryOp::BitwiseXor => Some(left ^ uint64_constant(right)?),
            }
        }
        MachineTerm::Unary {
            format: MachineIntegerType::UInt64,
            op: MachineUnaryOp::BitwiseNot,
            operand,
        } => Some(!uint64_constant(operand)?),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => match condition.as_ref() {
            ConditionTerm::Constant(true) => uint64_constant(then_term),
            ConditionTerm::Constant(false) => uint64_constant(else_term),
            _ => None,
        },
        _ => None,
    }
}

const FLOAT_ROUND_EXTRA_BITS: u32 = 4;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DecodedFloat {
    Nan,
    Infinity {
        negative: bool,
    },
    Finite {
        negative: bool,
        significand: u64,
        exponent: i32,
    },
}

fn float32_bits_as_const(term: &MachineTerm) -> Option<u32> {
    match term {
        bits32_constant!(value) => Some(constant_u32(*value)),
        MachineTerm::Float32Negate(value) => Some(float32_bits_as_const(value)? ^ 0x8000_0000),
        MachineTerm::Float32Binary {
            operator,
            left,
            right,
        } => Some(float_binary_bits(
            u64::from(float32_bits_as_const(left)?),
            u64::from(float32_bits_as_const(right)?),
            8,
            23,
            *operator,
        ) as u32),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => match condition.as_ref() {
            ConditionTerm::Constant(true) => float32_bits_as_const(then_term),
            ConditionTerm::Constant(false) => float32_bits_as_const(else_term),
            _ => None,
        },
        _ => None,
    }
}

fn float64_bits_as_const(term: &MachineTerm) -> Option<u64> {
    match term {
        uint64_constant!(value) => Some(constant_u64(*value)),
        MachineTerm::Float64Negate(value) => {
            Some(float64_bits_as_const(value)? ^ 0x8000_0000_0000_0000)
        }
        MachineTerm::Float64Binary {
            operator,
            left,
            right,
        } => Some(float_binary_bits(
            float64_bits_as_const(left)?,
            float64_bits_as_const(right)?,
            11,
            52,
            *operator,
        )),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => match condition.as_ref() {
            ConditionTerm::Constant(true) => float64_bits_as_const(then_term),
            ConditionTerm::Constant(false) => float64_bits_as_const(else_term),
            _ => None,
        },
        _ => None,
    }
}

fn decode_float_bits(bits: u64, exponent_bits: u32, fraction_bits: u32, bias: i32) -> DecodedFloat {
    let sign_bit = 1u64 << (exponent_bits + fraction_bits);
    let exponent_mask = (1u64 << exponent_bits) - 1;
    let fraction_mask = (1u64 << fraction_bits) - 1;
    let exponent = (bits >> fraction_bits) & exponent_mask;
    let fraction = bits & fraction_mask;
    let negative = bits & sign_bit != 0;
    if exponent == exponent_mask {
        return if fraction == 0 {
            DecodedFloat::Infinity { negative }
        } else {
            DecodedFloat::Nan
        };
    }
    if exponent == 0 {
        return DecodedFloat::Finite {
            negative,
            significand: fraction,
            exponent: 1 - bias - fraction_bits as i32,
        };
    }
    DecodedFloat::Finite {
        negative,
        significand: (1u64 << fraction_bits) | fraction,
        exponent: exponent as i32 - bias - fraction_bits as i32,
    }
}

fn canonical_float_nan(exponent_bits: u32, fraction_bits: u32) -> u64 {
    (((1u64 << exponent_bits) - 1) << fraction_bits) | (1u64 << (fraction_bits - 1))
}

fn float_infinity(negative: bool, exponent_bits: u32, fraction_bits: u32) -> u64 {
    let sign = if negative {
        1u64 << (exponent_bits + fraction_bits)
    } else {
        0
    };
    sign | (((1u64 << exponent_bits) - 1) << fraction_bits)
}

fn float_zero(negative: bool, exponent_bits: u32, fraction_bits: u32) -> u64 {
    if negative {
        1u64 << (exponent_bits + fraction_bits)
    } else {
        0
    }
}

fn shift_right_jam(value: u128, shift: u32) -> u128 {
    if shift == 0 {
        return value;
    }
    if shift >= 128 {
        return u128::from(value != 0);
    }
    let truncated = value >> shift;
    let lost = value & ((1u128 << shift) - 1);
    truncated | u128::from(lost != 0)
}

/// Round a nonnegative integer right shift to nearest, ties to even.
///
/// The floating-point conversions in this slice operate on the exact integer
/// significands of IEEE values. Keeping the rounding here in integer space
/// makes the result independent of the host floating-point environment.
pub(in crate::kernel) fn round_right_to_even(value: u128, shift: u32) -> u128 {
    if shift == 0 {
        return value;
    }
    if shift >= 128 {
        return 0;
    }
    let truncated = value >> shift;
    let remainder = value & ((1u128 << shift) - 1);
    let halfway = 1u128 << (shift - 1);
    if remainder > halfway || (remainder == halfway && truncated & 1 != 0) {
        truncated + 1
    } else {
        truncated
    }
}

fn round_float_result(
    negative: bool,
    significand: u128,
    exponent: i32,
    exponent_bits: u32,
    fraction_bits: u32,
    bias: i32,
) -> u64 {
    let sign = if negative {
        1u64 << (exponent_bits + fraction_bits)
    } else {
        0
    };
    if significand == 0 {
        return sign;
    }

    let precision = fraction_bits + 1;
    let min_normal_exponent = 1 - bias;
    let min_subnormal_exponent = min_normal_exponent - fraction_bits as i32;
    let max_encoded_exponent = (1u32 << exponent_bits) - 1;
    let max_normal_exponent = max_encoded_exponent as i32 - 1 - bias;

    let significand_bits = 128 - significand.leading_zeros();
    let mut unbiased_exponent = exponent + significand_bits as i32 - 1;
    if unbiased_exponent >= min_normal_exponent {
        // The fraction field below is the significand with its leading bit
        // masked off, so the significand has to be normalized to exactly
        // `precision` bits first. Cancellation and division can leave fewer
        // than that: `1.0 - 0.96875` reaches here as one bit at exponent -5,
        // which without the left shift would encode as 2^-5 * (1 + 2^-52)
        // rather than 2^-5.
        let mut rounded = if significand_bits > precision {
            round_right_to_even(significand, significand_bits - precision)
        } else {
            significand << (precision - significand_bits)
        };
        if rounded >= (1u128 << precision) {
            rounded >>= 1;
            unbiased_exponent += 1;
        }
        if unbiased_exponent > max_normal_exponent {
            return float_infinity(negative, exponent_bits, fraction_bits);
        }
        let encoded_exponent = (unbiased_exponent + bias) as u64;
        return sign
            | (encoded_exponent << fraction_bits)
            | ((rounded as u64) & ((1u64 << fraction_bits) - 1));
    }

    let rounded = if exponent >= min_subnormal_exponent {
        significand << (exponent - min_subnormal_exponent) as u32
    } else {
        round_right_to_even(significand, (min_subnormal_exponent - exponent) as u32)
    };
    if rounded >= (1u128 << fraction_bits) {
        // Rounding the largest subnormal up crosses into the least normal.
        return sign | (1u64 << fraction_bits);
    }
    if rounded == 0 {
        return sign;
    }
    sign | rounded as u64
}

fn negate_decoded_float(value: DecodedFloat) -> DecodedFloat {
    match value {
        DecodedFloat::Nan => DecodedFloat::Nan,
        DecodedFloat::Infinity { negative } => DecodedFloat::Infinity {
            negative: !negative,
        },
        DecodedFloat::Finite {
            negative,
            significand,
            exponent,
        } => DecodedFloat::Finite {
            negative: !negative,
            significand,
            exponent,
        },
    }
}

fn add_decoded_floats(
    left: DecodedFloat,
    right: DecodedFloat,
    exponent_bits: u32,
    fraction_bits: u32,
    bias: i32,
) -> u64 {
    match (left, right) {
        (DecodedFloat::Nan, _) | (_, DecodedFloat::Nan) => {
            return canonical_float_nan(exponent_bits, fraction_bits);
        }
        (DecodedFloat::Infinity { negative: left }, DecodedFloat::Infinity { negative: right }) => {
            return if left == right {
                float_infinity(left, exponent_bits, fraction_bits)
            } else {
                canonical_float_nan(exponent_bits, fraction_bits)
            };
        }
        (DecodedFloat::Infinity { negative }, _) | (_, DecodedFloat::Infinity { negative }) => {
            return float_infinity(negative, exponent_bits, fraction_bits);
        }
        _ => {}
    }

    let DecodedFloat::Finite {
        negative: left_negative,
        significand: left_significand,
        exponent: left_exponent,
    } = left
    else {
        unreachable!();
    };
    let DecodedFloat::Finite {
        negative: right_negative,
        significand: right_significand,
        exponent: right_exponent,
    } = right
    else {
        unreachable!();
    };
    if left_significand == 0 && right_significand == 0 {
        return float_zero(
            left_negative && right_negative,
            exponent_bits,
            fraction_bits,
        );
    }

    let exponent = left_exponent.max(right_exponent);
    let left = shift_right_jam(
        u128::from(left_significand) << FLOAT_ROUND_EXTRA_BITS,
        (exponent - left_exponent) as u32,
    );
    let right = shift_right_jam(
        u128::from(right_significand) << FLOAT_ROUND_EXTRA_BITS,
        (exponent - right_exponent) as u32,
    );
    let signed_left = if left_negative {
        -(left as i128)
    } else {
        left as i128
    };
    let signed_right = if right_negative {
        -(right as i128)
    } else {
        right as i128
    };
    let sum = signed_left + signed_right;
    if sum == 0 {
        return float_zero(false, exponent_bits, fraction_bits);
    }
    let negative = sum < 0;
    let magnitude = if negative {
        (-sum) as u128
    } else {
        sum as u128
    };
    round_float_result(
        negative,
        magnitude,
        exponent - FLOAT_ROUND_EXTRA_BITS as i32,
        exponent_bits,
        fraction_bits,
        bias,
    )
}

fn multiply_decoded_floats(
    left: DecodedFloat,
    right: DecodedFloat,
    exponent_bits: u32,
    fraction_bits: u32,
    bias: i32,
) -> u64 {
    let (left_negative, left_significand, left_exponent) = match left {
        DecodedFloat::Nan => return canonical_float_nan(exponent_bits, fraction_bits),
        DecodedFloat::Infinity { negative } => match right {
            DecodedFloat::Finite { significand: 0, .. } => {
                return canonical_float_nan(exponent_bits, fraction_bits);
            }
            DecodedFloat::Nan => return canonical_float_nan(exponent_bits, fraction_bits),
            _ => {
                return float_infinity(
                    negative ^ decoded_sign(right),
                    exponent_bits,
                    fraction_bits,
                );
            }
        },
        DecodedFloat::Finite {
            negative,
            significand,
            exponent,
        } => (negative, significand, exponent),
    };
    let (right_negative, right_significand, right_exponent) = match right {
        DecodedFloat::Nan => return canonical_float_nan(exponent_bits, fraction_bits),
        DecodedFloat::Infinity { negative } => {
            if left_significand == 0 {
                return canonical_float_nan(exponent_bits, fraction_bits);
            }
            return float_infinity(negative ^ left_negative, exponent_bits, fraction_bits);
        }
        DecodedFloat::Finite {
            negative,
            significand,
            exponent,
        } => (negative, significand, exponent),
    };
    let negative = left_negative ^ right_negative;
    if left_significand == 0 || right_significand == 0 {
        return float_zero(negative, exponent_bits, fraction_bits);
    }
    let product = u128::from(left_significand) * u128::from(right_significand);
    let target_top = fraction_bits + FLOAT_ROUND_EXTRA_BITS;
    let highest_bit = 127 - product.leading_zeros();
    let (significand, exponent) = if highest_bit > target_top {
        (
            shift_right_jam(product, highest_bit - target_top),
            left_exponent + right_exponent + (highest_bit - target_top) as i32,
        )
    } else {
        (
            product << (target_top - highest_bit),
            left_exponent + right_exponent - (target_top - highest_bit) as i32,
        )
    };
    round_float_result(
        negative,
        significand,
        exponent,
        exponent_bits,
        fraction_bits,
        bias,
    )
}

fn decoded_sign(value: DecodedFloat) -> bool {
    match value {
        DecodedFloat::Nan => false,
        DecodedFloat::Infinity { negative } | DecodedFloat::Finite { negative, .. } => negative,
    }
}

fn divide_decoded_floats(
    left: DecodedFloat,
    right: DecodedFloat,
    exponent_bits: u32,
    fraction_bits: u32,
    bias: i32,
) -> u64 {
    let negative = decoded_sign(left) ^ decoded_sign(right);
    match (left, right) {
        (DecodedFloat::Nan, _) | (_, DecodedFloat::Nan) => {
            return canonical_float_nan(exponent_bits, fraction_bits);
        }
        (DecodedFloat::Infinity { .. }, DecodedFloat::Infinity { .. })
        | (
            DecodedFloat::Finite { significand: 0, .. },
            DecodedFloat::Finite { significand: 0, .. },
        ) => {
            return canonical_float_nan(exponent_bits, fraction_bits);
        }
        (DecodedFloat::Infinity { .. }, _) => {
            return float_infinity(negative, exponent_bits, fraction_bits);
        }
        (_, DecodedFloat::Infinity { .. }) => {
            return float_zero(negative, exponent_bits, fraction_bits);
        }
        (DecodedFloat::Finite { significand: 0, .. }, _) => {
            return float_zero(negative, exponent_bits, fraction_bits);
        }
        (_, DecodedFloat::Finite { significand: 0, .. }) => {
            return float_infinity(negative, exponent_bits, fraction_bits);
        }
        _ => {}
    }

    let DecodedFloat::Finite {
        significand: left_significand,
        exponent: left_exponent,
        ..
    } = left
    else {
        unreachable!();
    };
    let DecodedFloat::Finite {
        significand: right_significand,
        exponent: right_exponent,
        ..
    } = right
    else {
        unreachable!();
    };
    let working_shift = fraction_bits + FLOAT_ROUND_EXTRA_BITS;
    let target_bits = working_shift + 1;
    let numerator = u128::from(left_significand) << working_shift;
    let divisor = u128::from(right_significand);
    // The working quotient is at least 2^3: the dividend significand is at
    // least 1 while the divisor is narrower than the working shift by more
    // than three bits, so the bit length below always measures a real bit.
    let magnitude_bits = 128 - (numerator / divisor).leading_zeros();
    // Normalize the quotient so its leading bit sits exactly at
    // `working_shift`, mirroring `multiply_decoded_floats`. That shape keeps
    // every rounding shift inside `round_float_result` at least two bits
    // wide, so the sticky bit in bit 0 can never collide with the rounding
    // bit. Jamming the remainder into a variable-width quotient instead
    // mis-rounds: a one-bit subnormal shift lands the sticky exactly on the
    // rounding bit (the subnormal-division regression), and fewer quotient
    // bits than the format precision treats the jammed value as exact,
    // drifting by many ulps.
    //
    // A positive adjustment widens the numerator and divides again; a
    // negative one divides by a widened divisor. Either way the single
    // division's remainder becomes the sticky bit, so the normalized
    // quotient is within one unit of the exact value, and bit 0 being clear
    // means the division was exact. Both widenings fit u128: the numerator
    // shift is bounded by the measured magnitude against the divisor width,
    // and the divisor shift by the quotient's own bit length.
    let adjust = target_bits as i32 - magnitude_bits as i32;
    let (quotient, exponent) = if adjust >= 0 {
        let numerator = u128::from(left_significand) << (working_shift + adjust as u32);
        let quotient = numerator / divisor;
        let sticky = u128::from(!numerator.is_multiple_of(divisor));
        (
            quotient | sticky,
            left_exponent - right_exponent - working_shift as i32 - adjust,
        )
    } else {
        let divisor = divisor << (-adjust as u32);
        let quotient = numerator / divisor;
        let sticky = u128::from(!numerator.is_multiple_of(divisor));
        (
            quotient | sticky,
            left_exponent - right_exponent - working_shift as i32 - adjust,
        )
    };
    round_float_result(
        negative,
        quotient,
        exponent,
        exponent_bits,
        fraction_bits,
        bias,
    )
}

fn float_binary_bits(
    left: u64,
    right: u64,
    exponent_bits: u32,
    fraction_bits: u32,
    operator: FloatBinaryOperator,
) -> u64 {
    let bias = (1i32 << (exponent_bits - 1)) - 1;
    let left = decode_float_bits(left, exponent_bits, fraction_bits, bias);
    let right = decode_float_bits(right, exponent_bits, fraction_bits, bias);
    match operator {
        FloatBinaryOperator::Add => {
            add_decoded_floats(left, right, exponent_bits, fraction_bits, bias)
        }
        FloatBinaryOperator::Subtract => add_decoded_floats(
            left,
            negate_decoded_float(right),
            exponent_bits,
            fraction_bits,
            bias,
        ),
        FloatBinaryOperator::Multiply => {
            multiply_decoded_floats(left, right, exponent_bits, fraction_bits, bias)
        }
        FloatBinaryOperator::Divide => {
            divide_decoded_floats(left, right, exponent_bits, fraction_bits, bias)
        }
    }
}

fn int64_shift_count_constant(term: &MachineTerm) -> Option<u32> {
    let value = match term {
        bits32_constant!(value) => u64::from(constant_u32(*value)),
        int64_constant!(value) if constant_i64(*value) >= 0 => constant_i64(*value) as u64,
        uint64_constant!(value) => constant_u64(*value),
        _ => return None,
    };
    u32::try_from(value).ok()
}

impl MachineTerm {
    pub(crate) fn int64_from_32(value: Self) -> Self {
        let value = value.into_word32();
        match value {
            int32_constant!(value) => Self::int64_constant(i64::from(constant_u32(value) as i32)),
            int64_constant!(_) | cast_term!(Int64From32, _) => value,
            value => MachineTerm::legacy_cast(MachineCastSpelling::Int64From32, Box::new(value)),
        }
    }

    pub(crate) fn uint32_from_64(value: Self) -> Self {
        // Children are already constructed bottom-up. Only inspect the root:
        // rescanning the operand here makes repeated conversions quadratic.
        fn root(value: MachineTerm) -> MachineTerm {
            match value {
                uint64_constant!(bits) => MachineTerm::constant(constant_u64(bits) as u32),
                int64_constant!(bits) => MachineTerm::constant(constant_i64(bits) as u32),
                cast_term!(UInt64From32, value)
                | cast_term!(Int64From32, value)
                | cast_term!(Int64FromUInt32, value)
                | cast_term!(UInt64FromInt32, value) => *value,
                value => {
                    MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(value))
                }
            }
        }
        match value {
            Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: a,
                right: b,
            } => match (*a, *b) {
                (a, uint64_constant!(b)) => {
                    Self::add(root(a), Self::constant(constant_u64(b) as u32))
                }
                (uint64_constant!(a), b) => {
                    Self::add(Self::constant(constant_u64(a) as u32), root(b))
                }
                (a, b) => root(Self::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(a),
                    right: Box::new(b),
                }),
            },
            Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Subtract,
                left: a,
                right: b,
            } => match (*a, *b) {
                (a, uint64_constant!(b)) => {
                    Self::subtract(root(a), Self::constant(constant_u64(b) as u32))
                }
                (a, b) => root(Self::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Subtract,
                    left: Box::new(a),
                    right: Box::new(b),
                }),
            },
            value => root(value),
        }
    }

    pub(crate) fn uint64_from_32(value: Self) -> Self {
        let value = value.into_word32();
        match value {
            int32_constant!(value) => Self::uint64_constant(u64::from(constant_u32(value))),
            uint64_constant!(_) | cast_term!(UInt64From32, _) => value,
            value => MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(value)),
        }
    }

    pub(crate) fn int64_from_uint32(value: Self) -> Self {
        let value = value.into_word32();
        match value {
            int32_constant!(value) => Self::int64_constant(i64::from(constant_u32(value))),
            int64_constant!(_) | cast_term!(Int64FromUInt32, _) => value,
            value => {
                MachineTerm::legacy_cast(MachineCastSpelling::Int64FromUInt32, Box::new(value))
            }
        }
    }

    pub(crate) fn uint64_from_int32(value: Self) -> Self {
        let value = value.into_word32();
        match value {
            int32_constant!(value) => {
                Self::uint64_constant((constant_u32(value) as i32 as i64) as u64)
            }
            uint64_constant!(_) | cast_term!(UInt64FromInt32, _) => value,
            value => {
                MachineTerm::legacy_cast(MachineCastSpelling::UInt64FromInt32, Box::new(value))
            }
        }
    }

    pub(crate) fn uint64_from_int64(value: Self) -> Self {
        match value {
            int64_constant!(value) => Self::uint64_constant(constant_i64(value) as u64),
            uint64_constant!(_) | cast_term!(UInt64FromInt64, _) => value,
            value => {
                MachineTerm::legacy_cast(MachineCastSpelling::UInt64FromInt64, Box::new(value))
            }
        }
    }

    /// Both typed values use the same 64-bit bitvector carrier. Signedness
    /// determines the following operators; this conversion preserves the bits.
    pub(crate) fn int64_from_uint64_bits(value: Self) -> Self {
        match value {
            uint64_constant!(bits) => Self::int64_constant(constant_u64(bits) as i64),
            cast_term!(UInt64FromInt64, value) => *value,
            cast_term!(UInt64From32, value) => Self::int64_from_uint32(*value),
            cast_term!(UInt64FromInt32, value) => Self::int64_from_32(*value),
            value => value,
        }
    }

    pub(crate) fn int64_as_const(&self) -> Option<i64> {
        int64_constant(self)
    }

    pub(crate) fn uint64_as_const(&self) -> Option<u64> {
        uint64_constant(self)
    }

    /// The raw bits of either signed or unsigned 64-bit constant arithmetic.
    /// Equality is insensitive to the source signedness, so its constructor
    /// may compare both constant families without changing C semantics.
    pub(crate) fn bitvector64_as_const(&self) -> Option<u64> {
        self.uint64_as_const()
            .or_else(|| self.int64_as_const().map(|value| value as u64))
    }

    fn int64_binary(
        left: Self,
        right: Self,
        operation: impl FnOnce(i64, i64) -> Option<i64>,
        op: MachineBinaryOp,
    ) -> Self {
        let constructor = |left, right| Self::Binary {
            format: MachineIntegerType::Int64,
            op,
            left,
            right,
        };
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => operation(left, right)
                .map(Self::int64_constant)
                .unwrap_or_else(|| {
                    constructor(
                        Box::new(Self::int64_constant(left)),
                        Box::new(Self::int64_constant(right)),
                    )
                }),
            _ => constructor(Box::new(left), Box::new(right)),
        }
    }

    /// Logical arithmetic preserves symbolic operations so a stored raw
    /// operation has an exact Surface spelling. Only two literal operands
    /// use the constant evaluator; algebraic identities belong to checking.
    pub(crate) fn logical_machine_binary(
        format: MachineIntegerType,
        op: MachineBinaryOp,
        left: Self,
        right: Self,
    ) -> Self {
        let literal = |value: &Self| {
            matches!(
                value,
                bits32_constant!(_) | int64_constant!(_) | uint64_constant!(_)
            )
        };
        if literal(&left) && literal(&right) {
            return Self::machine_binary(format, op, left, right);
        }
        if format.format().bits() == 32 {
            return Self::node32(
                format,
                op,
                Self::operand32(format, left),
                Self::operand32(format, right),
            );
        }
        Self::Binary {
            format,
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// `left op right` at a 32- or 64-bit `format`, through the operator's
    /// smart constructor. Division, remainder and right shift are signed at
    /// a signed format and unsigned at an unsigned one; every other operator
    /// is built at the format asked, over operands in that format
    /// (`design/machine-integers.md`, "Every format its own nodes"). No
    /// other format has [`Self::Binary`] nodes.
    pub(crate) fn machine_binary(
        format: MachineIntegerType,
        op: MachineBinaryOp,
        left: Self,
        right: Self,
    ) -> Self {
        use MachineBinaryOp as Op;
        use MachineIntegerType as Ty;
        match (format, op) {
            (Ty::Int32 | Ty::UInt32, Op::Add) => Self::add_at(format, left, right),
            (Ty::Int32 | Ty::UInt32, Op::Subtract) => Self::subtract_at(format, left, right),
            (Ty::Int32 | Ty::UInt32, Op::Multiply) => Self::multiply_at(format, left, right),
            (Ty::Int32, Op::Divide) => Self::divide(left, right),
            (Ty::UInt32, Op::Divide) => Self::unsigned_divide(left, right),
            (Ty::Int32, Op::Remainder) => Self::remainder(left, right),
            (Ty::UInt32, Op::Remainder) => Self::unsigned_remainder(left, right),
            (Ty::Int32, Op::ShiftLeft) => Self::shift_left(left, right),
            (Ty::UInt32, Op::ShiftLeft) => Self::uint32_shift_left(left, right),
            (Ty::Int32, Op::ShiftRight) => Self::arithmetic_shift_right(left, right),
            (Ty::UInt32, Op::ShiftRight) => Self::logical_shift_right(left, right),
            (Ty::Int32 | Ty::UInt32, Op::BitwiseAnd) => Self::bitwise_and_at(format, left, right),
            (Ty::Int32 | Ty::UInt32, Op::BitwiseOr) => Self::bitwise_or_at(format, left, right),
            (Ty::Int32 | Ty::UInt32, Op::BitwiseXor) => Self::bitwise_xor_at(format, left, right),
            (Ty::Int64, Op::Add) => Self::int64_add(left, right),
            (Ty::Int64, Op::Subtract) => Self::int64_subtract(left, right),
            (Ty::Int64, Op::Multiply) => Self::int64_multiply(left, right),
            (Ty::Int64, Op::Divide) => Self::int64_divide(left, right),
            (Ty::Int64, Op::Remainder) => Self::int64_remainder(left, right),
            (Ty::Int64, Op::ShiftLeft) => Self::int64_shift_left(left, right),
            (Ty::Int64, Op::ShiftRight) => Self::int64_arithmetic_shift_right(left, right),
            (Ty::Int64, Op::BitwiseAnd) => Self::int64_bitwise_and(left, right),
            (Ty::Int64, Op::BitwiseOr) => Self::int64_bitwise_or(left, right),
            (Ty::Int64, Op::BitwiseXor) => Self::int64_bitwise_xor(left, right),
            (Ty::UInt64, Op::Add) => Self::uint64_add(left, right),
            (Ty::UInt64, Op::Subtract) => Self::uint64_subtract(left, right),
            (Ty::UInt64, Op::Multiply) => Self::uint64_multiply(left, right),
            (Ty::UInt64, Op::Divide) => Self::uint64_divide(left, right),
            (Ty::UInt64, Op::Remainder) => Self::uint64_remainder(left, right),
            (Ty::UInt64, Op::ShiftLeft) => Self::uint64_shift_left(left, right),
            (Ty::UInt64, Op::ShiftRight) => Self::uint64_logical_shift_right(left, right),
            (Ty::UInt64, Op::BitwiseAnd) => Self::uint64_bitwise_and(left, right),
            (Ty::UInt64, Op::BitwiseOr) => Self::uint64_bitwise_or(left, right),
            (Ty::UInt64, Op::BitwiseXor) => Self::uint64_bitwise_xor(left, right),
            (Ty::Int8 | Ty::UInt8 | Ty::Int16 | Ty::UInt16, op)
                if crate::kernel::primitives::is_native_narrow_operator(op) =>
            {
                Self::narrow_binary(format, op, left, right)
            }
            _ => panic!("no {format:?} machine binary operator yet"),
        }
    }

    /// `op operand` at a 32- or 64-bit `format`, through the operator's
    /// smart constructor.
    pub(crate) fn machine_unary(
        format: MachineIntegerType,
        op: MachineUnaryOp,
        operand: Self,
    ) -> Self {
        match (format, op) {
            (
                MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                MachineUnaryOp::BitwiseNot,
            ) => Self::bitwise_not_at(format, operand),
            (MachineIntegerType::Int64, MachineUnaryOp::BitwiseNot) => {
                Self::int64_bitwise_not(operand)
            }
            (MachineIntegerType::UInt64, MachineUnaryOp::BitwiseNot) => {
                Self::uint64_bitwise_not(operand)
            }
            (
                MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16,
                MachineUnaryOp::BitwiseNot,
            ) => match operand.narrow_constant_bits(format) {
                Some(bits) => Self::narrow_constant(format, !bits),
                None => Self::Unary {
                    format,
                    op: MachineUnaryOp::BitwiseNot,
                    operand: Box::new(operand),
                },
            },
            _ => panic!("no {format:?} machine unary operator yet"),
        }
    }

    /// The native 8- or 16-bit constant of `format` whose bits are `bits`
    /// reduced modulo 2^N: a value of its own width, not a 32-bit word.
    pub(crate) fn narrow_constant(format: MachineIntegerType, bits: u128) -> Self {
        let format = format.format();
        Self::machine_constant(
            MachineIntegerConstant::from_bits(format, bits & format.mask())
                .expect("masked bits fit the format"),
        )
    }

    /// The bits of a native constant of the 8- or 16-bit `format`, if this
    /// term is one. One match on the root.
    pub(crate) fn narrow_constant_bits(&self, format: MachineIntegerType) -> Option<u128> {
        match self {
            native_constant!(constant_format, bits) if *constant_format == format => Some(*bits),
            _ => None,
        }
    }

    /// `left op right` at an 8- or 16-bit `format`, a native node of that
    /// width (decision G4: `+ - * & | ^ <<`). Two constants fold modulo
    /// 2^N; a shift folds only by a constant count below N, as the 32-bit
    /// shifts do. Every other operand pair is the node itself. One match on
    /// each root.
    fn narrow_binary(
        format: MachineIntegerType,
        op: MachineBinaryOp,
        left: Self,
        right: Self,
    ) -> Self {
        use MachineBinaryOp as Op;
        crate::instrumentation::record_deterministic_work(1);
        let width = format.format().bits();
        let folded = match (left.narrow_constant_bits(format), op) {
            (Some(bits), Op::ShiftLeft) => {
                let count = right
                    .narrow_constant_bits(format)
                    .or_else(|| right.as_const().map(u128::from));
                count
                    .filter(|count| *count < u128::from(width))
                    .map(|count| bits << count)
            }
            (Some(a), op) => right.narrow_constant_bits(format).and_then(|b| match op {
                Op::Add => Some(a.wrapping_add(b)),
                Op::Subtract => Some(a.wrapping_sub(b)),
                Op::Multiply => Some(a.wrapping_mul(b)),
                Op::BitwiseAnd => Some(a & b),
                Op::BitwiseOr => Some(a | b),
                Op::BitwiseXor => Some(a ^ b),
                _ => None,
            }),
            (None, _) => None,
        };
        match folded {
            Some(bits) => Self::narrow_constant(format, bits),
            None => Self::Binary {
                format,
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_add(left: Self, right: Self) -> Self {
        Self::int64_binary(left, right, i64::checked_add, MachineBinaryOp::Add)
    }

    pub(crate) fn int64_subtract(left: Self, right: Self) -> Self {
        if left == right {
            return Self::int64_constant(0);
        }
        Self::int64_binary(left, right, i64::checked_sub, MachineBinaryOp::Subtract)
    }

    pub(crate) fn int64_multiply(left: Self, right: Self) -> Self {
        // As at the narrower widths: neither identity can overflow.
        match (int64_constant(&left), int64_constant(&right)) {
            (_, Some(1)) => return left,
            (Some(1), _) => return right,
            (_, Some(0)) | (Some(0), _) => return Self::int64_constant(0),
            _ => {}
        }
        Self::int64_binary(left, right, i64::checked_mul, MachineBinaryOp::Multiply)
    }

    pub(crate) fn int64_divide(left: Self, right: Self) -> Self {
        Self::int64_binary(
            left,
            right,
            checked_int64_divide_const,
            MachineBinaryOp::Divide,
        )
    }

    pub(crate) fn int64_remainder(left: Self, right: Self) -> Self {
        Self::int64_binary(
            left,
            right,
            checked_int64_remainder_const,
            MachineBinaryOp::Remainder,
        )
    }

    pub(crate) fn int64_shift_left(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if left >= 0 && count < 64 => left
                .checked_shl(count)
                .filter(|value| *value >= 0)
                .map(Self::int64_constant)
                .unwrap_or_else(|| Self::Binary {
                    format: MachineIntegerType::Int64,
                    op: MachineBinaryOp::ShiftLeft,
                    left: Box::new(Self::int64_constant(left)),
                    right: Box::new(right),
                }),
            _ => Self::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::ShiftLeft,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_arithmetic_shift_right(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if count < 64 => Self::int64_constant(left >> count),
            _ => Self::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::ShiftRight,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_bitwise_and(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => Self::int64_constant(left & right),
            _ => Self::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::BitwiseAnd,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_bitwise_or(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => Self::int64_constant(left | right),
            _ => Self::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::BitwiseOr,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_bitwise_xor(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => Self::int64_constant(left ^ right),
            _ => Self::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::BitwiseXor,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_bitwise_not(value: Self) -> Self {
        match int64_constant(&value) {
            Some(value) => Self::int64_constant(!value),
            None => Self::Unary {
                format: MachineIntegerType::Int64,
                op: MachineUnaryOp::BitwiseNot,
                operand: Box::new(value),
            },
        }
    }

    fn uint64_binary(
        left: Self,
        right: Self,
        operation: impl FnOnce(u64, u64) -> Option<u64>,
        op: MachineBinaryOp,
    ) -> Self {
        let constructor = |left, right| Self::Binary {
            format: MachineIntegerType::UInt64,
            op,
            left,
            right,
        };
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => operation(left, right)
                .map(Self::uint64_constant)
                .unwrap_or_else(|| {
                    constructor(
                        Box::new(Self::uint64_constant(left)),
                        Box::new(Self::uint64_constant(right)),
                    )
                }),
            _ => constructor(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_add(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (uint64_constant!(0), _) => return right,
            (_, uint64_constant!(0)) => return left,
            // `(x - c) + c` is `x`: both operations wrap modulo 2^64, so
            // the identity holds for every `x`. A fold's end restated one
            // lower and stepped back is the end itself.
            (
                Self::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Subtract,
                    left: inner,
                    right: taken,
                },
                uint64_constant!(added),
            ) if matches!(taken.as_ref(), uint64_constant!(taken) if constant_u64(*taken) == constant_u64(*added)) =>
            {
                return inner.as_ref().clone();
            }
            _ => {}
        }
        Self::uint64_binary(
            left,
            right,
            |left, right| Some(left.wrapping_add(right)),
            MachineBinaryOp::Add,
        )
    }

    pub(crate) fn uint64_subtract(left: Self, right: Self) -> Self {
        if matches!(right, uint64_constant!(0)) {
            return left;
        }
        // Atomic identities avoid comparing arbitrary operand trees on this
        // constructor's hot path. Compound operands can use the checked lemma
        // for a symbolic variable through ordinary substitution.
        if let (Self::Variable(a), Self::Variable(b)) = (&left, &right)
            && a == b
        {
            return Self::uint64_constant(0);
        }
        // `(x + c) - c` is `x`, by the same wrapping identity as in
        // `uint64_add`.
        if let (
            Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: inner,
                right: added,
            },
            uint64_constant!(taken),
        ) = (&left, &right)
            && matches!(added.as_ref(), uint64_constant!(added) if constant_u64(*added) == constant_u64(*taken))
        {
            return inner.as_ref().clone();
        }
        Self::uint64_binary(
            left,
            right,
            |left, right| Some(left.wrapping_sub(right)),
            MachineBinaryOp::Subtract,
        )
    }

    pub(crate) fn uint64_multiply(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), uint64_constant(&right)) {
            (_, Some(1)) => return left,
            (Some(1), _) => return right,
            (_, Some(0)) | (Some(0), _) => return Self::uint64_constant(0),
            _ => {}
        }
        Self::uint64_binary(
            left,
            right,
            |left, right| Some(left.wrapping_mul(right)),
            MachineBinaryOp::Multiply,
        )
    }

    pub(crate) fn uint64_divide(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            checked_uint64_divide_const,
            MachineBinaryOp::Divide,
        )
    }

    pub(crate) fn uint64_remainder(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            checked_uint64_remainder_const,
            MachineBinaryOp::Remainder,
        )
    }

    pub(crate) fn uint64_shift_left(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if count < 64 => {
                Self::uint64_constant(left.wrapping_shl(count))
            }
            _ => Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::ShiftLeft,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_logical_shift_right(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if count < 64 => Self::uint64_constant(left >> count),
            _ => Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::ShiftRight,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_bitwise_and(left: Self, right: Self) -> Self {
        // Masking a masked term masks by the intersection, an exact bit
        // identity that keeps tag arithmetic such as `(w & 1) & ~1` in a
        // shape the decision rules recognize.
        if let (
            Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseAnd,
                left: inner_left,
                right: inner_right,
            },
            Some(outer),
        ) = (&left, right.uint64_as_const())
        {
            match (inner_left.uint64_as_const(), inner_right.uint64_as_const()) {
                (None, Some(inner)) => {
                    return Self::uint64_bitwise_and(
                        inner_left.as_ref().clone(),
                        Self::uint64_constant(inner & outer),
                    );
                }
                (Some(inner), None) => {
                    return Self::uint64_bitwise_and(
                        inner_right.as_ref().clone(),
                        Self::uint64_constant(inner & outer),
                    );
                }
                _ => {}
            }
        }
        if right.uint64_as_const() == Some(0) || left.uint64_as_const() == Some(0) {
            return Self::uint64_constant(0);
        }
        // A mask distributes over an or with a constant: `(x | c) & m` is
        // `(x & m) | (c & m)`, so a tag set inside the mask reads back.
        if let (
            Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseOr,
                left: inner_left,
                right: inner_right,
            },
            Some(mask),
        ) = (&left, right.uint64_as_const())
        {
            let inner = match (inner_left.uint64_as_const(), inner_right.uint64_as_const()) {
                (None, Some(constant)) => Some((inner_left.as_ref().clone(), constant)),
                (Some(constant), None) => Some((inner_right.as_ref().clone(), constant)),
                _ => None,
            };
            if let Some((other, constant)) = inner {
                return Self::uint64_bitwise_or(
                    Self::uint64_bitwise_and(other, Self::uint64_constant(mask)),
                    Self::uint64_constant(constant & mask),
                );
            }
        }
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => Self::uint64_constant(left & right),
            _ => Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseAnd,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_bitwise_or(left: Self, right: Self) -> Self {
        // An or with a constant that covers every bit a masked term can
        // have is that constant: `(x & m) | k` is `k` when `m` lies inside
        // `k`.
        if let (
            Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseAnd,
                left: masked_left,
                right: masked_right,
            },
            Some(constant),
        ) = (&left, right.uint64_as_const())
            && let Some(mask) = masked_left
                .uint64_as_const()
                .or_else(|| masked_right.uint64_as_const())
            && mask & !constant == 0
        {
            return Self::uint64_constant(constant);
        }
        if left.uint64_as_const() == Some(0) {
            return right;
        }
        if right.uint64_as_const() == Some(0) {
            return left;
        }
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => Self::uint64_constant(left | right),
            _ => Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseOr,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_bitwise_xor(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => Self::uint64_constant(left ^ right),
            _ => Self::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseXor,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_bitwise_not(value: Self) -> Self {
        match uint64_constant(&value) {
            Some(value) => Self::uint64_constant(!value),
            None => Self::Unary {
                format: MachineIntegerType::UInt64,
                op: MachineUnaryOp::BitwiseNot,
                operand: Box::new(value),
            },
        }
    }
}

impl AddressOffset {
    pub fn constant(value: i64) -> Self {
        Self::Constant(value)
    }

    /// This offset as `sum(sext(index) * stride) + constant`, when every
    /// leaf is a constant or a scaled `int32` index: the scaled leaves and
    /// the constant. The sum is exact, with no wrap, so it describes the
    /// offset's integer value.
    pub(in crate::kernel) fn int32_scaled_linear_form(
        &self,
    ) -> Option<(Vec<(&SharedMachineIntegerTerm, i64)>, i64)> {
        // Each leaf's magnitude stays below `2^31 * 2^24`, so a sum of at
        // most this many of them, and their constant, fits in an `i64`.
        const MAX_LEAVES: usize = 64;
        const MAX_STRIDE: i64 = 1 << 24;
        const MAX_CONSTANT: i64 = 1 << 48;
        let mut scaled = Vec::new();
        let mut constant = 0i64;
        let mut pending = vec![self];
        let mut leaves = 0usize;
        while let Some(term) = pending.pop() {
            leaves += 1;
            if leaves > MAX_LEAVES {
                return None;
            }
            match term {
                Self::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                Self::Constant(value) if value.unsigned_abs() < MAX_CONSTANT as u64 => {
                    constant += value;
                }
                Self::Int32Scaled { value, byte_width }
                    if byte_width.unsigned_abs() <= MAX_STRIDE as u64 =>
                {
                    scaled.push((value, *byte_width));
                }
                _ => return None,
            }
        }
        Some((scaled, constant))
    }

    pub(in crate::kernel) fn as_const(&self) -> Option<i64> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) => None,
            Self::Add(left, right) => left.as_const()?.checked_add(right.as_const()?),
            Self::Int32Scaled { value, byte_width } => {
                let value = value.operand_view().word32_constant()? as i32 as i64;
                value.checked_mul(*byte_width)
            }
            Self::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let value = if *unsigned {
                    i64::try_from(value.operand_view().uint64_constant()?).ok()?
                } else {
                    value.operand_view().int64_constant()?
                };
                value.checked_mul(*byte_width)
            }
        }
    }

    pub(crate) fn add(left: Self, right: Self) -> Self {
        if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
            return Self::Constant(left + right);
        }
        if left.as_const() == Some(0) {
            return right;
        }
        if right.as_const() == Some(0) {
            return left;
        }
        // Keep a chain of constant byte displacements in one canonical
        // shape. Nested member access commonly forms `(base + outer) +
        // inner`, while aggregate copying starts from `base + total`;
        // treating those as distinct pointers would mint unrelated
        // symbolic loads for the same field.
        if let (Self::Add(base, trailing), Self::Constant(right)) = (&left, &right)
            && let Some(trailing) = trailing.as_const()
        {
            return Self::add((**base).clone(), Self::Constant(trailing + right));
        }
        Self::Add(Box::new(left), Box::new(right))
    }

    pub(crate) fn scale_int32(value: MachineTerm, byte_width: i64) -> Self {
        match value.as_const() {
            Some(value) => Self::Constant((value as i32 as i64) * byte_width),
            None => Self::scaled_int32_node(value, byte_width),
        }
    }

    pub(crate) fn scale_int64(value: MachineTerm, byte_width: i64, unsigned: bool) -> Self {
        // A widened int32 index times a u32 stride fits in signed int64.
        // Recover its exact pointer scale without interpreting a modular
        // int32 product as an address displacement.
        if !unsigned {
            if let cast_term!(Int64From32, index) = &value
                && u32::try_from(byte_width).is_ok()
            {
                return Self::scale_int32(index.as_ref().clone(), byte_width);
            }
            if let MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Multiply,
                left,
                right,
            } = &value
            {
                for (index, stride) in [(left, right), (right, left)] {
                    if let (cast_term!(Int64From32, index), int64_constant!(stride)) =
                        (index.as_ref(), stride.as_ref())
                        && let Ok(stride) = u32::try_from(constant_i64(*stride))
                        && let Some(width) = i64::from(stride).checked_mul(byte_width)
                        && u32::try_from(width).is_ok()
                    {
                        return Self::scale_int32(index.as_ref().clone(), width);
                    }
                }
            }
        }
        let constant = if unsigned {
            value.uint64_as_const().and_then(|value| {
                i64::try_from(value)
                    .ok()
                    .and_then(|value| value.checked_mul(byte_width))
            })
        } else {
            value
                .int64_as_const()
                .and_then(|value| value.checked_mul(byte_width))
        };
        match constant {
            Some(value) => Self::Constant(value),
            None => Self::scaled_int64_node(value, byte_width, unsigned),
        }
    }
}

impl ConditionTerm {
    /// The value this condition has because its two operands are the same
    /// term, when it is a comparison of that kind.
    ///
    /// A term compared with itself is equal to itself, and no less or
    /// greater than itself, whatever value it denotes: `t <= t`, `t >= t`
    /// and `t == t` are true, `t < t`, `t > t` and `t != t` are false. The
    /// check is syntactic identity only, never simplification, so it costs
    /// one structural comparison. Floating-point comparisons are excluded
    /// because a NaN is not equal to itself, and overflow conditions are not
    /// comparisons. Algebraic equality is excluded too: an algebraic term can
    /// be a malformed application the kernel deliberately leaves undecided.
    pub(crate) fn reflexive_value(&self) -> Option<bool> {
        match self {
            Self::PointerEqual(left, right) => (left == right).then_some(true),

            Self::Compare {
                relation,
                left,
                right,
                ..
            } => (left == right).then_some(!matches!(
                relation,
                CompareRelation::LessThan | CompareRelation::GreaterThan
            )),
            Self::IntegerLessEqual(left, right)
            | Self::IntegerGreaterEqual(left, right)
            | Self::IntegerEqual(left, right) => (left == right).then_some(true),
            Self::IntegerLessThan(left, right)
            | Self::IntegerGreaterThan(left, right)
            | Self::IntegerNotEqual(left, right) => (left == right).then_some(false),
            Self::AddressOffsetEqual(left, right) => (left == right).then_some(true),
            Self::AddressEqual(left, right) => (left == right).then_some(true),
            // A `Bool` value is two-valued, so it is equivalent to itself.
            Self::BoolEqual(left, right) => (left == right).then_some(true),
            Self::AlgebraicEqual(_, _)
            | Self::Constant(_)
            | Self::Variable(_)
            | Self::Overflows { .. }
            | Self::Float32(_)
            | Self::Float64(_)
            | Self::BoolApplication(_)
            | Self::BoolIf { .. }
            | Self::BoolLoad(..) => None,
        }
    }

    pub(crate) fn float32_compare(
        left: MachineTerm,
        right: MachineTerm,
        operator: ComparisonOperator,
    ) -> Self {
        match (left.float32_as_const(), right.float32_as_const()) {
            (Some(left), Some(right)) => Self::Constant(compare_float_bits(
                u64::from(left),
                u64::from(right),
                8,
                23,
                operator,
            )),
            _ => Self::Float32(FloatCondition::Comparison {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            }),
        }
    }

    pub(crate) fn float64_compare(
        left: MachineTerm,
        right: MachineTerm,
        operator: ComparisonOperator,
    ) -> Self {
        match (left.float64_as_const(), right.float64_as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(compare_float_bits(left, right, 11, 52, operator))
            }
            _ => Self::Float64(FloatCondition::Comparison {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            }),
        }
    }

    pub(crate) fn float32_classification(
        value: MachineTerm,
        classification: FloatClassification,
    ) -> Self {
        match value.float32_as_const() {
            Some(value) => {
                Self::Constant(classify_float_bits(u64::from(value), 8, 23, classification))
            }
            None => Self::Float32(FloatCondition::Classification {
                classification,
                value: Box::new(value),
            }),
        }
    }

    pub(crate) fn float64_classification(
        value: MachineTerm,
        classification: FloatClassification,
    ) -> Self {
        match value.float64_as_const() {
            Some(value) => Self::Constant(classify_float_bits(value, 11, 52, classification)),
            None => Self::Float64(FloatCondition::Classification {
                classification,
                value: Box::new(value),
            }),
        }
    }

    /// The native comparison `left REL right` of two 8- or 16-bit values of
    /// `format`, at that format: two constants fold. One match on each
    /// root.
    pub(crate) fn narrow_compare(
        format: MachineIntegerType,
        relation: CompareRelation,
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        use CompareRelation as R;
        crate::instrumentation::record_deterministic_work(1);
        let value = |term: &MachineTerm| {
            format
                .constant_from_term(term)
                .and_then(crate::kernel::MachineIntegerConstant::to_i128)
        };
        if let (Some(a), Some(b)) = (value(&left), value(&right)) {
            return Self::Constant(match relation {
                R::LessThan => a < b,
                R::LessEqual => a <= b,
                R::GreaterThan => a > b,
                R::GreaterEqual => a >= b,
                R::Equal => a == b,
            });
        }
        // Two constants fold; a comparison of a term with itself keeps its
        // structure, as the 32-bit constructors keep it: a reflexive
        // equality is a `transport` source naming its operand.
        Self::Compare {
            format,
            relation,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// The comparison `left REL right` at `format`, through the folding
    /// constructor of its width (`signed_less_than`, `uint64_less_than`,
    /// ...). An 8- or 16-bit comparison is a native comparison of its own
    /// format ([`Self::narrow_compare`]).
    pub(crate) fn machine_compare(
        format: MachineIntegerType,
        relation: CompareRelation,
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        use CompareRelation as R;
        use MachineIntegerType as Ty;
        match (format, relation) {
            (Ty::Int8 | Ty::Int16 | Ty::UInt8 | Ty::UInt16, relation) => {
                Self::narrow_compare(format, relation, left, right)
            }
            (Ty::Int32, R::LessThan) => Self::signed_less_than(left, right),
            (Ty::Int32, R::LessEqual) => Self::signed_less_equal(left, right),
            (Ty::Int32, R::GreaterThan) => Self::signed_greater_than(left, right),
            (Ty::Int32, R::GreaterEqual) => Self::signed_greater_equal(left, right),
            (Ty::Int32, R::Equal) => Self::equal(left, right),
            (Ty::UInt32, R::Equal) => Self::uint32_equal(left, right),
            (Ty::UInt32, R::LessThan) => Self::unsigned_less_than(left, right),
            (Ty::UInt32, R::LessEqual) => Self::unsigned_less_equal(left, right),
            (Ty::UInt32, R::GreaterThan) => Self::unsigned_greater_than(left, right),
            (Ty::UInt32, R::GreaterEqual) => Self::unsigned_greater_equal(left, right),
            (Ty::Int64, R::LessThan) => Self::int64_signed_less_than(left, right),
            (Ty::Int64, R::LessEqual) => Self::int64_signed_less_equal(left, right),
            (Ty::Int64, R::GreaterThan) => Self::int64_signed_greater_than(left, right),
            (Ty::Int64, R::GreaterEqual) => Self::int64_signed_greater_equal(left, right),
            (Ty::Int64 | Ty::UInt64, R::Equal) => Self::int64_equal(left, right),
            (Ty::UInt64, R::LessThan) => Self::uint64_less_than(left, right),
            (Ty::UInt64, R::LessEqual) => Self::uint64_less_equal(left, right),
            (Ty::UInt64, R::GreaterThan) => Self::uint64_greater_than(left, right),
            (Ty::UInt64, R::GreaterEqual) => Self::uint64_greater_equal(left, right),
            // Equality reads no sign: it is filed at the signed format.
            (Ty::Int128 | Ty::UInt128, R::Equal) => {
                match (
                    machine_constant_value(format, &left),
                    machine_constant_value(format, &right),
                ) {
                    (Some(left), Some(right)) => Self::Constant(left == right),
                    _ if left == right => Self::Constant(true),
                    _ => Self::Compare {
                        format: Ty::Int128,
                        relation,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            (Ty::Int128 | Ty::UInt128, relation) => {
                match (
                    machine_constant_value(format, &left),
                    machine_constant_value(format, &right),
                ) {
                    (Some(left), Some(right)) => Self::Constant(match relation {
                        R::LessThan => left < right,
                        R::LessEqual => left <= right,
                        R::GreaterThan => left > right,
                        R::GreaterEqual => left >= right,
                        R::Equal => left == right,
                    }),
                    _ => Self::Compare {
                        format,
                        relation,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
        }
    }

    /// The overflow test of `left op right` at `format`, through the folding
    /// constructor of its format.
    pub(crate) fn machine_overflows(
        format: MachineIntegerType,
        op: OverflowOperation,
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        use MachineIntegerType as Ty;
        use OverflowOperation as O;
        // A 32-bit overflow test reads its operands' words (rule K1).
        let (left, right) = if format.format().bits() == 32 {
            (left.into_word32(), right.into_word32())
        } else {
            (left, right)
        };
        match (format, op) {
            (Ty::Int32, O::Add) => Self::signed_add_overflows(left, right),
            (Ty::Int32, O::Subtract) => Self::signed_subtract_overflows(left, right),
            (Ty::Int32, O::Multiply) => Self::signed_multiply_overflows(left, right),
            (Ty::Int32, O::Divide) => Self::signed_divide_overflows(left, right),
            (Ty::Int32, O::ShiftLeft) => Self::signed_shift_left_overflows(left, right),
            (Ty::Int64, O::Add) => Self::int64_signed_add_overflows(left, right),
            (Ty::Int64, O::Subtract) => Self::int64_signed_subtract_overflows(left, right),
            (Ty::Int64, O::Multiply) => Self::int64_signed_multiply_overflows(left, right),
            (Ty::Int64, O::Divide) => Self::int64_signed_divide_overflows(left, right),
            (Ty::Int64, O::ShiftLeft) => Self::int64_signed_shift_left_overflows(left, right),
            // Every other format folds constant operands by the exact
            // result's range: an unsigned overflow is a wrap, a narrow one
            // leaves the narrow range.
            (format, op @ (O::Add | O::Subtract | O::Multiply)) => {
                match (
                    machine_constant_value(format, &left),
                    machine_constant_value(format, &right),
                ) {
                    (Some(a), Some(b)) => {
                        let exact = match op {
                            O::Add => a + b,
                            O::Subtract => a - b,
                            _ => a * b,
                        };
                        let (minimum, maximum) =
                            crate::kernel::machine_integer::range::range(format);
                        Self::Constant(exact < minimum || exact > maximum)
                    }
                    _ => Self::Overflows {
                        format,
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            (format, op) => Self::Overflows {
                format,
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_less_than(left: MachineTerm, right: MachineTerm) -> Self {
        match int64_signed_order_by_width(&left, &right, |left, right| left < right) {
            Some(value) => Self::Constant(value),
            None => Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_less_equal(left: MachineTerm, right: MachineTerm) -> Self {
        match int64_signed_order_by_width(&left, &right, |left, right| left <= right) {
            Some(value) => Self::Constant(value),
            None => Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_greater_than(left: MachineTerm, right: MachineTerm) -> Self {
        match int64_signed_order_by_width(&left, &right, |left, right| left > right) {
            Some(value) => Self::Constant(value),
            None => Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterThan,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_greater_equal(left: MachineTerm, right: MachineTerm) -> Self {
        match int64_signed_order_by_width(&left, &right, |left, right| left >= right) {
            Some(value) => Self::Constant(value),
            None => Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    /// Checked full-width guards for truncated index bounds and order.
    /// Order requires the upper endpoint to fit in the signed word range;
    /// low-word equality follows from exact full-width equality.
    pub(crate) fn uint64_index_order_guards(&self) -> Option<[Self; 2]> {
        fn wide(term: &MachineTerm) -> Option<MachineTerm> {
            match term {
                cast_term!(UInt32From64, value) => Some(value.as_ref().clone()),
                bits32_constant!(value) if constant_u32(*value) <= i32::MAX as u32 => Some(
                    MachineTerm::uint64_constant(u64::from(constant_u32(*value))),
                ),
                binary_term!(Int32, Add, left, right) if right.as_const().is_some() => {
                    let cast_term!(UInt32From64, value) = left.as_ref() else {
                        return None;
                    };
                    Some(MachineTerm::uint64_add(
                        value.as_ref().clone(),
                        MachineTerm::uint64_constant(right.as_const()? as u64),
                    ))
                }
                _ => None,
            }
        }
        if let Self::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: a,
            right: b,
        } = self
        {
            return Some([Self::int64_equal(wide(a)?, wide(b)?), Self::Constant(true)]);
        }
        let (a, b, strict) = match self {
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (a, b, true),
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (b, a, true),
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (a, b, false),
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (b, a, false),
            _ => return None,
        };
        if !strict && a.as_const() == Some(0) {
            let b = wide(b)?;
            return Some([
                Self::uint64_less_equal(b, MachineTerm::uint64_constant(i32::MAX as u64)),
                Self::Constant(true),
            ]);
        }
        let a = wide(a)?;
        if !strict
            && let Some(limit) = b.as_const()
            && limit <= i32::MAX as u32
        {
            return Some([
                Self::uint64_less_equal(a.clone(), MachineTerm::uint64_constant(limit as u64)),
                Self::Constant(true),
            ]);
        }
        let b = wide(b)?;
        Some([
            if strict {
                Self::uint64_less_than(a.clone(), b.clone())
            } else {
                Self::uint64_less_equal(a.clone(), b.clone())
            },
            Self::uint64_less_equal(b.clone(), MachineTerm::uint64_constant(i32::MAX as u64)),
        ])
    }

    /// Regroup two exact pointer displacements by full-width unsigned
    /// indices, `(p + a) + b` and `p + (a + b)`, only when the `uint64`
    /// addition `a + b` does not wrap: the returned condition,
    /// `to_integer(a) + to_integer(b) <= 18446744073709551615`, for the
    /// sum the regrouped side holds. Each
    /// displacement is one scaled unsigned 64-bit scalar or a nonnegative
    /// representable constant, at one stride. A full-width displacement is
    /// exact, so its byte offset is the index times the stride with no
    /// wrap of its own. A shared pointer base may precede them; other
    /// nested sums are refused.
    pub(crate) fn pointer_offset_uint64_association_guard(&self) -> Option<ConditionTerm> {
        fn scalar(offset: &AddressOffset, width: i64) -> Option<SharedMachineIntegerTerm> {
            match offset {
                AddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned: true,
                } if *byte_width == width => Some(value.clone()),
                AddressOffset::Constant(value) if *value >= 0 && value % width == 0 => {
                    Some(SharedMachineIntegerTerm::index(
                        MachineIntegerType::Int64,
                        MachineTerm::uint64_constant((value / width) as u64),
                    ))
                }
                _ => None,
            }
        }
        let (left, right) = self.pointer_offset_sides()?;
        for (expanded, indexed) in [(left, right), (right, left)] {
            let AddressOffset::Add(left, right) = expanded else {
                continue;
            };
            let (left, indexed) = match (left.as_ref(), indexed) {
                (AddressOffset::Add(base, index), AddressOffset::Add(other_base, sum))
                    if base == other_base =>
                {
                    (index.as_ref(), sum.as_ref())
                }
                _ => (left.as_ref(), indexed),
            };
            let AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            } = indexed
            else {
                continue;
            };
            if *byte_width <= 0 {
                continue;
            }
            let (Some(left), Some(right)) = (scalar(left, *byte_width), scalar(right, *byte_width))
            else {
                continue;
            };
            let children = [left.operand_view(), right.operand_view()]
                .map(|view| KernelTerm::retained_machine_operand(MachineIntegerType::UInt64, view));
            let raw = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                children.clone(),
            );
            let Some(sum) = crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node(
                &raw, &children,
            ) else {
                continue;
            };
            let expected = KernelTerm::retained_machine_operand(
                MachineIntegerType::UInt64,
                value.operand_view(),
            );
            if crate::kernel::shared_machine_syntax_equal(&sum, &expected) {
                // `to_integer(a) + to_integer(b) <= 18446744073709551615`:
                // the sum's integer value fits a `uint64`.
                let integer = |term: &MachineTerm| {
                    IntegerTerm::from_machine(MachineIntegerType::UInt64, term.clone())
                        .map(SharedIntegerTerm::from)
                };
                return Some(Self::IntegerLessEqual(
                    IntegerTerm::Add(
                        integer(left.structural_value())?,
                        integer(right.structural_value())?,
                    )
                    .into(),
                    IntegerTerm::Constant(num_bigint::BigInt::from(u64::MAX)).into(),
                ));
            }
        }
        None
    }

    /// Regroup two exact pointer displacements into one signed-word index
    /// only when that index addition does not wrap. Each displacement is one
    /// scaled scalar or a representable constant. A shared pointer base may
    /// precede them; other nested sums and full-width indices are refused.
    pub(crate) fn pointer_offset_association_guard(&self) -> Option<[SharedMachineIntegerTerm; 2]> {
        fn scalar(offset: &AddressOffset, width: i64) -> Option<SharedMachineIntegerTerm> {
            match offset {
                AddressOffset::Int32Scaled { value, byte_width } if *byte_width == width => {
                    Some(value.clone())
                }
                AddressOffset::Constant(value) if value % width == 0 => {
                    i32::try_from(value / width).ok().map(|value| {
                        SharedMachineIntegerTerm::index(
                            MachineIntegerType::Int32,
                            MachineTerm::constant(value as u32),
                        )
                    })
                }
                _ => None,
            }
        }
        let (left, right) = self.pointer_offset_sides()?;
        for (expanded, indexed) in [(left, right), (right, left)] {
            let AddressOffset::Add(left, right) = expanded else {
                continue;
            };
            // Source pointers can carry a symbolic byte offset before the
            // selected index. Cancel only an identical leading base, without
            // consulting aliases or traversing unrelated offset addends.
            let (left, indexed) = match (left.as_ref(), indexed) {
                (AddressOffset::Add(base, index), AddressOffset::Add(other_base, sum))
                    if base == other_base =>
                {
                    (index.as_ref(), sum.as_ref())
                }
                _ => (left.as_ref(), indexed),
            };
            let AddressOffset::Int32Scaled { value, byte_width } = indexed else {
                continue;
            };
            if !(*byte_width > 0 && *byte_width <= i64::from(u32::MAX)) {
                continue;
            }
            let (Some(left), Some(right)) = (scalar(left, *byte_width), scalar(right, *byte_width))
            else {
                continue;
            };
            let children = [left.operand_view(), right.operand_view()]
                .map(|view| KernelTerm::retained_machine_operand(MachineIntegerType::Int32, view));
            let raw = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                children.clone(),
            );
            let sum = crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node(
                &raw, &children,
            )?;
            let expected = KernelTerm::retained_machine_operand(value.ty(), value.operand_view());
            if crate::kernel::shared_machine_syntax_equal(&sum, &expected) {
                return Some([left, right]);
            }
        }
        None
    }

    pub(crate) fn uint64_less_than(left: MachineTerm, right: MachineTerm) -> Self {
        // A value masked by a constant is bounded by that mask, so a tag
        // read `word & m` is below any bound above `m`.
        if let (
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseAnd,
                left: masked_left,
                right: masked_right,
            },
            Some(bound),
        ) = (&left, right.uint64_as_const())
            && let Some(mask) = masked_left
                .uint64_as_const()
                .or_else(|| masked_right.uint64_as_const())
            && mask < bound
        {
            return Self::Constant(true);
        }
        // No unsigned value is below zero: `x < 0u` is the C test an
        // unsigned bounds check `x >= 0 && x < n` negates.
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left < right),
            (_, Some(0)) | (Some(u64::MAX), _) => Self::Constant(false),
            _ => Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_less_equal(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left <= right),
            // Zero is the least unsigned 64-bit value and `u64::MAX` the
            // greatest.
            (Some(0), _) | (_, Some(u64::MAX)) => Self::Constant(true),
            _ => Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_greater_than(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left > right),
            (Some(0), _) | (_, Some(u64::MAX)) => Self::Constant(false),
            _ => Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn uint64_greater_equal(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left >= right),
            (_, Some(0)) | (Some(u64::MAX), _) => Self::Constant(true),
            _ => Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    /// The pointer condition that decides an address comparison. Equal
    /// pointers have equal addresses, and an address is zero exactly when its
    /// pointer is null. Equal addresses do not make equal pointers (a pointer
    /// one past an object may have the next object's address), so this only
    /// decides the comparison and never replaces it as a fact
    /// (`ConditionTerm::int64_equal`). Any other address-versus-integer
    /// comparison stays undecided: an integer with no pointer origin never
    /// proves or refutes identity with an allocation.
    pub(crate) fn address_equality_as_pointer_equality(
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> Option<Self> {
        match (left, right) {
            (MachineTerm::IntegerAddress(left, _), MachineTerm::IntegerAddress(right, _)) => Some(
                Self::address_equal(left.as_ref().clone(), right.as_ref().clone()),
            ),
            (MachineTerm::IntegerAddress(pointer, _), other)
            | (other, MachineTerm::IntegerAddress(pointer, _))
                if other.uint64_as_const() == Some(0) =>
            {
                Some(Self::address_equal(
                    pointer.as_ref().clone(),
                    Address::null(),
                ))
            }
            _ => None,
        }
    }

    /// The same relation with its operands swapped, for looking up a stored
    /// fact in either orientation. Symmetric relations flip to their mirror
    /// image; other conditions are returned unchanged.
    pub(crate) fn flipped(&self) -> Self {
        match self {
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: right.clone(),
                right: left.clone(),
            },
            Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: right.clone(),
                right: left.clone(),
            },
            Self::AddressEqual(left, right) => Self::AddressEqual(right.clone(), left.clone()),
            Self::PointerEqual(left, right) => Self::PointerEqual(right.clone(), left.clone()),
            Self::AddressOffsetEqual(left, right) => {
                Self::AddressOffsetEqual(right.clone(), left.clone())
            }
            other => other.clone(),
        }
    }

    /// `address(pointer) & (alignment - 1) == 0`: the low address bits are
    /// zero. This is the kernel form of the spec proposition
    /// `aligned(pointer, alignment)`; `alignment` must be a power of two.
    pub(crate) fn pointer_aligned(pointer: Address, alignment: u64) -> Self {
        debug_assert!(alignment.is_power_of_two());
        Self::uint64_equal(
            MachineTerm::uint64_bitwise_and(
                MachineTerm::IntegerAddress(
                    Box::new(pointer),
                    crate::kernel::AddressObjectClass::NONE,
                ),
                MachineTerm::uint64_constant(alignment - 1),
            ),
            MachineTerm::uint64_constant(0),
        )
    }

    /// Recognizes the alignment shape in either operand order and with any
    /// constant spelling of the mask and the zero.
    pub(crate) fn as_pointer_alignment(&self) -> Option<(&Address, u64)> {
        use crate::kernel::MachineOperandView as V;
        let masked = match self {
            Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                if right.bitvector64_as_const() == Some(0) {
                    V::Legacy(left)
                } else if left.bitvector64_as_const() == Some(0) {
                    V::Legacy(right)
                } else {
                    return None;
                }
            }
            Self::IntegerEqual(left, right) => {
                let word = if right.as_const().is_some_and(|n| n == &0.into()) {
                    left
                } else if left.as_const().is_some_and(|n| n == &0.into()) {
                    right
                } else {
                    return None;
                };
                let IntegerTerm::Machine(word) = word.as_ref() else {
                    return None;
                };
                if word.ty().format().bits() != 64 {
                    return None;
                }
                word.operand_view()
            }
            _ => return None,
        };
        let (MachineIntegerType::UInt64, MachineBinaryOp::BitwiseAnd, [left, right]) =
            masked.binary()?
        else {
            return None;
        };
        fn address(word: V<'_>) -> Option<&Address> {
            let native = match word {
                V::Legacy(native) => Some(native),
                V::Shared(root) => root.machine_conversion_leaf(),
            }?;
            if let MachineTerm::IntegerAddress(pointer, _) = native {
                Some(pointer.as_ref())
            } else {
                None
            }
        }
        let (pointer, mask) = if let Some(pointer) = address(left) {
            (pointer, right)
        } else {
            (address(right)?, left)
        };
        let alignment = mask.uint64_constant()?.checked_add(1)?;
        alignment.is_power_of_two().then_some((pointer, alignment))
    }

    pub(crate) fn int64_equal(left: MachineTerm, right: MachineTerm) -> Self {
        if left == right {
            return Self::Constant(true);
        }
        // An address is zero exactly when its pointer is null. Two addresses
        // stay an address equality: equal addresses are not equal pointers.
        if let (MachineTerm::IntegerAddress(pointer, _), other)
        | (other, MachineTerm::IntegerAddress(pointer, _)) = (&left, &right)
            && other.uint64_as_const() == Some(0)
        {
            return Self::address_equal(pointer.as_ref().clone(), Address::null());
        }
        match (left.bitvector64_as_const(), right.bitvector64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => {
                let condition = Self::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(left),
                    right: Box::new(right),
                };
                // Alignment describes address bits, independently of the
                // object's class. Give C masks and `aligned` one canonical
                // proposition while leaving pointer-producing words intact.
                if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
                    return Self::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Binary {
                            format: MachineIntegerType::UInt64,
                            op: MachineBinaryOp::BitwiseAnd,
                            left: Box::new(MachineTerm::IntegerAddress(
                                Box::new(pointer.clone()),
                                crate::kernel::AddressObjectClass::NONE,
                            )),
                            right: Box::new(MachineTerm::uint64_constant(alignment - 1)),
                        }),
                        right: Box::new(MachineTerm::uint64_constant(0)),
                    };
                }
                condition
            }
        }
    }

    /// 64-bit equality reads no sign, so it is [`Self::int64_equal`].
    pub(crate) fn uint64_equal(left: MachineTerm, right: MachineTerm) -> Self {
        Self::int64_equal(left, right)
    }

    pub(crate) fn int64_signed_add_overflows(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left.checked_add(right).is_none()),
            _ if int64_add_interval_fits(
                left.int64_width_interval(),
                right.int64_width_interval(),
            ) =>
            {
                Self::Constant(false)
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_subtract_overflows(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left.checked_sub(right).is_none()),
            _ if int64_subtract_interval_fits(
                left.int64_width_interval(),
                right.int64_width_interval(),
            ) =>
            {
                Self::Constant(false)
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Subtract,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_multiply_overflows(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left.checked_mul(right).is_none()),
            _ => Self::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Multiply,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_divide_overflows(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(right == 0 || (left == i64::MIN && right == -1))
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Divide,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(crate) fn int64_signed_shift_left_overflows(left: MachineTerm, right: MachineTerm) -> Self {
        match (left.int64_as_const(), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) => Self::Constant(
                count >= 64 || left < 0 || left.checked_shl(count).is_none_or(|result| result < 0),
            ),
            _ => Self::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::ShiftLeft,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    /// The `uint32` order `left < right`: a native comparison at `uint32`.
    /// A value whose unsigned bound (a constant, a constant mask) lies below
    /// a constant bound decides it.
    pub(crate) fn unsigned_less_than(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        if let bits32_constant!(bound) = &right
            && left.unsigned32_upper_bound() < constant_u32(*bound)
        {
            return Self::Constant(true);
        }
        Self::uint32_compare(CompareRelation::LessThan, left, right)
    }

    pub(crate) fn unsigned_less_equal(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        if let bits32_constant!(bound) = &right
            && left.unsigned32_upper_bound() <= constant_u32(*bound)
        {
            return Self::Constant(true);
        }
        Self::uint32_compare(CompareRelation::LessEqual, left, right)
    }

    pub(crate) fn unsigned_greater_than(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        if let bits32_constant!(bound) = &right
            && left.unsigned32_upper_bound() <= constant_u32(*bound)
        {
            return Self::Constant(false);
        }
        Self::uint32_compare(CompareRelation::GreaterThan, left, right)
    }

    pub(crate) fn unsigned_greater_equal(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        if let bits32_constant!(bound) = &right
            && left.unsigned32_upper_bound() < constant_u32(*bound)
        {
            return Self::Constant(false);
        }
        Self::uint32_compare(CompareRelation::GreaterEqual, left, right)
    }

    /// The `uint32` order node, folded when both operands are constants.
    fn uint32_compare(relation: CompareRelation, left: MachineTerm, right: MachineTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(match relation {
                CompareRelation::LessThan => left < right,
                CompareRelation::LessEqual => left <= right,
                CompareRelation::GreaterThan => left > right,
                CompareRelation::GreaterEqual => left >= right,
                CompareRelation::Equal => left == right,
            }),
            _ => Self::Compare {
                format: MachineIntegerType::UInt32,
                relation,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_less_than(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) < (right as i32)),
            _ => Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_less_equal(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) <= (right as i32)),
            _ => Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_greater_than(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) > (right as i32)),
            _ => Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_greater_equal(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) >= (right as i32)),
            _ => Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn equal(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    /// The equality of two `uint32` values, a `uint32` term as written. It
    /// is the same fact as the `int32` equality of the same bits at the
    /// fact-identity and lookup-key level only (rule K6,
    /// [`ConditionTerm::comparison_fact`]).
    pub(crate) fn uint32_equal(left: MachineTerm, right: MachineTerm) -> Self {
        match Self::equal(left, right) {
            Self::Compare {
                format: _,
                relation: CompareRelation::Equal,
                left,
                right,
            } => Self::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            condition => condition,
        }
    }

    pub(crate) fn signed_add_overflows(left: MachineTerm, right: MachineTerm) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_add(right as i32).1)
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_subtract_overflows(
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        if right.as_const() == Some(0) {
            return Self::Constant(false);
        }
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_sub(right as i32).1)
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Subtract,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_multiply_overflows(
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_mul(right as i32).1)
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Multiply,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_divide_overflows(
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(left == i32::MIN as u32 && right == (-1i32) as u32)
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn signed_shift_left_overflows(
        left: MachineTerm,
        right: MachineTerm,
    ) -> Self {
        let (left, right) = (left.into_word32(), right.into_word32());
        match (left.as_const(), right.as_const()) {
            (Some(left_value), Some(right_value)) => {
                match signed_shift_left_overflows_const(left_value, right_value) {
                    Some(overflows) => Self::Constant(overflows),
                    None => Self::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::ShiftLeft,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            _ => Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::ShiftLeft,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub(in crate::kernel) fn address_offset_equal(
        left: AddressOffset,
        right: AddressOffset,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ if pointer_offsets_differ_by_residue(&left, &right) => Self::Constant(false),
            _ => Self::AddressOffsetEqual(Box::new(left), Box::new(right)),
        }
    }

    /// The numeric consequence of an established true pointer equality.
    /// Unlike `pointer_offset_sides`, this does not describe an equivalent
    /// proposition: equal addresses alone cannot prove full-value equality.
    pub(crate) fn true_pointer_offset_sides(&self) -> Option<(&AddressOffset, &AddressOffset)> {
        match self {
            Self::PointerEqual(a, b) if a.base == b.base => Some((&a.offset, &b.offset)),
            _ => self.pointer_offset_sides(),
        }
    }

    /// A common-base comparison's offset view, retaining the original
    /// condition as the supporting premise in callers' indexes.
    pub(crate) fn pointer_offset_sides(&self) -> Option<(&AddressOffset, &AddressOffset)> {
        match self {
            Self::AddressOffsetEqual(a, b) => Some((a, b)),
            Self::AddressEqual(a, b) if a.base == b.base => Some((&a.offset, &b.offset)),
            Self::PointerEqual(a, b)
                if a.base == b.base
                    && a.provenance() == b.provenance()
                    && a.bounds() == b.bounds() =>
            {
                Some((&a.offset, &b.offset))
            }
            _ => None,
        }
    }

    /// Pointer equality as logical lowering states it: a non-null pointer
    /// value compared with itself keeps its `AddressEqual` node instead of
    /// folding to `true`, so the fact raises to `p == p` and lowers back
    /// (`docs/internals/raise-lower-principle.md`, "Lowering is structural").
    /// Producers whose result must match a lowered goal use it too; checking
    /// decides the reflexive comparison (`ConditionTerm::reflexive_value`).
    pub(crate) fn logical_pointer_equal(left: Pointer, right: Pointer) -> Self {
        if left == right && !left.is_null() {
            let address = left.address().clone();
            return Self::AddressEqual(Box::new(address.clone()), Box::new(address));
        }
        Self::pointer_equal(left, right)
    }

    pub(crate) fn pointer_equal(left: Pointer, right: Pointer) -> Self {
        if (left.provenance() == right.provenance()
            && left.bounds() == right.bounds()
            && left.bounds_are_known() == right.bounds_are_known()
            && (left.bounds_are_known() || left.bounds_owner() == right.bounds_owner()))
            || (matches!(left.program_type(), ProgramType::FunctionPointer(_))
                && matches!(right.program_type(), ProgramType::FunctionPointer(_)))
        {
            // With the complete pointer domain already identical, only the
            // numeric coordinates remain. A logical word cast's coordinates
            // use the same uint64 classes as its original word. Keep this
            // reduction out of raw pointer equality, which provenance checks
            // also use: numbers alone must never supply a pointer domain.
            if left.address().integer_address_bits().is_some()
                || right.address().integer_address_bits().is_some()
            {
                return Self::uint64_equal(
                    MachineTerm::integer_address(left.address().clone()),
                    MachineTerm::integer_address(right.address().clone()),
                );
            }
            Self::address_equal(left.address().clone(), right.address().clone())
        } else {
            // Whether two pointers are equal does not depend on the `const`
            // of the expressions that named them, and one proposition must
            // be one term however its operands were read.
            Self::PointerEqual(
                Box::new(left.with_pointee_constant(false)),
                Box::new(right.with_pointee_constant(false)),
            )
        }
    }

    pub fn address_equal(left: Address, right: Address) -> Self {
        if left.blocks_proven_distinct(&right) {
            Self::Constant(false)
        } else {
            // Keep the common base as evidence: a later equal pointer may use
            // another base spelling. The graph derives the offset comparison
            // without discarding the original address comparison.
            // Preserve symbolic reflexive comparisons as well: exact fact
            // checking must still see the comparison after a stored pointer
            // resolves to the same symbolic value on both sides.
            // A loaded pointer's block names an unknown address, so equal
            // displacements in it are a symbolic reflexive comparison too.
            if left.base == right.base
                && let Self::Constant(value) =
                    Self::address_offset_equal(left.offset.clone(), right.offset.clone())
                && !(value && matches!(left.base, AddressBase::LoadedPointer(_)))
            {
                return Self::Constant(value);
            }
            Self::AddressEqual(Box::new(left), Box::new(right))
        }
    }
}

/// Whether two offsets can never be equal because they differ by a constant
/// that no combination of their scaled indexes makes up: every scaled leaf
/// is a multiple of the strides' greatest common divisor, so offsets whose
/// constants differ modulo it are distinct. `items[x].y` at `x * 8 + 4` is
/// never the cell at `0` or `8`.
/// The value of a constant word read at `format`, or `None` for any other
/// term. Only constant nodes are read, so a symbolic operand costs one match.
fn machine_constant_value(
    format: MachineIntegerType,
    term: &MachineTerm,
) -> Option<num_bigint::BigInt> {
    if !matches!(term, MachineTerm::Constant { .. }) {
        return None;
    }
    match IntegerTerm::from_machine(format, term.clone())? {
        IntegerTerm::Constant(value) => Some(value),
        _ => None,
    }
}

fn pointer_offsets_differ_by_residue(left: &AddressOffset, right: &AddressOffset) -> bool {
    let (Some((left_scaled, left_constant)), Some((right_scaled, right_constant))) = (
        left.int32_scaled_linear_form(),
        right.int32_scaled_linear_form(),
    ) else {
        return false;
    };
    let divisor = left_scaled
        .iter()
        .chain(&right_scaled)
        .fold(0u64, |divisor, (_, stride)| {
            gcd(divisor, stride.unsigned_abs())
        });
    divisor > 1 && (left_constant - right_constant).unsigned_abs() % divisor != 0
}

fn gcd(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        (left, right) = (right, left % right);
    }
    left
}

fn classify_float_bits(
    bits: u64,
    exponent_bits: u32,
    fraction_bits: u32,
    classification: FloatClassification,
) -> bool {
    let exponent_mask = (1u64 << exponent_bits) - 1;
    let exponent = (bits >> fraction_bits) & exponent_mask;
    let fraction = bits & ((1u64 << fraction_bits) - 1);
    let all_ones = exponent == exponent_mask;
    let zero_exponent = exponent == 0;
    match classification {
        FloatClassification::Finite => !all_ones,
        FloatClassification::Infinite => all_ones && fraction == 0,
        FloatClassification::Zero => zero_exponent && fraction == 0,
        FloatClassification::Subnormal => zero_exponent && fraction != 0,
        FloatClassification::Nan => all_ones && fraction != 0,
    }
}

fn compare_float_bits(
    left: u64,
    right: u64,
    exponent_bits: u32,
    fraction_bits: u32,
    operator: ComparisonOperator,
) -> bool {
    let nan = FloatClassification::Nan;
    let left_nan = classify_float_bits(left, exponent_bits, fraction_bits, nan);
    let right_nan = classify_float_bits(right, exponent_bits, fraction_bits, nan);
    if left_nan || right_nan {
        return matches!(operator, ComparisonOperator::NotEqual);
    }

    let left_zero = classify_float_bits(
        left,
        exponent_bits,
        fraction_bits,
        FloatClassification::Zero,
    );
    let right_zero = classify_float_bits(
        right,
        exponent_bits,
        fraction_bits,
        FloatClassification::Zero,
    );
    let equal = (left_zero && right_zero) || left == right;
    if equal {
        return matches!(
            operator,
            ComparisonOperator::Equal
                | ComparisonOperator::LessEqual
                | ComparisonOperator::GreaterEqual
        );
    }

    // Order the two payloads by the usual monotone key: complement a negative
    // encoding, set the sign bit of a non-negative one. The complement has to
    // stay inside the format's own width, since these payloads sit in a `u64`
    // that is wider than every format except binary64. Complementing all 64
    // bits of a binary32 payload would raise every negative value above every
    // non-negative one, making `-1.0f < 1.0f` false.
    let width = exponent_bits + fraction_bits + 1;
    let payload_mask = if width >= u64::BITS {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let sign_bit = 1u64 << (exponent_bits + fraction_bits);
    let ordering_key = |bits: u64| {
        if bits & sign_bit != 0 {
            !bits & payload_mask
        } else {
            bits ^ sign_bit
        }
    };
    let left_key = ordering_key(left);
    let right_key = ordering_key(right);
    match operator {
        ComparisonOperator::Equal => false,
        ComparisonOperator::NotEqual => true,
        ComparisonOperator::LessThan => left_key < right_key,
        ComparisonOperator::LessEqual => left_key <= right_key,
        ComparisonOperator::GreaterThan => left_key > right_key,
        ComparisonOperator::GreaterEqual => left_key >= right_key,
    }
}

impl ProgramType {
    #[cfg(test)]
    pub(crate) fn function_pointer_signature(
        return_type: Self,
        parameter_types: &[Self],
    ) -> CallbackSignature {
        Self::qualified_function_pointer_signature(
            return_type,
            false,
            &parameter_types
                .iter()
                .map(|&ty| (ty, false))
                .collect::<Vec<_>>(),
        )
    }

    pub(crate) fn qualified_function_pointer_signature(
        return_type: Self,
        return_constant: bool,
        parameters: &[(Self, bool)],
    ) -> CallbackSignature {
        Self::qualified_function_pointer_signature_with_exceptional_outcome(
            return_type,
            return_constant,
            parameters,
            ExceptionalSignature::None,
        )
    }

    pub(crate) fn qualified_function_pointer_signature_with_exceptional_outcome(
        return_type: Self,
        return_constant: bool,
        parameters: &[(Self, bool)],
        exceptional_signature: ExceptionalSignature,
    ) -> CallbackSignature {
        // Exact base-46 digits: twenty-three modeled types, each with a pointee-const
        // bit. The leading one distinguishes arities. Fourteen digits plus
        // the sentinel use fewer than 79 bits, preserving the 13-parameter
        // capacity without truncation or probabilistic identities.
        fn code(program_type: ProgramType, constant: bool) -> Option<u128> {
            if constant && !program_type.is_object_pointer() {
                return None;
            }
            Some(
                match program_type {
                    // A function pointer over an abstract type is not encoded.
                    ProgramType::Parameter(_) | ProgramType::ParameterPointer(_) => return None,
                    ProgramType::Void => 0,
                    ProgramType::Bool => 19,
                    ProgramType::VoidPointer => 20,
                    ProgramType::Int32 => 1,
                    ProgramType::UInt8 => 2,
                    ProgramType::UInt32 => 3,
                    ProgramType::Int32Pointer => 4,
                    ProgramType::UInt8Pointer => 5,
                    ProgramType::Int32PointerPointer => 6,
                    ProgramType::UInt8PointerPointer => 7,
                    ProgramType::Int8 => 21,
                    ProgramType::Int16 => 8,
                    ProgramType::UInt16 => 9,
                    ProgramType::Int64 => 10,
                    ProgramType::UInt64 => 11,
                    ProgramType::Int8Pointer => 22,
                    ProgramType::Int16Pointer => 12,
                    ProgramType::UInt16Pointer => 13,
                    ProgramType::UInt32Pointer => 14,
                    ProgramType::Int64Pointer => 15,
                    ProgramType::UInt64Pointer => 16,
                    ProgramType::Float32 => 17,
                    ProgramType::Float64 => 18,
                    ProgramType::Int128
                    | ProgramType::UInt128
                    | ProgramType::Int128Pointer
                    | ProgramType::UInt128Pointer
                    | ProgramType::Int8PointerPointer
                    | ProgramType::Int8Array(_) => {
                        return None;
                    }
                    ProgramType::Int16PointerPointer
                    | ProgramType::UInt16PointerPointer
                    | ProgramType::UInt32PointerPointer
                    | ProgramType::Int128PointerPointer
                    | ProgramType::Int64PointerPointer
                    | ProgramType::UInt128PointerPointer
                    | ProgramType::UInt64PointerPointer
                    | ProgramType::FunctionPointer(_)
                    | ProgramType::Int32Array(_)
                    | ProgramType::UInt8Array(_)
                    | ProgramType::Int16Array(_)
                    | ProgramType::UInt16Array(_)
                    | ProgramType::UInt32Array(_)
                    | ProgramType::Int128Array(_)
                    | ProgramType::Int64Array(_)
                    | ProgramType::UInt128Array(_)
                    | ProgramType::UInt64Array(_)
                    | ProgramType::Float32Pointer
                    | ProgramType::Float64Pointer
                    | ProgramType::Float32PointerPointer
                    | ProgramType::Float64PointerPointer
                    | ProgramType::Float32Array(_)
                    | ProgramType::Float64Array(_)
                    | ProgramType::PointerArray(_, _)
                    | ProgramType::VoidPointerPointer => {
                        return None;
                    }
                } + if constant { 23 } else { 0 },
            )
        }

        if parameters.len() > 13 {
            return CallbackSignature::UNSPECIFIED;
        }
        let Some(return_code) = code(return_type, return_constant) else {
            return CallbackSignature::UNSPECIFIED;
        };
        let mut signature = 46 + return_code;
        for &(parameter_type, constant) in parameters {
            let Some(parameter_code) = code(parameter_type, constant) else {
                return CallbackSignature::UNSPECIFIED;
            };
            signature = signature * 46 + parameter_code;
        }
        // Ordinary callback signatures occupy fewer than 79 bits. Reserve a
        // high bit for the closed int32 exceptional channel so non-throwing
        // encodings cannot collide with it.
        let signature = match exceptional_signature {
            ExceptionalSignature::None => signature,
            ExceptionalSignature::Int32 => signature | (1u128 << 79),
            ExceptionalSignature::Opaque(_) => return CallbackSignature::UNSPECIFIED,
        };
        CallbackSignature::from_encoded(signature)
    }

    pub fn is_pointer(self) -> bool {
        self.pointee_type().is_some()
            || matches!(self, Self::VoidPointer | Self::FunctionPointer(_))
    }

    pub(crate) fn is_object_pointer(self) -> bool {
        self.is_pointer() && !matches!(self, Self::FunctionPointer(_))
    }

    pub(crate) fn pointer_types_compatible(self, other: Self) -> bool {
        self == other
            || (self.is_object_pointer()
                && other.is_object_pointer()
                && (self == Self::VoidPointer || other == Self::VoidPointer))
    }

    pub(crate) fn pointer_to(self) -> Option<Self> {
        match self {
            Self::Parameter(parameter) => Some(Self::ParameterPointer(parameter)),
            Self::ParameterPointer(_) => None,
            Self::Bool => None,
            Self::Int8 => Some(Self::Int8Pointer),
            Self::Int16 => Some(Self::Int16Pointer),
            Self::Int32 => Some(Self::Int32Pointer),
            Self::UInt8 => Some(Self::UInt8Pointer),
            Self::UInt16 => Some(Self::UInt16Pointer),
            Self::UInt32 => Some(Self::UInt32Pointer),
            Self::Int64 => Some(Self::Int64Pointer),
            Self::Int128 => Some(Self::Int128Pointer),
            Self::UInt64 => Some(Self::UInt64Pointer),
            Self::UInt128 => Some(Self::UInt128Pointer),
            Self::Float32 => Some(Self::Float32Pointer),
            Self::Float64 => Some(Self::Float64Pointer),
            Self::Int8Pointer => Some(Self::Int8PointerPointer),
            Self::Int16Pointer => Some(Self::Int16PointerPointer),
            Self::UInt16Pointer => Some(Self::UInt16PointerPointer),
            Self::Int32Pointer => Some(Self::Int32PointerPointer),
            Self::UInt8Pointer => Some(Self::UInt8PointerPointer),
            Self::UInt32Pointer => Some(Self::UInt32PointerPointer),
            Self::Int64Pointer => Some(Self::Int64PointerPointer),
            Self::Int128Pointer => Some(Self::Int128PointerPointer),
            Self::UInt64Pointer => Some(Self::UInt64PointerPointer),
            Self::UInt128Pointer => Some(Self::UInt128PointerPointer),
            Self::Float32Pointer => Some(Self::Float32PointerPointer),
            Self::Float64Pointer => Some(Self::Float64PointerPointer),
            Self::VoidPointer => Some(Self::VoidPointerPointer),
            Self::Int8PointerPointer | Self::Int8Array(_) => None,
            Self::Void
            | Self::VoidPointerPointer
            | Self::Int16PointerPointer
            | Self::UInt16PointerPointer
            | Self::Int32PointerPointer
            | Self::UInt8PointerPointer
            | Self::UInt32PointerPointer
            | Self::Int128PointerPointer
            | Self::Int64PointerPointer
            | Self::UInt128PointerPointer
            | Self::UInt64PointerPointer
            | Self::FunctionPointer(_)
            | Self::Int32Array(_)
            | Self::UInt8Array(_)
            | Self::Int16Array(_)
            | Self::UInt16Array(_)
            | Self::UInt32Array(_)
            | Self::Int128Array(_)
            | Self::Int64Array(_)
            | Self::UInt128Array(_)
            | Self::UInt64Array(_)
            | Self::Float32PointerPointer
            | Self::Float64PointerPointer
            | Self::Float32Array(_)
            | Self::Float64Array(_) => None,
            Self::PointerArray(_, _) => None,
        }
    }

    /// `unsigned char *` or `signed char *` (plain `char *` is one of them).
    pub(crate) fn is_character_pointer(self) -> bool {
        matches!(self, Self::UInt8Pointer | Self::Int8Pointer)
    }

    /// Whether `self` and `other` are pointers to the two signednesses of
    /// one integer width, or the same pointer type: GCC and Clang convert
    /// between them with at most a `-Wpointer-sign` warning, and C11 6.5p7
    /// lets the signed or unsigned type corresponding to an object's type
    /// read it. A load through either reads the cell's bits in its own
    /// signedness ([`Self::read_cell`]).
    pub(crate) fn is_signedness_view_of(self, other: Self) -> bool {
        let width_class = |ty| match ty {
            Self::Int8Pointer | Self::UInt8Pointer => Some(1),
            Self::Int16Pointer | Self::UInt16Pointer => Some(2),
            Self::Int32Pointer | Self::UInt32Pointer => Some(4),
            Self::Int64Pointer | Self::UInt64Pointer => Some(8),
            _ => None,
        };
        self == other || width_class(self).is_some_and(|width| width_class(other) == Some(width))
    }

    /// The value a load of this type reads from a cell holding `stored`, or
    /// `None` when the cell holds nothing this load can read.
    ///
    /// A load reads a cell of its own kind as stored ([`Self::accepts`]).
    /// The one other read is through the integer type of the other
    /// signedness and the same width (C11 6.5p7), which GCC and Clang allow
    /// through a pointer conversion with at most a `-Wpointer-sign`
    /// warning: the load reads the cell's bits in its own signedness. A
    /// 32-bit read is the sign cast σ of the stored word (rule K5), as the
    /// kernel's own C conversion between `int` and `unsigned int` is; a
    /// 64-bit term uses the bit-preserving conversions between its two typed
    /// carriers. Narrower terms are their extended values, so
    /// the read is the modular conversion between the two types, as for
    /// bytes below.
    ///
    /// For bytes, a one-byte character load reads a one-byte integer cell
    /// of the other signedness as the same eight bits. An `unsigned char` load of a `signed char`
    /// cell holding `t` reads `t mod 256`; a `signed char` load of an
    /// `unsigned char` cell holding `u` reads the two's-complement value of
    /// `u`'s eight bits. Both are the modular conversion between the two
    /// byte types, so a constant is folded and a symbolic value keeps an
    /// explicit conversion term; nothing about the cell is guessed.
    pub(crate) fn read_cell(self, stored: &ProgramValue) -> Option<ProgramValue> {
        if self.accepts(stored) {
            return Some(stored.clone());
        }
        let reinterpret = |source, destination, term: &MachineTerm| {
            MachineTerm::machine_integer_cast(source, destination, term.clone())
        };
        match (self, stored) {
            (Self::UInt8, ProgramValue::Int8(term)) => Some(ProgramValue::UInt8(reinterpret(
                MachineIntegerType::Int8,
                MachineIntegerType::UInt8,
                term,
            ))),
            (Self::Int8, ProgramValue::UInt8(term)) => Some(ProgramValue::Int8(reinterpret(
                MachineIntegerType::UInt8,
                MachineIntegerType::Int8,
                term,
            ))),
            (Self::UInt16, ProgramValue::Int16(term)) => Some(ProgramValue::UInt16(reinterpret(
                MachineIntegerType::Int16,
                MachineIntegerType::UInt16,
                term,
            ))),
            (Self::Int16, ProgramValue::UInt16(term)) => Some(ProgramValue::Int16(reinterpret(
                MachineIntegerType::UInt16,
                MachineIntegerType::Int16,
                term,
            ))),
            // Rule K5: the four bytes read in the other signedness are the
            // stored word under the sign cast σ.
            (Self::UInt32, ProgramValue::Int32(term)) => {
                Some(ProgramValue::UInt32(MachineTerm::sign_cast32(
                    MachineIntegerType::Int32,
                    MachineIntegerType::UInt32,
                    term.clone(),
                )))
            }
            (Self::Int32, ProgramValue::UInt32(term)) => {
                Some(ProgramValue::Int32(MachineTerm::sign_cast32(
                    MachineIntegerType::UInt32,
                    MachineIntegerType::Int32,
                    term.clone(),
                )))
            }
            (Self::UInt64, ProgramValue::Int64(term)) => Some(ProgramValue::UInt64(
                MachineTerm::uint64_from_int64(term.clone()),
            )),
            (Self::Int64, ProgramValue::UInt64(term)) => Some(ProgramValue::Int64(
                MachineTerm::int64_from_uint64_bits(term.clone()),
            )),
            _ => None,
        }
    }

    pub(crate) fn accepts(self, value: &ProgramValue) -> bool {
        match (self, value.numeric_value()) {
            (Self::Int128, ProgramValue::Int128(term)) => {
                MachineIntegerType::Int128.accepts_wide_term(term)
            }
            (Self::UInt128, ProgramValue::UInt128(term)) => {
                MachineIntegerType::UInt128.accepts_wide_term(term)
            }
            (Self::Int8, ProgramValue::Int8(_)) => true,
            (Self::Parameter(name), ProgramValue::Parameter(term)) => {
                term.algebraic_type == name.algebraic_type()
            }
            (Self::Void, ProgramValue::Void)
            | (Self::Bool, ProgramValue::Bool(_))
            | (Self::Int16, ProgramValue::Int16(_))
            | (Self::Int32, ProgramValue::Int32(_))
            | (Self::UInt8, ProgramValue::UInt8(_))
            | (Self::UInt16, ProgramValue::UInt16(_))
            | (Self::Int64, ProgramValue::Int64(_))
            | (Self::UInt64, ProgramValue::UInt64(_))
            | (Self::Float32, ProgramValue::Float32(_))
            | (Self::Float64, ProgramValue::Float64(_))
            | (Self::UInt32, ProgramValue::UInt32(_)) => true,
            (target, ProgramValue::Pointer(pointer)) if target.is_pointer() => {
                pointer.is_null()
                    || (pointer.program_type().pointer_types_compatible(target)
                        && if target.is_function_pointer() {
                            pointer.base.is_function()
                                || pointer.address().as_loaded_value().is_some()
                        } else {
                            !pointer.base.is_function()
                        })
            }
            _ => false,
        }
    }

    /// The LP64 alignment of an object of this type: scalar and pointer
    /// widths, or the element width of an array.
    pub(crate) fn abi_alignment(self) -> u32 {
        match self {
            Self::Int32Array(_) | Self::UInt32Array(_) | Self::Float32Array(_) => 4,
            Self::UInt8Array(_) => 1,
            Self::Int8Array(_) => 1,
            Self::Int16Array(_) | Self::UInt16Array(_) => 2,
            Self::Int64Array(_) | Self::UInt64Array(_) | Self::Float64Array(_) => 8,
            Self::PointerArray(_, _) => 8,
            Self::Int128 | Self::UInt128 | Self::Int128Array(_) | Self::UInt128Array(_) => 16,
            scalar => scalar.byte_width().min(C_POINTER_BYTE_WIDTH),
        }
    }

    pub fn byte_width(self) -> u32 {
        match self {
            // An abstract value stored in memory, as a generic struct's
            // field, takes a word: no program reads its bytes, so its
            // width is the model's choice. A local holds one in its binding.
            Self::Parameter(_) => ABSTRACT_VALUE_WIDTH,
            Self::ParameterPointer(_) => C_POINTER_BYTE_WIDTH,
            Self::Void => 0,
            Self::Bool => 1,
            Self::VoidPointer => C_POINTER_BYTE_WIDTH,
            Self::VoidPointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int8 => 1,
            Self::Int16 => 2,
            Self::Int32 => 4,
            Self::UInt8 => 1,
            Self::UInt16 => 2,
            Self::UInt32 => 4,
            Self::Int64 => 8,
            Self::UInt64 => 8,
            Self::Int128 | Self::UInt128 => 16,
            Self::Float32 => 4,
            Self::Float64 => 8,
            Self::Int8Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int16Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int32Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt16Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt32Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int64Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int128Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt64Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt128Pointer => C_POINTER_BYTE_WIDTH,
            Self::Float32Pointer => C_POINTER_BYTE_WIDTH,
            Self::Float64Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int8PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int16PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int32PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt16PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt32PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int64PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int128PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt64PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt128PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Float32PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Float64PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::FunctionPointer(_) => C_POINTER_BYTE_WIDTH,
            Self::Int32Array(length) => length.saturating_mul(4),
            Self::UInt8Array(length) => length,
            Self::Int8Array(length) => length,
            Self::Int16Array(length) | Self::UInt16Array(length) => length.saturating_mul(2),
            Self::UInt32Array(length) => length.saturating_mul(4),
            Self::Int64Array(length) | Self::UInt64Array(length) => length.saturating_mul(8),
            Self::Float32Array(length) => length.saturating_mul(4),
            Self::Float64Array(length) => length.saturating_mul(8),
            Self::Int128Array(length) | Self::UInt128Array(length) => length.saturating_mul(16),
            Self::PointerArray(_, length) => length.saturating_mul(C_POINTER_BYTE_WIDTH),
        }
    }

    pub(crate) fn supports_scalar_array_write(self, copy: bool) -> bool {
        matches!(self, Self::Int32 | Self::UInt8 | Self::UInt32)
            || (!copy
                && (MachineIntegerType::from_program_type(self).is_some()
                    || matches!(self, Self::Float32 | Self::Float64)))
    }

    pub(crate) fn array_element_type(self) -> Option<Self> {
        Some(match self {
            Self::Int8Array(_) => Self::Int8,
            Self::UInt8Array(_) => Self::UInt8,
            Self::Int16Array(_) => Self::Int16,
            Self::UInt16Array(_) => Self::UInt16,
            Self::Int32Array(_) => Self::Int32,
            Self::UInt32Array(_) => Self::UInt32,
            Self::Int64Array(_) => Self::Int64,
            Self::UInt64Array(_) => Self::UInt64,
            Self::Int128Array(_) => Self::Int128,
            Self::UInt128Array(_) => Self::UInt128,
            Self::Float32Array(_) => Self::Float32,
            Self::Float64Array(_) => Self::Float64,
            Self::PointerArray(element, _) => element.pointer_type(),
            _ => return None,
        })
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::VoidPointerPointer => Some(Self::VoidPointer),
            Self::ParameterPointer(parameter) => Some(Self::Parameter(parameter)),
            Self::Int8Pointer => Some(Self::Int8),
            Self::Int16Pointer => Some(Self::Int16),
            Self::Int32Pointer => Some(Self::Int32),
            Self::UInt8Pointer => Some(Self::UInt8),
            Self::UInt16Pointer => Some(Self::UInt16),
            Self::UInt32Pointer => Some(Self::UInt32),
            Self::Int64Pointer => Some(Self::Int64),
            Self::Int128Pointer => Some(Self::Int128),
            Self::UInt64Pointer => Some(Self::UInt64),
            Self::UInt128Pointer => Some(Self::UInt128),
            Self::Int8PointerPointer => Some(Self::Int8Pointer),
            Self::Int16PointerPointer => Some(Self::Int16Pointer),
            Self::Int32PointerPointer => Some(Self::Int32Pointer),
            Self::UInt8PointerPointer => Some(Self::UInt8Pointer),
            Self::UInt16PointerPointer => Some(Self::UInt16Pointer),
            Self::UInt32PointerPointer => Some(Self::UInt32Pointer),
            Self::Int64PointerPointer => Some(Self::Int64Pointer),
            Self::Int128PointerPointer => Some(Self::Int128Pointer),
            Self::UInt64PointerPointer => Some(Self::UInt64Pointer),
            Self::UInt128PointerPointer => Some(Self::UInt128Pointer),
            Self::Float32Pointer => Some(Self::Float32),
            Self::Float64Pointer => Some(Self::Float64),
            Self::Float32PointerPointer => Some(Self::Float32Pointer),
            Self::Float64PointerPointer => Some(Self::Float64Pointer),
            Self::PointerArray(element, _) => Some(element.pointer_type()),
            _ => None,
        }
    }

    fn is_function_pointer(self) -> bool {
        matches!(self, Self::FunctionPointer(_))
    }
}

/// The variable a scalar C value is, when it is exactly one: a symbolic
/// binder's or a call result's value, not an expression over one.
pub(crate) fn single_variable_of_program_value(value: &ProgramValue) -> Option<Variable> {
    match value.numeric_value() {
        ProgramValue::Bool(MachineTerm::Variable(variable))
        | ProgramValue::Int8(MachineTerm::Variable(variable))
        | ProgramValue::Int16(MachineTerm::Variable(variable))
        | ProgramValue::Int32(MachineTerm::Variable(variable))
        | ProgramValue::UInt8(MachineTerm::Variable(variable))
        | ProgramValue::UInt16(MachineTerm::Variable(variable))
        | ProgramValue::UInt32(MachineTerm::Variable(variable))
        | ProgramValue::Int64(MachineTerm::Variable(variable))
        | ProgramValue::UInt64(MachineTerm::Variable(variable)) => Some(*variable),
        _ => None,
    }
}

impl ProgramValue {
    /// An unconstrained complete C word has identity but no pointer authority.
    pub(crate) fn complete_word(self, identity: Address) -> Self {
        if !matches!(self, Self::Int64(_) | Self::UInt64(_)) {
            return self;
        }
        Self::PointerInteger(PointerIntegerValue {
            numeric: Box::new(self),
            pointer: Box::new(Pointer::new(identity, ProgramType::VoidPointer)),
            kind: PointerIntegerKind::Word { changed_bits: 0 },
        })
    }

    /// Canonicalize the C object-pointer conversions a resource's declared
    /// parameter type admits, preserving the pointer's provenance and bounds.
    pub(crate) fn resource_argument_at_type(self, expected: ProgramType) -> Self {
        match self {
            Self::Pointer(pointer) if pointer.program_type().pointer_types_compatible(expected) => {
                Self::Pointer(pointer.with_type(expected))
            }
            value => value,
        }
    }

    /// Mathematical observation, deliberately without a representation record.
    pub(crate) fn numeric_value(&self) -> &Self {
        match self {
            Self::PointerInteger(record) => record.numeric.numeric_value(),
            _ => self,
        }
    }

    pub(crate) fn pointer(pointer: Address) -> Self {
        Self::typed_pointer(pointer, ProgramType::Int32Pointer)
    }

    pub(crate) fn typed_pointer(pointer: Address, program_type: ProgramType) -> Self {
        Self::Pointer(Pointer::new(pointer, program_type))
    }

    pub(crate) fn typed_pointer_with_pointee_constant(
        pointer: Address,
        program_type: ProgramType,
        pointee_constant: bool,
    ) -> Self {
        Self::Pointer(Pointer::new(pointer, program_type).with_pointee_constant(pointee_constant))
    }

    pub(crate) fn retag_pointer(self, program_type: ProgramType) -> Self {
        match self {
            Self::Pointer(pointer) => Self::Pointer(pointer.with_type(program_type)),
            value => value,
        }
    }

    pub(crate) fn with_pointer_pointee_volatile(self, pointee_volatile: bool) -> Self {
        match self {
            Self::Pointer(pointer) => {
                Self::Pointer(pointer.with_pointee_volatile(pointee_volatile))
            }
            value => value,
        }
    }

    /// Records the class of the object a pointer value designates; see
    /// [`Pointer::with_object_class`].
    pub(crate) fn with_pointer_object_class(
        self,
        object_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        match self {
            Self::Pointer(pointer) => Self::Pointer(pointer.with_object_class(object_class)),
            value => value,
        }
    }

    pub(crate) fn with_pointer_object_type_evidence(
        self,
        evidence: Option<ObjectTypeEvidence>,
    ) -> Self {
        match self {
            Self::Pointer(pointer) => Self::Pointer(pointer.with_object_type_evidence(evidence)),
            value => value,
        }
    }

    pub(crate) fn with_contract_pointer_object_class(
        self,
        declared: Option<crate::kernel::effective_type::CAccessClass>,
        required: Option<crate::kernel::effective_type::CAccessClass>,
        parameter: usize,
        scope: u64,
    ) -> Self {
        let checked = required.is_some();
        match required.or(declared) {
            Some(class) if super::super::object_types::nominal_class(&class) => self
                .with_pointer_object_type_evidence(Some(ObjectTypeEvidence::parameter(
                    class, parameter, scope, checked,
                ))),
            class => self.with_pointer_declared_object_class(class),
        }
    }

    pub(crate) fn with_pointer_declared_object_class(
        self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        match self {
            Self::Pointer(pointer) => Self::Pointer(pointer.with_declared_object_class(class)),
            value => value,
        }
    }

    pub(crate) fn with_pointer_pointee_constant(self, pointee_constant: bool) -> Self {
        match self {
            Self::Pointer(pointer) => {
                Self::Pointer(pointer.with_pointee_constant(pointee_constant))
            }
            value => value,
        }
    }

    pub(crate) fn program_type(&self) -> ProgramType {
        match self {
            Self::PointerInteger(record) => record.numeric.program_type(),
            Self::Parameter(term) => {
                ProgramType::Parameter(TypeParameterName::of(&term.algebraic_type))
            }
            Self::Void => ProgramType::Void,
            Self::Bool(_) => ProgramType::Bool,
            Self::Int8(_) => ProgramType::Int8,
            Self::Int16(_) => ProgramType::Int16,
            Self::Int32(_) => ProgramType::Int32,
            Self::UInt8(_) => ProgramType::UInt8,
            Self::UInt16(_) => ProgramType::UInt16,
            Self::UInt32(_) => ProgramType::UInt32,
            Self::Int64(_) => ProgramType::Int64,
            Self::UInt64(_) => ProgramType::UInt64,
            Self::Int128(_) => ProgramType::Int128,
            Self::UInt128(_) => ProgramType::UInt128,
            Self::Float32(_) => ProgramType::Float32,
            Self::Float64(_) => ProgramType::Float64,
            Self::Pointer(pointer) => pointer.program_type(),
        }
    }

    pub(in crate::kernel) fn byte_width(&self) -> u32 {
        match self {
            Self::PointerInteger(_) => 8,
            Self::Parameter(_) => ABSTRACT_VALUE_WIDTH,
            Self::Void => 0,
            Self::Bool(_) => 1,
            Self::Int8(_) => 1,
            Self::Int16(_) => 2,
            Self::Int32(_) => 4,
            Self::UInt8(_) => 1,
            Self::UInt16(_) => 2,
            Self::UInt32(_) => 4,
            Self::Int64(_) => 8,
            Self::UInt64(_) => 8,
            Self::Int128(_) | Self::UInt128(_) => 16,
            Self::Float32(_) => 4,
            Self::Float64(_) => 8,
            Self::Pointer(_) => C_POINTER_BYTE_WIDTH,
        }
    }
}

impl LValue {
    pub(in crate::kernel) fn local(name: impl Into<BindingName>, value_type: ProgramType) -> Self {
        Self::local_with_qualifiers(name, value_type, false, false)
    }

    pub(in crate::kernel) fn local_with_qualifiers(
        name: impl Into<BindingName>,
        value_type: ProgramType,
        volatile: bool,
        pointee_volatile: bool,
    ) -> Self {
        Self {
            storage: LValueStorage::Local { name: name.into() },
            value_type,
            volatile,
            pointee_volatile,
            constant: false,
            pointee_constant: false,
            bounds: None,
            provenance: None,
            bounds_known: false,
            bounds_owner: None,
            access_class: None,
            object_class: None,
        }
    }

    pub(in crate::kernel) fn memory_with_volatile(
        pointer: Address,
        value_type: ProgramType,
        volatile: bool,
    ) -> Self {
        Self::memory_with_qualifiers(pointer, value_type, volatile, false)
    }

    pub(in crate::kernel) fn memory_with_qualifiers(
        pointer: Address,
        value_type: ProgramType,
        volatile: bool,
        pointee_volatile: bool,
    ) -> Self {
        Self {
            storage: LValueStorage::Memory { pointer },
            value_type,
            volatile,
            pointee_volatile,
            constant: false,
            pointee_constant: false,
            bounds: None,
            provenance: None,
            bounds_known: false,
            bounds_owner: None,
            access_class: None,
            object_class: None,
        }
    }

    pub(in crate::kernel) fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(in crate::kernel) fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    /// The lvalue reached through `pointer`, which keeps its bounds and the
    /// class of the object it designates.
    pub(in crate::kernel) fn with_bounds_of(mut self, pointer: &Pointer) -> Self {
        self.bounds = pointer.bounds().cloned().map(std::sync::Arc::new);
        self.provenance = Some(std::sync::Arc::new(pointer.provenance().clone()));
        self.bounds_known = pointer.bounds_are_known();
        self.bounds_owner = pointer.bounds_owner.clone();
        self.object_class = pointer.object_class();
        self
    }

    pub(in crate::kernel) fn access_provenance(&self) -> Option<(&Address, Option<&Address>)> {
        self.provenance.as_deref().map(|root| {
            (
                root,
                if self.bounds_known {
                    None
                } else {
                    self.bounds_owner.as_deref()
                },
            )
        })
    }

    /// The class of the lvalue's type, which an access through it uses.
    pub(in crate::kernel) fn with_access_class(
        mut self,
        access_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.access_class = access_class;
        self
    }

    pub(in crate::kernel) fn access_class(
        &self,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.access_class.clone()
    }

    pub(in crate::kernel) fn object_class(
        &self,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.object_class.clone()
    }

    pub(in crate::kernel) fn bounds(&self) -> Option<&SubobjectBounds> {
        self.bounds.as_deref()
    }

    pub fn value_type(&self) -> ProgramType {
        self.value_type
    }

    pub(in crate::kernel) fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub(in crate::kernel) fn pointee_is_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub(in crate::kernel) fn is_constant(&self) -> bool {
        self.constant
    }

    pub(in crate::kernel) fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub(in crate::kernel) fn pointer(&self, state: &ExecutionState) -> Option<Address> {
        match &self.storage {
            LValueStorage::Local { name } => {
                let pointer = state.locals.slot(name)?.clone();
                state.memory.has_block(&pointer.base).then_some(pointer)
            }
            LValueStorage::Memory { pointer } => Some(pointer.clone()),
        }
    }
}

impl SharedPureApplication {
    pub(in crate::kernel) fn integer_address_bits(&self) -> Option<&MachineTerm> {
        if self.name() == "$integer-address"
            && let [PureFunctionArgument::Value(ProgramValue::UInt64(bits))] = self.arguments()
        {
            Some(bits)
        } else {
            None
        }
    }
}

impl Address {
    pub(in crate::kernel) fn integer_address_bits(&self) -> Option<&MachineTerm> {
        if self.offset == AddressOffset::Constant(0)
            && let AddressBase::PureFunctionApplication(application) = &self.base
        {
            application.integer_address_bits()
        } else {
            None
        }
    }

    /// The raw base address from which this pointer's object provenance came.
    ///
    /// External parameters share one memory block, so their leading offset is
    /// the only raw base address that survives parameter abstraction. Pointer
    /// arithmetic appends displacement terms; remove those displacements when
    /// deciding whether the originating object base may be null.
    pub(in crate::kernel) fn object_base(&self) -> Self {
        fn external_base(offset: &AddressOffset) -> &AddressOffset {
            match offset {
                AddressOffset::Add(base, _) => external_base(base),
                offset => offset,
            }
        }

        Self {
            base: self.base.clone(),
            offset: if self.base == AddressBase::ExternalArgument {
                external_base(&self.offset).clone()
            } else {
                AddressOffset::Constant(0)
            },
        }
    }

    /// The C object identity carried by this pointer.
    ///
    /// Concrete blocks already are object identities. External parameters
    /// share one address-space block so memory operations remain conservatively
    /// alias-aware; the variable in their leading offset also names a separate
    /// opaque object block. Keeping that block separate from the raw offset is
    /// essential: address equality does not prove that adjacent C objects have
    /// the same provenance. Pointer arithmetic appends displacement terms and
    /// therefore preserves the leading identity.
    pub(in crate::kernel) fn object_identity(&self) -> Self {
        if self.base == AddressBase::ExternalArgument {
            let base = self.object_base();
            let variable = match &base.offset {
                AddressOffset::Variable(variable) => Some(*variable),
                AddressOffset::Int32Scaled { value, .. }
                | AddressOffset::Int64Scaled { value, .. } => {
                    value.operand_view().variable().copied()
                }
                AddressOffset::Constant(_) | AddressOffset::Add(_, _) => None,
            };
            if let Some(variable) = variable {
                return Self {
                    base: AddressBase::ExternalObject(variable),
                    offset: AddressOffset::Constant(0),
                };
            }
            return Self {
                base: self.base.clone(),
                offset: base.offset,
            };
        }

        Self {
            base: self.base.clone(),
            offset: AddressOffset::Constant(0),
        }
    }

    pub(crate) fn null() -> Self {
        Self {
            base: "null".into(),
            offset: AddressOffset::Constant(0),
        }
    }

    /// Whether this pointer is in the null object's block, at any offset.
    ///
    /// Unlike a null test, this stays true for a pointer already displaced
    /// from null, so a second displacement is judged the same way as the
    /// first.
    pub(in crate::kernel) fn is_in_null_block(&self) -> bool {
        self.base == AddressBase::Concrete("null".to_string())
    }

    /// Numeric LP64 reconstruction. This application is only an address;
    /// a complete C word carries its independent provenance beside it.
    pub(in crate::kernel) fn from_integer_address(bits: MachineTerm) -> Self {
        if bits.uint64_as_const() == Some(0) {
            return Self::null();
        }
        Self {
            base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                "$integer-address".into(),
                vec![PureFunctionArgument::Value(ProgramValue::UInt64(bits))],
            )),
            offset: AddressOffset::Constant(0),
        }
    }

    pub(crate) fn symbolic(variable: Variable) -> Self {
        Self {
            base: AddressBase::Symbolic(variable),
            offset: AddressOffset::Constant(0),
        }
    }

    /// The base of storage the verifier introduced for an object the C
    /// abstract machine creates but the program never names. The identity must
    /// come from the single kernel variable allocator, so that it is fresh.
    /// See [`AddressBase::Temporary`].
    pub(crate) fn verifier_temporary(identity: Variable) -> Self {
        Self {
            base: AddressBase::Temporary(identity.0),
            offset: AddressOffset::Constant(0),
        }
    }

    /// Name an eight-byte pointer read as a typed graph application. The
    /// caller supplies the assumption-free defining state and address.
    /// Access observations are retained separately from this identity.
    pub(crate) fn loaded_value(memory: &SharedMemory, address: &Address) -> Self {
        Self {
            base: AddressBase::LoadedPointer(crate::kernel::eval::pointer_load_identity(
                memory, address,
            )),
            offset: AddressOffset::Constant(0),
        }
    }

    /// The read of the pointer cell at `address` in `memory`, identified by
    /// its version point: the term a Click read of that place lowers to.
    /// Two reads of an unchanged cell in different memories are this same
    /// term. Unlike [`Self::canonical_loaded_value`], a stored pointer does
    /// not replace the read.
    pub(crate) fn canonical_read(memory: &SharedMemory, address: &Address) -> Self {
        let read = MachineTerm::MemoryLoad(
            ProgramPoint::at(memory),
            Box::new(address.clone()),
            LoadKind::Int32,
        );
        named_pointer_read(
            canonical_pointer_read(&read).expect("a memory load has a canonical read"),
        )
    }

    /// The pointer read of `address` in `memory`, named at the canonical
    /// read of that cell, as a direct lowering of the same place names it.
    pub(crate) fn canonical_loaded_value(memory: &SharedMemory, address: &Address) -> Self {
        // A cell holding a complete stored pointer reads as that pointer.
        if let Some(ProgramValue::Pointer(stored)) = memory.memory().known_value(address) {
            return stored.address().clone();
        }
        let read = MachineTerm::MemoryLoad(
            ProgramPoint::at(memory),
            Box::new(address.clone()),
            LoadKind::Int32,
        );
        match canonical_pointer_read(&read) {
            Some(named) => named_pointer_read(named),
            None => Self::loaded_value(memory, address),
        }
    }

    /// Recover the load definition and any subsequent pointer displacement.
    /// The defining address is never reconstructed from this value's block or
    /// from its pointee width.
    pub(crate) fn as_loaded_value(&self) -> Option<LoadedPointerView> {
        let AddressBase::LoadedPointer(identity) = self.base else {
            return None;
        };
        let (defining_memory, defining_address) =
            crate::kernel::eval::registered_pointer_load(identity)?;
        Some(LoadedPointerView {
            identity,
            defining_memory,
            defining_address,
            displacement: self.offset.clone(),
        })
    }

    /// The pointer value a load of a pointer-typed cell denotes, where
    /// `bits` names what the cell holds: a raw `MemoryLoad` or the load
    /// variable minted for it. The value is the read's own name, whatever
    /// storage held it and whatever its pointee; `None` when `bits` is
    /// neither a load nor a registered load variable.
    pub(crate) fn loaded(bits: &MachineTerm) -> Option<Self> {
        if let Some(named) = canonical_pointer_read(bits) {
            return Some(named_pointer_read(named));
        }
        let MachineTerm::MemoryLoad(memory, address, _) = bits else {
            return None;
        };
        Some(Self::loaded_value(
            &memory.shared_memory().unchanged_bytes_source(),
            address,
        ))
    }

    /// The pointer a logical read of `address` in `memory` reads, named by
    /// the cell's version as every logical read is
    /// (`docs/internals/raise-lower-principle.md`): never by a pointer the cell
    /// holds, which the read-over-write authority relates to the read
    /// (`eval::pointer_read_over_write_value`). A cell holding its own read
    /// is that read.
    pub(crate) fn version_read(memory: &SharedMemory, address: &Address) -> Self {
        match Self::version_read_value(memory, address) {
            Ok(held) => held.address().clone(),
            Err(read) => read,
        }
    }

    /// A logical read with the whole pointer value when the read is a
    /// value the memory already holds for the cell (its own materialized
    /// read, or static storage's symbolic initial contents), provenance and
    /// bounds included; otherwise the named read, as `Err`.
    pub(crate) fn version_read_value(
        memory: &SharedMemory,
        address: &Address,
    ) -> Result<Pointer, Self> {
        let source = memory.unchanged_bytes_source();
        let canonical = crate::kernel::memory_history::canonical_value_load_memory(
            &source,
            address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
        );
        // A cell holding its own read (a materialization), as a named read or
        // as the load variable of its word, reads as that read.
        let own_read = |held: &SharedMemory| match held.memory().known_value(address) {
            Some(ProgramValue::Pointer(stored))
                if stored.address().as_loaded_value().is_some_and(|read| {
                    read.defining_address == *address
                        && read.displacement == AddressOffset::Constant(0)
                }) || matches!(
                    stored.address(),
                    Address {
                        base: AddressBase::Symbolic(variable),
                        offset: AddressOffset::Constant(0),
                    } if crate::kernel::registered_load_for_variable(variable)
                        .is_some_and(|(_, registered)| registered == *address)
                ) =>
            {
                Some(stored)
            }
            _ => None,
        };
        // The selected state can restore a checked loop-frame observation
        // without changing its byte identity. Inspect its cache before stripping
        // observation edges; the byte source need not retain that knowledge.
        if let Some(read) = own_read(memory)
            .or_else(|| own_read(&source))
            .or_else(|| own_read(&canonical))
        {
            return Ok(read);
        }
        // Pointer values retain the selected read directly. Observation metadata
        // records the live source independently of the term's identity.
        let bits = MachineTerm::MemoryLoad(
            ProgramPoint::at(memory),
            Box::new(address.clone()),
            LoadKind::Int32,
        );
        Err(Self::loaded(&bits).expect("a pointer read has a structural descriptor"))
    }

    pub(crate) fn symbolic_function(variable: Variable) -> Self {
        Self {
            base: AddressBase::FunctionSymbolic(variable),
            offset: AddressOffset::Constant(0),
        }
    }

    pub(crate) fn function(name: impl Into<String>) -> Self {
        Self {
            base: AddressBase::Function(name.into()),
            offset: AddressOffset::Constant(0),
        }
    }
    pub(in crate::kernel) fn has_symbolic_block(&self) -> bool {
        matches!(
            self.base,
            AddressBase::ExternalArgument
                | AddressBase::Symbolic(_)
                | AddressBase::LoadedPointer(_)
                | AddressBase::PureFunctionApplication(_)
        )
    }

    pub(in crate::kernel) fn blocks_proven_distinct(&self, other: &Self) -> bool {
        self.base.proven_distinct(&other.base)
    }
    pub(in crate::kernel) fn offset_by_int32_elements(&self, elements: MachineTerm) -> Self {
        self.offset_by_elements(elements, 4)
    }

    pub(crate) fn offset_by_bytes(&self, bytes: u32) -> Self {
        Self {
            base: self.base.clone(),
            offset: AddressOffset::add(
                self.offset.clone(),
                AddressOffset::Constant(i64::from(bytes)),
            ),
        }
    }

    pub(in crate::kernel) fn offset_by_shared_elements(
        &self,
        elements: SharedMachineIntegerTerm,
        byte_width: u32,
    ) -> Self {
        let displacement = match elements.operand_view().word32_constant() {
            Some(value) => AddressOffset::Constant(i64::from(value as i32) * i64::from(byte_width)),
            None => AddressOffset::Int32Scaled {
                value: elements,
                byte_width: i64::from(byte_width),
            },
        };
        Self {
            base: self.base.clone(),
            offset: AddressOffset::add(self.offset.clone(), displacement),
        }
    }

    pub(in crate::kernel) fn offset_by_elements(
        &self,
        elements: MachineTerm,
        byte_width: u32,
    ) -> Self {
        Self {
            base: self.base.clone(),
            offset: AddressOffset::add(
                self.offset.clone(),
                AddressOffset::scale_int32(elements, i64::from(byte_width)),
            ),
        }
    }

    pub(in crate::kernel) fn offset_by_typed_elements(
        &self,
        elements: MachineTerm,
        byte_width: u32,
        unsigned: bool,
        wide: bool,
    ) -> Self {
        Self {
            base: self.base.clone(),
            offset: AddressOffset::add(
                self.offset.clone(),
                if wide {
                    AddressOffset::scale_int64(elements, i64::from(byte_width), unsigned)
                } else {
                    AddressOffset::scale_int32(elements, i64::from(byte_width))
                },
            ),
        }
    }

    /// This pointer's offset less `base`'s, exactly, when both name one block
    /// and every non-constant summand of `base` occurs in this offset; see
    /// [`offset_less_base`].
    pub(crate) fn offset_from_base(&self, base: &Self) -> Option<AddressOffset> {
        if self.base != base.base {
            return None;
        }
        offset_less_base(&self.offset, &base.offset)
    }

    pub(crate) fn element_index_from_base(&self, base: &Self) -> Option<MachineTerm> {
        self.element_index_from_base_with_width(base, 4)
    }

    /// This pointer's exact unsigned 64-bit element index from `base`, for
    /// elements of `byte_width` bytes: the index of a wide offset `i *
    /// byte_width`, or a nonnegative constant offset divided out. No
    /// 32-bit reading of an index takes part.
    pub(crate) fn shared_wide_element_index_from_base(
        &self,
        base: &Self,
        byte_width: u32,
    ) -> Option<SharedMachineIntegerTerm> {
        let width = i64::from(byte_width);
        match self.offset_from_base(base)? {
            AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            } if byte_width == width => Some(value),
            AddressOffset::Constant(bytes) if bytes >= 0 && bytes % width == 0 => {
                let root = KernelTerm::retained_native_machine_operand(
                    MachineIntegerType::UInt64,
                    &MachineTerm::uint64_constant((bytes / width) as u64),
                );
                Some(MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64))
            }
            _ => None,
        }
    }

    pub(crate) fn element_index_from_base_with_width(
        &self,
        base: &Self,
        byte_width: u32,
    ) -> Option<MachineTerm> {
        if self.base != base.base {
            return None;
        }

        if self.offset == base.offset {
            return Some(MachineTerm::constant(0));
        }

        if base.offset == AddressOffset::Constant(0) {
            return crate::kernel::reasoning::element_index_from_offset(&self.offset, byte_width);
        }

        match &self.offset {
            AddressOffset::Add(left, right) if left.as_ref() == &base.offset => {
                crate::kernel::reasoning::element_index_from_offset(right, byte_width)
            }
            AddressOffset::Add(left, right) if right.as_ref() == &base.offset => {
                crate::kernel::reasoning::element_index_from_offset(left, byte_width)
            }
            _ => {
                if let Some(rest) = offset_less_base(&self.offset, &base.offset)
                    && let Some(index) = native_element_index_of_difference(&rest, byte_width)
                {
                    return Some(index);
                }
                if let (Some(pointer_index), Some(base_index)) = (
                    crate::kernel::reasoning::element_index_from_offset(&self.offset, byte_width),
                    crate::kernel::reasoning::element_index_from_offset(&base.offset, byte_width),
                ) {
                    Some(MachineTerm::subtract(pointer_index, base_index))
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn shared_element_index_from_base_with_width(
        &self,
        base: &Self,
        byte_width: u32,
    ) -> Option<SharedMachineIntegerTerm> {
        if self.base != base.base {
            return None;
        }

        if self.offset == base.offset {
            return Some(
                MachineOperandView::Legacy(&MachineTerm::constant(0))
                    .retain(MachineIntegerType::Int32),
            );
        }

        if base.offset == AddressOffset::Constant(0) {
            return crate::kernel::reasoning::shared_element_index_from_offset(
                &self.offset,
                byte_width,
            );
        }

        match &self.offset {
            AddressOffset::Add(left, right) if left.as_ref() == &base.offset => {
                crate::kernel::reasoning::shared_element_index_from_offset(right, byte_width)
            }
            AddressOffset::Add(left, right) if right.as_ref() == &base.offset => {
                crate::kernel::reasoning::shared_element_index_from_offset(left, byte_width)
            }
            _ => {
                if let Some(rest) = offset_less_base(&self.offset, &base.offset)
                    && let Some(index) = element_index_of_difference(&rest, byte_width)
                {
                    return Some(index);
                }
                if let (Some(pointer_index), Some(base_index)) = (
                    crate::kernel::reasoning::shared_element_index_from_offset(
                        &self.offset,
                        byte_width,
                    ),
                    crate::kernel::reasoning::shared_element_index_from_offset(
                        &base.offset,
                        byte_width,
                    ),
                ) {
                    Some(crate::kernel::assumptions::index_binary(
                        MachineBinaryOp::Subtract,
                        pointer_index.operand_view(),
                        base_index.operand_view(),
                    ))
                } else {
                    None
                }
            }
        }
    }

    /// [`Self::element_index_from_base_with_width`] for a caller that needs the
    /// delta's `i64` value rather than its residue.
    ///
    /// Same shapes, answered exactly. The index that function returns is a
    /// modular `MachineTerm`, so it names the delta only modulo `2^32`:
    /// the two byte offsets are exact `i64`, and every step that folds them
    /// into one 32-bit index — an `Add` of two displacements, the closing
    /// `MachineTerm::subtract` — can wrap. A rule concluding *membership*
    /// or *containment* is reading the delta as a number and needs this form;
    /// see [`crate::kernel::reasoning::ExactElementDelta`].
    pub(in crate::kernel) fn exact_element_delta_from_base(
        &self,
        base: &Self,
        byte_width: u32,
        assumptions: Option<&PureFactContext>,
    ) -> Option<crate::kernel::reasoning::ExactElementDelta> {
        use crate::kernel::reasoning::{ExactElementDelta, exact_element_delta_from_offset};

        if self.base != base.base {
            return None;
        }
        if self.offset == base.offset {
            return Some(ExactElementDelta::zero());
        }
        if base.offset == AddressOffset::Constant(0) {
            return exact_element_delta_from_offset(&self.offset, byte_width);
        }
        match &self.offset {
            AddressOffset::Add(left, right) if left.as_ref() == &base.offset => {
                exact_element_delta_from_offset(right, byte_width)
            }
            AddressOffset::Add(left, right) if right.as_ref() == &base.offset => {
                exact_element_delta_from_offset(left, byte_width)
            }
            _ => {
                if let Some(rest) = offset_less_base(&self.offset, &base.offset)
                    && let Some(delta) = exact_element_delta_from_offset(&rest, byte_width)
                {
                    return Some(delta);
                }
                exact_element_delta_from_offset(&self.offset, byte_width)?.subtract(
                    exact_element_delta_from_offset(&base.offset, byte_width)?,
                    assumptions,
                )
            }
        }
    }
}

/// The element index of a difference [`offset_less_base`] returned, spelled
/// as the kernel spells an index less a constant: a negative trailing
/// constant is `index - c`, the form [`MachineTerm::subtract`] gives
/// `(b + i) - (b + c)`, rather than the residue `index + (2^32 - c)`.
fn native_element_index_of_difference(
    difference: &AddressOffset,
    byte_width: u32,
) -> Option<MachineTerm> {
    if let AddressOffset::Add(symbolic, constant) = difference
        && let AddressOffset::Constant(bytes) = constant.as_ref()
        && *bytes < 0
    {
        let elements = crate::kernel::reasoning::element_index_from_offset(
            &AddressOffset::Constant(-bytes),
            byte_width,
        )?;
        return Some(MachineTerm::subtract(
            crate::kernel::reasoning::element_index_from_offset(symbolic, byte_width)?,
            elements,
        ));
    }
    crate::kernel::reasoning::element_index_from_offset(difference, byte_width)
}

fn element_index_of_difference(
    difference: &AddressOffset,
    byte_width: u32,
) -> Option<SharedMachineIntegerTerm> {
    if let AddressOffset::Add(symbolic, constant) = difference
        && let AddressOffset::Constant(bytes) = constant.as_ref()
        && *bytes < 0
    {
        let elements = crate::kernel::reasoning::shared_element_index_from_offset(
            &AddressOffset::Constant(-bytes),
            byte_width,
        )?;
        return Some(crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Subtract,
            crate::kernel::reasoning::shared_element_index_from_offset(symbolic, byte_width)?
                .operand_view(),
            elements.operand_view(),
        ));
    }
    crate::kernel::reasoning::shared_element_index_from_offset(difference, byte_width)
}

/// `offset - base`, exactly, as the summands of `offset` that `base` does not
/// account for: `((b + k) + 4) - b` is `k + 4`, and `(b + k + 12) - (b + 8)`
/// is `k + 4`.
///
/// A pointer offset is a mathematical `i64` sum, so removing a summand that
/// occurs on both sides and subtracting the constant parts is exact; nothing
/// here reads a residue. Every non-constant summand of `base` must occur
/// syntactically among those of `offset`, each occurrence matched once, or
/// there is no answer and the caller keeps its own. The walk is over the two
/// terms and nothing else.
fn offset_less_base(offset: &AddressOffset, base: &AddressOffset) -> Option<AddressOffset> {
    fn summands(term: &AddressOffset) -> Option<(Vec<&AddressOffset>, i64)> {
        let mut symbolic = Vec::new();
        let mut constant = 0i64;
        let mut pending = vec![term];
        while let Some(current) = pending.pop() {
            if let Some(value) = current.as_const() {
                constant = constant.checked_add(value)?;
                continue;
            }
            match current {
                AddressOffset::Add(left, right) => {
                    // Right first, so `left` is walked first and the
                    // summands keep their written order.
                    pending.push(right);
                    pending.push(left);
                }
                other => symbolic.push(other),
            }
        }
        Some((symbolic, constant))
    }
    let (mut rest, offset_constant) = summands(offset)?;
    let (base_summands, base_constant) = summands(base)?;
    for summand in base_summands {
        let position = rest.iter().position(|candidate| *candidate == summand)?;
        rest.remove(position);
    }
    let constant = offset_constant.checked_sub(base_constant)?;
    let difference = rest
        .into_iter()
        .cloned()
        .reduce(AddressOffset::add)
        .unwrap_or(AddressOffset::Constant(0));
    Some(AddressOffset::add(
        difference,
        AddressOffset::Constant(constant),
    ))
}

#[cfg(test)]
mod float_evaluator_differential_tests {
    use super::*;

    struct FloatCase {
        name: &'static str,
        a: u64,
        b: u64,
        operator: FloatBinaryOperator,
        exponent_bits: u32,
        fraction_bits: u32,
        expected: u64,
    }

    /// Differential guard for the integer-space IEEE-754 evaluator
    /// (the subnormal-division regression). A fixed vector of operand bit
    /// patterns spanning signed zeros, subnormals, infinities, NaNs, cancellation pairs, and
    /// normal/subnormal boundary results, checked against correctly rounded
    /// results. Expected values were computed with exact rational arithmetic
    /// and confirmed against a C compiler on this profile. NaN cases expect
    /// the evaluator's canonical NaN; payloads are not compared.
    #[test]
    fn float_binary_matches_reference() {
        use FloatBinaryOperator::{Add, Divide, Multiply, Subtract};
        let cases = [
            // Division: the subnormal-division regression is fixed. The first
            // case is the regression itself: the sticky bit collided with the
            // rounding bit and folded one ulp high (0x18, not 0x17).
            FloatCase {
                name: "s13 subnormal dividend",
                a: 0x00000003,
                b: 0x3e02b932,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000017,
            },
            FloatCase {
                name: "div subnormal quotient drift",
                a: 0x00004d7f,
                b: 0x006b25e4,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3b3927b4,
            },
            FloatCase {
                name: "div subnormal dividend near tie",
                a: 0x000dae8f,
                b: 0x004f725d,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3e3058f7,
            },
            FloatCase {
                name: "div 1/3",
                a: 0x3f800000,
                b: 0x40400000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3eaaaaab,
            },
            FloatCase {
                name: "div 2/3",
                a: 0x40000000,
                b: 0x40400000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3f2aaaab,
            },
            FloatCase {
                name: "div 1/0",
                a: 0x3f800000,
                b: 0x00000000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7f800000,
            },
            FloatCase {
                name: "div -1/0",
                a: 0xbf800000,
                b: 0x00000000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0xff800000,
            },
            FloatCase {
                name: "div 0/0",
                a: 0x00000000,
                b: 0x00000000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7fc00000,
            },
            FloatCase {
                name: "div inf/inf",
                a: 0x7f800000,
                b: 0x7f800000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7fc00000,
            },
            FloatCase {
                name: "div 5/inf",
                a: 0x40a00000,
                b: 0x7f800000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000000,
            },
            FloatCase {
                name: "div -0/5",
                a: 0x80000000,
                b: 0x40a00000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x80000000,
            },
            FloatCase {
                name: "div max/0.5 overflows",
                a: 0x7f7fffff,
                b: 0x3f000000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7f800000,
            },
            FloatCase {
                name: "div 1/4 exact",
                a: 0x3f800000,
                b: 0x40800000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3e800000,
            },
            FloatCase {
                name: "div min-subnormal/2 underflows",
                a: 0x00000001,
                b: 0x40000000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000000,
            },
            FloatCase {
                name: "div tiny-normal/16 subnormal",
                a: 0x00800000,
                b: 0x41800000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00080000,
            },
            FloatCase {
                name: "div max-subnormal/1",
                a: 0x007fffff,
                b: 0x3f800000,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x007fffff,
            },
            FloatCase {
                name: "div subnormal/subnormal",
                a: 0x00000002,
                b: 0x00000001,
                operator: Divide,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x40000000,
            },
            FloatCase {
                name: "div f64 1/3",
                a: 0x3ff0000000000000,
                b: 0x4008000000000000,
                operator: Divide,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x3fd5555555555555,
            },
            FloatCase {
                name: "div f64 min-subnormal/2 underflows",
                a: 0x0000000000000001,
                b: 0x4000000000000000,
                operator: Divide,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x0000000000000000,
            },
            FloatCase {
                name: "div f64 tiny-normal/2^24 subnormal",
                a: 0x0010000000000000,
                b: 0x4160000000000000,
                operator: Divide,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x0000000020000000,
            },
            FloatCase {
                name: "div f64 0/0",
                a: 0x0000000000000000,
                b: 0x0000000000000000,
                operator: Divide,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x7ff8000000000000,
            },
            FloatCase {
                name: "div f64 1/0",
                a: 0x3ff0000000000000,
                b: 0x0000000000000000,
                operator: Divide,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x7ff0000000000000,
            },
            // Addition/subtraction: cancellation, signed zeros, infinities.
            FloatCase {
                name: "sub cancellation",
                a: 0x3f800000,
                b: 0x3f780000,
                operator: Subtract,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3d000000,
            },
            FloatCase {
                name: "add 1+(-1)",
                a: 0x3f800000,
                b: 0xbf800000,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000000,
            },
            FloatCase {
                name: "add -0+-0",
                a: 0x80000000,
                b: 0x80000000,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x80000000,
            },
            FloatCase {
                name: "add inf+-inf",
                a: 0x7f800000,
                b: 0xff800000,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7fc00000,
            },
            FloatCase {
                name: "add max+max overflows",
                a: 0x7f7fffff,
                b: 0x7f7fffff,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7f800000,
            },
            FloatCase {
                name: "add min-subnormal+min-subnormal",
                a: 0x00000001,
                b: 0x00000001,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000002,
            },
            FloatCase {
                name: "add 0.1f+0.2f",
                a: 0x3dcccccd,
                b: 0x3e4ccccd,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3e99999a,
            },
            FloatCase {
                name: "add 1+2^-24 ties to even",
                a: 0x3f800000,
                b: 0x33800000,
                operator: Add,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x3f800000,
            },
            FloatCase {
                name: "sub 5-3",
                a: 0x40a00000,
                b: 0x40400000,
                operator: Subtract,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x40000000,
            },
            // Multiplication: zeros, infinities, subnormal boundaries.
            FloatCase {
                name: "mul 1.5*2.5",
                a: 0x3fc00000,
                b: 0x40200000,
                operator: Multiply,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x40700000,
            },
            FloatCase {
                name: "mul min-subnormal*2",
                a: 0x00000001,
                b: 0x40000000,
                operator: Multiply,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000002,
            },
            FloatCase {
                name: "mul max*2 overflows",
                a: 0x7f7fffff,
                b: 0x40000000,
                operator: Multiply,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7f800000,
            },
            FloatCase {
                name: "mul 0*inf",
                a: 0x00000000,
                b: 0x7f800000,
                operator: Multiply,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x7fc00000,
            },
            FloatCase {
                name: "mul subnormal*subnormal underflows",
                a: 0x00000001,
                b: 0x00000001,
                operator: Multiply,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x00000000,
            },
            FloatCase {
                name: "mul -0*5",
                a: 0x80000000,
                b: 0x40a00000,
                operator: Multiply,
                exponent_bits: 8,
                fraction_bits: 23,
                expected: 0x80000000,
            },
            FloatCase {
                name: "add f64 1+(-1)",
                a: 0x3ff0000000000000,
                b: 0xbff0000000000000,
                operator: Add,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x0000000000000000,
            },
            FloatCase {
                name: "mul f64 1.5*2.5",
                a: 0x3ff8000000000000,
                b: 0x4004000000000000,
                operator: Multiply,
                exponent_bits: 11,
                fraction_bits: 52,
                expected: 0x400e000000000000,
            },
        ];
        for case in cases {
            let got = float_binary_bits(
                case.a,
                case.b,
                case.exponent_bits,
                case.fraction_bits,
                case.operator,
            );
            assert_eq!(
                got, case.expected,
                "float evaluator mismatch for {}: {:#x} op {:#x} gave {:#x}, expected {:#x}",
                case.name, case.a, case.b, got, case.expected,
            );
        }
    }
}

#[cfg(test)]
mod shift_overflow_refusal_tests {
    use super::*;

    #[test]
    fn out_of_range_shift_count_does_not_fold_to_no_overflow() {
        let left = MachineTerm::constant(1);
        let right = MachineTerm::constant(40);

        assert_eq!(
            signed_shift_left_overflows_const(1, 40),
            None,
            "the helper must refuse to decide an out-of-range count"
        );
        assert_eq!(
            ConditionTerm::signed_shift_left_overflows(left.clone(), right.clone()),
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::ShiftLeft,
                left: Box::new(left),
                right: Box::new(right)
            },
            "an out-of-range shift must not become the safe constant false"
        );
    }
}

/// Whether a proposition holds with no facts at all, by a constant structural
/// check: a condition that is the ground constant it asserts, a closed native
/// comparison, or a comparison of a term with itself whose value
/// ([`ConditionTerm::reflexive_value`]) is the one asserted.
///
/// Every `using` list consults this one rule, so a premise that states such a
/// fact needs no fact behind it wherever it is listed, and the kernel's
/// condition decision answers the same comparisons the same way.
pub(crate) fn proposition_holds_without_facts(proposition: &Proposition) -> bool {
    match proposition {
        condition_source_0 @ Proposition::ConditionIs(_, value)
            if let Some((ConditionTerm::Constant(constant), _)) =
                condition_source_0.condition_native() =>
        {
            constant == value
        }
        condition_source_0 @ Proposition::ConditionIs(_, value)
            if let Some((
                condition @ ConditionTerm::Compare {
                    format,
                    left,
                    right,
                    ..
                },
                _,
            )) = condition_source_0.condition_native()
                && (format.constant_from_term(left).is_some()
                    && format.constant_from_term(right).is_some()) =>
        {
            PureFactContext::decide_intrinsically(condition) == Some(*value)
        }
        Proposition::ConditionIs(condition, value) => {
            condition.native_compat().reflexive_value() == Some(*value)
        }
        _ => false,
    }
}

/// Whether `proposition` holds by the range of its operand's format alone:
/// a comparison of one machine value with a constant that every value of
/// the format meets (maintainer direction, 2026-10-31). The value's range is
/// its own format's, or for the 32-bit widening of an 8- or 16-bit value
/// its source's: `widen(x) >= -128` for an `int8` `x`, `0 <= to_integer(b)`
/// for a `uint8` `b`. A bound past the range is not implied, and a fact the
/// context states is not consulted. One match on the root and its operands.
pub(crate) fn holds_by_format_range(proposition: &Proposition) -> bool {
    use CompareRelation as R;
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    // The range of a machine operand read at `format`.
    fn machine_range(
        term: MachineOperandView<'_>,
        format: MachineIntegerType,
    ) -> Option<(i128, i128)> {
        let bounds = |ty: MachineIntegerType| {
            let (lo, hi) = ty.format().bounds();
            Some((i128::try_from(lo).ok()?, i128::try_from(hi).ok()?))
        };
        match term.narrow_widening32_operand() {
            // A 32-bit comparison reads a widened narrow value as its source
            // value, except an `int8`/`int16` value read unsigned.
            Some((source, _)) if format.format().bits() == 32 => (format.format().is_signed()
                || !source.format().is_signed())
            .then(|| bounds(source))
            .flatten(),
            _ if format.format().bits() < 32 && format.format().bits() > 0 => bounds(format),
            _ => None,
        }
    }
    let decide = |(lo, hi): (i128, i128), relation: R, constant: i128, flipped: bool| {
        // `x REL c`, or `c REL x` when `flipped`.
        let (low_true, high_true) = match (relation, flipped) {
            (R::LessThan, false) | (R::GreaterThan, true) => (hi < constant, lo >= constant),
            (R::LessEqual, false) | (R::GreaterEqual, true) => (hi <= constant, lo > constant),
            (R::GreaterThan, false) | (R::LessThan, true) => (lo > constant, hi <= constant),
            (R::GreaterEqual, false) | (R::LessEqual, true) => (lo >= constant, hi < constant),
            (R::Equal, _) => (
                lo == constant && hi == constant,
                constant < lo || constant > hi,
            ),
        };
        // `low_true`: every value meets it; `high_true`: none does.
        if low_true {
            Some(true)
        } else if high_true {
            Some(false)
        } else {
            None
        }
    };
    let truth = match condition.native_compat() {
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } => {
            let constant = |term: &MachineTerm| {
                format
                    .constant_from_term(term)
                    .and_then(MachineIntegerConstant::to_i128)
            };
            match (constant(left), constant(right)) {
                (None, Some(c)) => machine_range(MachineOperandView::Legacy(left), *format)
                    .and_then(|range| decide(range, *relation, c, false)),
                (Some(c), None) => machine_range(MachineOperandView::Legacy(right), *format)
                    .and_then(|range| decide(range, *relation, c, true)),
                _ => None,
            }
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => {
            let relation = match condition.native_compat() {
                ConditionTerm::IntegerLessThan(..) => R::LessThan,
                ConditionTerm::IntegerLessEqual(..) => R::LessEqual,
                ConditionTerm::IntegerGreaterThan(..) => R::GreaterThan,
                _ => R::GreaterEqual,
            };
            let range = |term: &IntegerTerm| match term {
                IntegerTerm::Machine(machine) => machine
                    .operand_view()
                    .narrow_widening32_operand()
                    .map_or(machine.ty(), |(source, _)| source)
                    .format()
                    .bounds(),
                _ => (num_bigint::BigInt::from(1), num_bigint::BigInt::from(0)),
            };
            let constant =
                |term: &IntegerTerm| term.as_const().and_then(|c| i128::try_from(c).ok());
            let in_range = |(lo, hi): (num_bigint::BigInt, num_bigint::BigInt)| {
                Some((i128::try_from(lo).ok()?, i128::try_from(hi).ok()?))
                    .filter(|(lo, hi)| lo <= hi)
            };
            match (constant(left), constant(right)) {
                (None, Some(c)) => {
                    in_range(range(left)).and_then(|range| decide(range, relation, c, false))
                }
                (Some(c), None) => {
                    in_range(range(right)).and_then(|range| decide(range, relation, c, true))
                }
                _ => None,
            }
        }
        _ => None,
    };
    truth == Some(*value)
}

/// An equality or disequality with its sides swapped. `have a == b` and
/// `have b == a` establish one fact, so a `using` premise may name either spelling of the
/// fact the proof holds.
pub(crate) fn mirrored_equality(proposition: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let mirrored = match condition.native_compat() {
        ConditionTerm::IntegerEqual(left, right) => {
            ConditionTerm::IntegerEqual(right.clone(), left.clone())
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            ConditionTerm::IntegerNotEqual(right.clone(), left.clone())
        }
        ConditionTerm::AlgebraicEqual(left, right) => {
            ConditionTerm::AlgebraicEqual(right.clone(), left.clone())
        }
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::Equal,
            left,
            right,
        } => ConditionTerm::Compare {
            format: *format,
            relation: CompareRelation::Equal,
            left: right.clone(),
            right: left.clone(),
        },
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: right.clone(),
            right: left.clone(),
        },
        ConditionTerm::AddressOffsetEqual(left, right) => {
            ConditionTerm::AddressOffsetEqual(right.clone(), left.clone())
        }
        ConditionTerm::AddressEqual(left, right) => {
            ConditionTerm::AddressEqual(right.clone(), left.clone())
        }
        ConditionTerm::PointerEqual(left, right) => {
            ConditionTerm::PointerEqual(right.clone(), left.clone())
        }
        _ => return None,
    };
    Some(Proposition::condition_is(mirrored, *value))
}

/// The one availability rule for a premise a `using` list names, over the
/// lookup `available` the site already owns: the premise holds with no facts
/// ([`proposition_holds_without_facts`]), or it or its mirrored equality
/// ([`mirrored_equality`]) is available. Every using list, and every checker
/// that matches a theorem requirement against listed evidence, asks this and
/// nothing else, so no site accepts a spelling another refuses.
pub(crate) fn listed_premise_holds(
    premise: &Proposition,
    available: impl Fn(&Proposition) -> bool,
) -> bool {
    if listed_premise_holds_with(premise, &available) {
        return true;
    }
    crate::kernel::arithmetic_comparison_form(premise)
        .is_some_and(|comparison| listed_premise_holds_with(&comparison, &available))
}

fn listed_premise_holds_with(
    premise: &Proposition,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    proposition_holds_without_facts(premise)
        // Instantiating an Integer theorem preserves a constant arithmetic
        // DAG such as `0 == 0 + 0`, while a written citation may lower to
        // `true`. Both denote the same ground fact. The evaluator rejects
        // symbolic operands from cached shape flags and uses only the named
        // expression's shared DAG, never the available-fact collection.
        || matches!(premise, Proposition::ConditionIs(condition, expected)
            if crate::kernel::proof::integer_arithmetic::literal_integer_comparison_value(condition.native_compat())
                == Some(*expected))
        || holds_by_format_range(premise)
        || available(premise)
        || mirrored_equality(premise).is_some_and(|mirrored| available(&mirrored))
        // A conjunction holds when each conjunct does. A theorem's
        // `defined((t + pos) + 4)`, instantiated at `pos := r - x`, is the
        // two no-overflow conditions of its own sums; the fact written at
        // the call also carries `r - x`'s, nested differently.
        || matches!(premise, Proposition::And(left, right)
            if listed_premise_holds_with(left, available)
                && listed_premise_holds_with(right, available))
}

#[cfg(test)]
mod integer_equality_citation_tests {
    use super::*;

    #[test]
    fn listed_closed_native_order_is_checked_without_facts() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let condition = ConditionTerm::Compare {
                format,
                relation: CompareRelation::LessThan,
                left: Box::new(
                    crate::kernel::machine_integer::range::constant_word(format, &0.into())
                        .unwrap(),
                ),
                right: Box::new(
                    crate::kernel::machine_integer::range::constant_word(format, &2.into())
                        .unwrap(),
                ),
            };
            assert!(listed_premise_holds(
                &Proposition::condition_is(condition.clone(), true),
                |_| false
            ));
            assert!(!listed_premise_holds(
                &Proposition::condition_is(condition, false),
                |_| false
            ));
        }
    }

    #[test]
    fn listed_integer_constant_arithmetic_is_available_without_facts() {
        let zero: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
        let sum: SharedIntegerTerm = IntegerTerm::Add(zero.clone(), zero.clone()).into();
        let equality = ConditionTerm::IntegerEqual(zero.clone(), sum);
        assert!(listed_premise_holds(
            &Proposition::condition_is(equality.clone(), true),
            |_| false
        ));
        assert!(!listed_premise_holds(
            &Proposition::condition_is(equality, false),
            |_| false
        ));
        let symbolic = ConditionTerm::IntegerEqual(
            zero.clone(),
            IntegerTerm::Variable(Variable(931_001)).into(),
        );
        assert!(!listed_premise_holds(
            &Proposition::condition_is(symbolic, true),
            |_| false
        ));
        let undefined = ConditionTerm::IntegerEqual(
            IntegerTerm::truncating_quotient(
                IntegerTerm::constant_i64(1),
                IntegerTerm::constant_i64(0),
            )
            .into(),
            zero,
        );
        assert!(!listed_premise_holds(
            &Proposition::condition_is(undefined, true),
            |_| false
        ));
    }

    #[test]
    fn integer_equality_mirroring_preserves_polarity_and_exact_operands() {
        let left: SharedIntegerTerm = IntegerTerm::Variable(Variable(931_011)).into();
        let right: SharedIntegerTerm = IntegerTerm::Variable(Variable(931_012)).into();
        for polarity in [true, false] {
            let source = Proposition::condition_is(
                ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                polarity,
            );
            let target = Proposition::condition_is(
                ConditionTerm::IntegerEqual(right.clone(), left.clone()),
                polarity,
            );
            assert_eq!(mirrored_equality(&source), Some(target.clone()));
            assert_eq!(mirrored_equality(&target), Some(source.clone()));
            assert!(listed_premise_holds(&target, |fact| fact == &source));
            let wrong_polarity = Proposition::condition_is(
                ConditionTerm::IntegerEqual(right.clone(), left.clone()),
                !polarity,
            );
            assert!(!listed_premise_holds(&wrong_polarity, |fact| fact == &source));
        }
        let ordered = Proposition::condition_is(ConditionTerm::IntegerLessThan(left, right), true);
        assert!(mirrored_equality(&ordered).is_none());
    }
}

#[cfg(test)]
mod connective_walk_tests {
    use super::*;

    /// A right side whose left sibling already decides the connective is
    /// not asked, and the answer is the one asking it would give.
    #[test]
    fn a_decided_connective_does_not_ask_its_right_side() {
        let side = |name: u64| {
            Proposition::condition_is(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(name)),
                    MachineTerm::constant(0),
                ),
                true,
            )
        };
        let (held, missing, other) = (side(1), side(2), side(3));
        let or = |left: &Proposition, right: &Proposition| {
            Proposition::Or(Box::new(left.clone()), Box::new(right.clone()))
        };
        let and = |left: &Proposition, right: &Proposition| {
            Proposition::And(Box::new(left.clone()), Box::new(right.clone()))
        };
        let walk = |root: &Proposition| {
            let asked = std::cell::RefCell::new(Vec::new());
            let result = first_unavailable_connective_side(root, &|side| {
                asked.borrow_mut().push(side.clone());
                side == &held
            })
            .cloned();
            (result, asked.into_inner())
        };
        // `held or missing` holds without asking `missing`.
        let (result, asked) = walk(&or(&held, &missing));
        assert_eq!(result, None);
        assert!(!asked.contains(&missing), "{asked:?}");
        // `missing or held` asks both and holds.
        let (result, asked) = walk(&or(&missing, &held));
        assert_eq!(result, None);
        assert!(asked.contains(&held));
        // `missing or other` names the disjunction.
        let root = or(&missing, &other);
        assert_eq!(walk(&root).0, Some(root.clone()));
        // `missing and held` names `missing` without asking `held`.
        let (result, asked) = walk(&and(&missing, &held));
        assert_eq!(result, Some(missing.clone()));
        assert!(!asked.contains(&held), "{asked:?}");
        // `held and missing` asks both and names `missing`.
        assert_eq!(walk(&and(&held, &missing)).0, Some(missing.clone()));
        // Nested: the decided disjunction skips its right side, and the
        // enclosing conjunction still asks its own.
        let (result, asked) = walk(&and(&or(&held, &missing), &other));
        assert_eq!(result, Some(other.clone()));
        assert!(
            !asked.contains(&missing) && asked.contains(&other),
            "{asked:?}"
        );
    }
}

/// Whether `root` follows from facts through its own `and`/`or` structure:
/// a side holds when `available` says so, a conjunction when both sides do,
/// a disjunction when either does. Returns the first side that fails, or
/// `None` when the goal holds. The walk is iterative because conjunction
/// spines are long, and it visits each side of the goal at most once. A
/// right side is not visited when its left side already decides the
/// connective: a disjunction whose left side holds, or a conjunction whose
/// left side fails.
pub(crate) fn first_unavailable_connective_side<'a>(
    root: &'a Proposition,
    available: &impl Fn(&Proposition) -> bool,
) -> Option<&'a Proposition> {
    enum Task<'a> {
        Visit(&'a Proposition),
        // The right side of a connective, visited only when the left side's
        // result, on top of the result stack, leaves the connective open.
        VisitRight(&'a Proposition, &'a Proposition),
        Join(&'a Proposition),
    }
    let mut tasks = vec![Task::Visit(root)];
    // Each finished side leaves the first unavailable side beneath it.
    let mut results: Vec<Option<&'a Proposition>> = Vec::new();
    while let Some(task) = tasks.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match task {
            // Conjunction facts are admitted as their conjuncts. Do not
            // query a whole subtree again at every point along a spine.
            Task::Visit(side) if !matches!(side, Proposition::And(..)) && available(side) => {
                results.push(None);
            }
            Task::Visit(side @ (Proposition::And(left, right) | Proposition::Or(left, right))) => {
                tasks.push(Task::Join(side));
                tasks.push(Task::VisitRight(side, right));
                tasks.push(Task::Visit(left));
            }
            // The join reads the right side only when the left side leaves
            // the connective open: an available left disjunct joins to
            // `None`, and an unavailable left conjunct joins to itself,
            // whatever the right side gives. So the placeholder pushed for
            // an unread right side leaves every result unchanged, and the
            // right side is not asked. Asking it was not free: `available`
            // runs frozen atomic checkers, and the right disjunct of a
            // null-guarded requirement, `p == 0 or separate(memory(q),
            // memory(p->f))` with `p == 0` known, is a separation nothing
            // can establish, refused only after every route had asked the
            // owned members of its block to contain each side.
            Task::VisitRight(parent, right) => {
                let left = *results
                    .last()
                    .expect("a right side follows its left side's result");
                match (parent, left) {
                    (Proposition::Or(..), None) | (Proposition::And(..), Some(_)) => {
                        results.push(None);
                    }
                    _ => tasks.push(Task::Visit(right)),
                }
            }
            Task::Visit(side) => results.push(Some(side)),
            Task::Join(side) => {
                let right = results.pop().expect("a joined side has a right result");
                let left = results.pop().expect("a joined side has a left result");
                results.push(match side {
                    Proposition::And(..) => left.or(right),
                    // A disjunction needs one side; when neither holds, the
                    // disjunction itself is what is missing.
                    _ => left.and(right).map(|_| side),
                });
            }
        }
    }
    results.pop().expect("the root leaves one result")
}

/// Select a read structurally, retaining legacy variables only as input adapters.
fn canonical_pointer_read(bits: &MachineTerm) -> Option<MachineTerm> {
    let read = match bits {
        MachineTerm::MemoryLoad(..) => crate::kernel::eval::canonical_scalar_read(bits),
        MachineTerm::Variable(variable) => {
            crate::kernel::registered_load_term_for_variable(variable)?
        }
        _ => return None,
    };
    Some(read)
}

fn named_pointer_read(read: MachineTerm) -> Address {
    let MachineTerm::MemoryLoad(memory, address, _) = &read else {
        unreachable!("selected pointer read");
    };
    let value = Address::loaded_value(&memory.shared_memory().unchanged_bytes_source(), address);
    if let AddressBase::LoadedPointer(identity) = value.base {
        crate::kernel::eval::record_pointer_load_source(identity, &read);
    }
    value
}

#[cfg(test)]
mod format_range_premise_tests {
    use super::*;

    fn widen(source: MachineIntegerType, id: u64) -> MachineTerm {
        MachineTerm::machine_integer_cast(
            source,
            MachineIntegerType::Int32,
            MachineTerm::Variable(Variable(id)),
        )
    }

    fn holds(relation: CompareRelation, left: MachineTerm, bound: i32) -> bool {
        holds_by_format_range(&Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation,
                left: Box::new(left),
                right: Box::new(MachineTerm::constant(bound as u32)),
            },
            true,
        ))
    }

    /// A premise its operand's format range implies is available at every
    /// narrow width; a bound one step past the range is not.
    #[test]
    fn a_premise_within_the_format_range_holds_and_one_past_it_does_not() {
        use CompareRelation::{GreaterEqual, LessEqual};
        for (source, lo, hi) in [
            (MachineIntegerType::Int8, -128, 127),
            (MachineIntegerType::UInt8, 0, 255),
            (MachineIntegerType::Int16, -32768, 32767),
            (MachineIntegerType::UInt16, 0, 65535),
        ] {
            assert!(holds(GreaterEqual, widen(source, 7), lo), "{source:?}");
            assert!(holds(LessEqual, widen(source, 7), hi), "{source:?}");
            assert!(!holds(GreaterEqual, widen(source, 7), lo + 1), "{source:?}");
            assert!(!holds(LessEqual, widen(source, 7), hi - 1), "{source:?}");
            // The Integer reading of the narrow value has the same range.
            let observed: SharedIntegerTerm =
                IntegerTerm::from_machine(source, MachineTerm::Variable(Variable(8)))
                    .unwrap()
                    .into();
            let at_least = |bound: i64| {
                holds_by_format_range(&Proposition::condition_is(
                    ConditionTerm::IntegerLessEqual(
                        IntegerTerm::constant_i64(bound).into(),
                        observed.clone(),
                    ),
                    true,
                ))
            };
            assert!(at_least(lo as i64), "{source:?}");
            assert!(!at_least(lo as i64 + 1), "{source:?}");
        }
        // A 32-bit value's word has no narrower range to lend.
        assert!(!holds(
            GreaterEqual,
            MachineTerm::Variable(Variable(9)),
            -128
        ));
    }
    #[test]
    fn shared_format_ranges_preserve_true_false_and_unknown_without_exports() {
        use crate::kernel::{KernelTerm, KernelTermExport, KernelType, VerificationSession};
        use MachineIntegerType as T;
        let cases = [
            (T::Int32, None),
            (T::UInt32, None),
            (T::Int64, None),
            (T::UInt64, None),
            (T::Int32, Some(T::Int8)),
            (T::Int32, Some(T::UInt8)),
            (T::Int32, Some(T::Int16)),
            (T::Int32, Some(T::UInt16)),
            (T::UInt32, Some(T::UInt8)),
            (T::UInt32, Some(T::UInt16)),
        ];
        for (index, (format, narrow)) in cases.into_iter().enumerate() {
            let _session = VerificationSession::enter();
            let variable = Variable(994000 + index as u64);
            let root = if let Some(source) = narrow {
                KernelTerm::machine_cast_shared(
                    MachineCastSpelling::Generic,
                    source,
                    format,
                    KernelTerm::variable(KernelType::Program(source.program_type()), variable),
                )
            } else {
                let leaf =
                    KernelTerm::variable(KernelType::Program(format.program_type()), variable);
                KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [leaf.clone(), leaf],
                )
            };
            let machine = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
            assert!(!machine.has_boxed_operand());
            let observed: SharedIntegerTerm = IntegerTerm::Machine(machine).into();
            let (lo, hi) = narrow.unwrap_or(format).format().bounds();
            let (lo, hi) = (i128::try_from(lo).unwrap(), i128::try_from(hi).unwrap());
            let exports = KernelTermExport::machine_export_count();
            for bound in [lo - 1, lo, 1, hi, hi + 1] {
                for relation in [
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                ] {
                    for flipped in [false, true] {
                        let constant: SharedIntegerTerm =
                            IntegerTerm::constant(bound.into()).into();
                        let (left, right) = if flipped {
                            (constant, observed.clone())
                        } else {
                            (observed.clone(), constant)
                        };
                        let condition = match relation {
                            CompareRelation::LessThan => {
                                ConditionTerm::IntegerLessThan(left, right)
                            }
                            CompareRelation::LessEqual => {
                                ConditionTerm::IntegerLessEqual(left, right)
                            }
                            CompareRelation::GreaterThan => {
                                ConditionTerm::IntegerGreaterThan(left, right)
                            }
                            CompareRelation::GreaterEqual => {
                                ConditionTerm::IntegerGreaterEqual(left, right)
                            }
                            _ => unreachable!(),
                        };
                        let at = |value| {
                            let (a, b) = if flipped {
                                (bound, value)
                            } else {
                                (value, bound)
                            };
                            match relation {
                                CompareRelation::LessThan => a < b,
                                CompareRelation::LessEqual => a <= b,
                                CompareRelation::GreaterThan => a > b,
                                CompareRelation::GreaterEqual => a >= b,
                                _ => unreachable!(),
                            }
                        };
                        for truth in [true, false] {
                            assert_eq!(
                                holds_by_format_range(&Proposition::condition_is(
                                    condition.clone(),
                                    truth
                                )),
                                at(lo) == truth && at(hi) == truth,
                                "{format:?}/{narrow:?}, {relation:?} {bound}, flipped={flipped}, truth={truth}"
                            );
                        }
                    }
                }
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn shared_narrow_widening_view_matches_the_written_cast() {
        use crate::kernel::{KernelTermExport, KernelTermImport, VerificationSession};
        use MachineIntegerType as T;
        let _session = VerificationSession::enter();
        for (source, destination) in [
            (T::Int8, T::Int32),
            (T::UInt16, T::UInt32),
            (T::Int32, T::Int64),
            (T::UInt8, T::UInt64),
            (T::Int32, T::UInt32),
        ] {
            let variable = Variable(994101);
            let native = MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: source,
                to: destination,
                value: Box::new(MachineTerm::Variable(variable)),
            };
            let root = KernelTermImport::default()
                .machine_arithmetic(destination, &native)
                .unwrap();
            let exports = KernelTermExport::machine_export_count();
            let read = MachineOperandView::Shared(&root).narrow_widening32_operand();
            assert_eq!(
                read.map(|(ty, _)| ty),
                native.narrow_widening32_operand().map(|(ty, _)| ty)
            );
            if let Some((_, value)) = read {
                assert_eq!(value.variable(), Some(&variable));
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        use super::*;
        include!(
            "../../scaling_tests/kernel/primitives/term_operations/format_range_premise_tests.rs"
        );
    }
}
