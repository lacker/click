//! Width and numeric interpretation of fixed-width integer constants.
//!
//! These are representation values, not execution certificates. A format may
//! describe 128 bits before a frontend or symbolic runtime supports that width.
//! Checked conversions preserve the numeric value; modulo conversions are an
//! explicit, separate policy for languages that specify them.

use super::{MachineIntegerType, MachineTerm, ProgramValue};
use crate::kernel::MachineCastSpelling;
use crate::kernel::machine_integer::format_audit::{self, WordIdentity};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint32_constant, uint64_constant,
};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// Closed set of supported representation widths. No zero or oversized shifts
/// can be introduced through a caller-supplied numeric width.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MachineIntegerWidth {
    Bits8,
    Bits16,
    Bits32,
    Bits64,
    Bits128,
}

impl MachineIntegerWidth {
    pub const fn bits(self) -> u32 {
        match self {
            Self::Bits8 => 8,
            Self::Bits16 => 16,
            Self::Bits32 => 32,
            Self::Bits64 => 64,
            Self::Bits128 => 128,
        }
    }
}

/// A value format, independent of source spelling, ABI alignment, and the
/// widths currently admitted by a frontend or the symbolic execution model.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MachineIntegerFormat {
    width: MachineIntegerWidth,
    signed: bool,
}

impl MachineIntegerFormat {
    /// Whether every source value is representable without changing its
    /// numeric interpretation. This is a width/signedness check, not a walk.
    pub const fn contains(self, source: Self) -> bool {
        if self.signed {
            if source.signed {
                self.bits() >= source.bits()
            } else {
                self.bits() > source.bits()
            }
        } else {
            !source.signed && self.bits() >= source.bits()
        }
    }

    pub const fn new(width: MachineIntegerWidth, signed: bool) -> Self {
        Self { width, signed }
    }

    pub const fn width(self) -> MachineIntegerWidth {
        self.width
    }

    pub const fn bits(self) -> u32 {
        self.width.bits()
    }

    pub const fn byte_width(self) -> u32 {
        self.bits() / 8
    }

    pub const fn is_signed(self) -> bool {
        self.signed
    }

    pub(crate) const fn mask(self) -> u128 {
        if self.bits() == 128 {
            u128::MAX
        } else {
            (1u128 << self.bits()) - 1
        }
    }

    /// Inclusive exact numeric bounds. The largest allocation is 128 bits;
    /// arithmetic work is charged before constructing either BigInt.
    pub fn bounds(self) -> (BigInt, BigInt) {
        crate::instrumentation::record_deterministic_work(self.bits() as usize * 2);
        if self.signed {
            let upper = (self.mask() >> 1) as i128;
            (BigInt::from(-upper - 1), BigInt::from(upper))
        } else {
            (BigInt::from(0), BigInt::from(self.mask()))
        }
    }
}

/// A constant with a checked format and at most that format's number of bits.
/// Fields are private so malformed payload/width pairs cannot enter a consumer.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MachineIntegerConstant {
    format: MachineIntegerFormat,
    bits: u128,
}

/// Failure of truncating division in one already-resolved machine format.
/// This does not select a source language's promotion or panic/UB policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MachineIntegerDivisionError {
    FormatMismatch,
    DivisionByZero,
    SignedOverflow,
}

impl MachineIntegerConstant {
    /// Interpret an explicitly supplied representation, without truncation.
    pub fn from_bits(format: MachineIntegerFormat, bits: u128) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        (bits <= format.mask()).then_some(Self { format, bits })
    }

    pub fn from_signed(format: MachineIntegerFormat, value: i128) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        if !format.signed {
            return Self::from_unsigned(format, u128::try_from(value).ok()?);
        }
        let upper = (format.mask() >> 1) as i128;
        if value < -upper - 1 || value > upper {
            return None;
        }
        Some(Self {
            format,
            bits: (value as u128) & format.mask(),
        })
    }

    pub fn from_unsigned(format: MachineIntegerFormat, value: u128) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        let upper = if format.signed {
            format.mask() >> 1
        } else {
            format.mask()
        };
        (value <= upper).then_some(Self {
            format,
            bits: value,
        })
    }

    /// Checked numeric conversion from an exact Integer. Huge numerals are
    /// refused by their cached bit length, before inspecting their limbs.
    pub fn from_integer(format: MachineIntegerFormat, value: &BigInt) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        if value.bits() > u64::from(format.bits()) {
            return None;
        }
        if format.signed {
            Self::from_signed(format, value.to_i128()?)
        } else {
            Self::from_unsigned(format, value.to_u128()?)
        }
    }

    /// Decimal spelling of a numeric value; parsing never wraps or reinterprets
    /// an out-of-range literal. Work is proportional to the explicit spelling.
    pub fn parse_decimal(format: MachineIntegerFormat, value: &str) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(value.len().saturating_add(1));
        if format.signed {
            Self::from_signed(format, value.parse().ok()?)
        } else {
            Self::from_unsigned(format, value.parse().ok()?)
        }
    }

    pub const fn format(self) -> MachineIntegerFormat {
        self.format
    }

    /// The constant a term's [`MachineTerm::Constant`] node names,
    /// whose bits its builders already checked. Charges no work: reading the
    /// node's fields does not.
    pub(crate) const fn from_term_bits(format: MachineIntegerFormat, bits: u128) -> Self {
        debug_assert!(bits <= format.mask());
        Self { format, bits }
    }

    pub const fn bits(self) -> u128 {
        self.bits
    }

    /// Quotient truncated toward zero and remainder with the dividend's sign.
    /// Both results retain the exact operand format. Signed MIN / -1 and
    /// MIN % -1 fail together, even though the mathematical remainder is zero.
    /// Source promotions must happen before calling this representation API.
    pub fn truncating_div_rem(
        self,
        divisor: Self,
    ) -> Result<(Self, Self), MachineIntegerDivisionError> {
        use MachineIntegerDivisionError::*;
        crate::instrumentation::record_deterministic_work(1);
        if self.format != divisor.format {
            return Err(FormatMismatch);
        }
        if divisor.bits == 0 {
            return Err(DivisionByZero);
        }
        if self.format.signed {
            let left = self.signed_value();
            let right = divisor.signed_value();
            let quotient = left.checked_div(right).ok_or(SignedOverflow)?;
            // A host i128 quotient can still overflow a narrower format.
            let quotient = Self::from_signed(self.format, quotient).ok_or(SignedOverflow)?;
            let remainder =
                Self::from_signed(self.format, left.checked_rem(right).ok_or(SignedOverflow)?)
                    .expect("a defined truncating remainder fits its operand format");
            Ok((quotient, remainder))
        } else {
            Ok((
                Self {
                    format: self.format,
                    bits: self.bits / divisor.bits,
                },
                Self {
                    format: self.format,
                    bits: self.bits % divisor.bits,
                },
            ))
        }
    }

    fn signed_value(self) -> i128 {
        if self.format.bits() == 128 {
            self.bits as i128
        } else {
            let shift = 128 - self.format.bits();
            ((self.bits << shift) as i128) >> shift
        }
    }

    pub fn to_i128(self) -> Option<i128> {
        if self.format.signed {
            Some(self.signed_value())
        } else {
            i128::try_from(self.bits).ok()
        }
    }

    pub fn to_u128(self) -> Option<u128> {
        if self.format.signed {
            u128::try_from(self.signed_value()).ok()
        } else {
            Some(self.bits)
        }
    }

    pub fn to_integer(self) -> BigInt {
        crate::instrumentation::record_deterministic_work(self.format.bits() as usize);
        if self.format.signed {
            BigInt::from(self.signed_value())
        } else {
            BigInt::from(self.bits)
        }
    }

    /// Preserve the numeric value, including signedness changes, or refuse.
    pub fn checked_convert(self, destination: MachineIntegerFormat) -> Option<Self> {
        if self.format.signed {
            Self::from_signed(destination, self.signed_value())
        } else {
            Self::from_unsigned(destination, self.bits)
        }
    }

    /// Explicit congruence modulo 2^destination-width. This policy implements
    /// Rust integer `as` and C++20 integral conversions; it must not silently
    /// choose the implementation-defined signed narrowing policy of C.
    pub fn convert_modulo(self, destination: MachineIntegerFormat) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let extended = if self.format.signed {
            self.signed_value() as u128
        } else {
            self.bits
        };
        Self {
            format: destination,
            bits: extended & destination.mask(),
        }
    }
}

impl MachineIntegerType {
    /// The byte width of the word a value of this type rides in: 4 for 8 to
    /// 32 bits, whose values ride in the 32-bit word, 8 for 64 bits and 16
    /// for 128.
    pub(crate) const fn carrier_bytes(self) -> u32 {
        match self {
            Self::Int8 | Self::UInt8 | Self::Int16 | Self::UInt16 | Self::Int32 | Self::UInt32 => 4,
            Self::Int64 | Self::UInt64 => 8,
            Self::Int128 | Self::UInt128 => 16,
        }
    }

    /// The Click name of the type.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Int8 => "int8",
            Self::UInt8 => "uint8",
            Self::Int16 => "int16",
            Self::UInt16 => "uint16",
            Self::Int32 => "int32",
            Self::UInt32 => "uint32",
            Self::Int64 => "int64",
            Self::UInt64 => "uint64",
            Self::Int128 => "int128",
            Self::UInt128 => "uint128",
        }
    }

    /// The type of `format`, the inverse of [`Self::format`].
    pub const fn of_format(format: MachineIntegerFormat) -> Self {
        use MachineIntegerWidth::*;
        match (format.width(), format.is_signed()) {
            (Bits8, true) => Self::Int8,
            (Bits8, false) => Self::UInt8,
            (Bits16, true) => Self::Int16,
            (Bits16, false) => Self::UInt16,
            (Bits32, true) => Self::Int32,
            (Bits32, false) => Self::UInt32,
            (Bits64, true) => Self::Int64,
            (Bits64, false) => Self::UInt64,
            (Bits128, true) => Self::Int128,
            (Bits128, false) => Self::UInt128,
        }
    }

    pub const fn format(self) -> MachineIntegerFormat {
        use MachineIntegerWidth::*;
        let (width, signed) = match self {
            Self::Int8 => (Bits8, true),
            Self::UInt8 => (Bits8, false),
            Self::Int16 => (Bits16, true),
            Self::UInt16 => (Bits16, false),
            Self::Int32 => (Bits32, true),
            Self::UInt32 => (Bits32, false),
            Self::Int64 => (Bits64, true),
            Self::UInt64 => (Bits64, false),
            Self::Int128 => (Bits128, true),
            Self::UInt128 => (Bits128, false),
        };
        MachineIntegerFormat::new(width, signed)
    }

    /// The constant term of `value` at this format: an 8- or 16-bit value's
    /// own native constant, a 32- or 64-bit word, or a 128-bit constant.
    pub(crate) fn constant_term(self, value: MachineIntegerConstant) -> Option<MachineTerm> {
        if value.format != self.format() {
            return None;
        }
        Some(match self {
            Self::Int8 | Self::UInt8 | Self::Int16 | Self::UInt16 => {
                MachineTerm::machine_constant(value)
            }
            Self::Int32 => MachineTerm::constant(value.to_i128()? as u32),
            Self::UInt32 => MachineTerm::uint32_constant(value.to_u128()? as u32),
            Self::Int64 => MachineTerm::int64_constant(value.to_i128()? as i64),
            Self::UInt64 => MachineTerm::uint64_constant(value.to_u128()? as u64),
            Self::Int128 | Self::UInt128 => MachineTerm::machine_constant(value),
        })
    }

    /// Root validation for the bounded wide runtime profile. The term arena
    /// is shared, but its legacy arithmetic nodes must not acquire a wide
    /// interpretation merely by changing a value wrapper.
    pub(crate) fn accepts_wide_term(self, value: &MachineTerm) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if self.format().bits() != 128 {
            return false;
        }
        match value {
            MachineTerm::Constant { format, .. } => *format == self,
            MachineTerm::Variable(_) => true,
            MachineTerm::MemoryLoad(_, _, kind) => {
                crate::kernel::LoadKind::of_type(self.program_type()) == Some(*kind)
            }
            MachineTerm::IntegerToMachine { destination, .. } => *destination == self,
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } => *destination == self && source.accepts_cast_operand(value),
            _ => false,
        }
    }

    pub(in crate::kernel) fn accepts_cast_operand(self, value: &MachineTerm) -> bool {
        let (mut ty, mut value) = (self, value);
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match value {
                MachineTerm::Constant { .. } => {
                    return ty.constant_from_term(value).is_some();
                }
                MachineTerm::Variable(_) => return true,
                MachineTerm::MemoryLoad(_, _, kind) if ty.format().bits() == 128 => {
                    return crate::kernel::LoadKind::of_type(ty.program_type()) == Some(*kind);
                }
                MachineTerm::IntegerToMachine { destination, .. } => return *destination == ty,
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: operand,
                    from: source,
                    to: destination,
                } => {
                    if *destination != ty {
                        return false;
                    }
                    // Observation unwraps only strictly widening conversions.
                    // Validate that same bounded chain; equal-width and narrowing
                    // nodes stay typed and opaque. There are only five widths.
                    if ty.format().bits() > source.format().bits()
                        && ty.format().contains(source.format())
                    {
                        ty = *source;
                        value = operand;
                    } else {
                        return true;
                    }
                }
                _ => return ty.format().bits() != 128,
            }
        }
    }

    pub(crate) fn constant_value(self, value: MachineIntegerConstant) -> Option<ProgramValue> {
        Some(self.value_from_term(self.constant_term(value)?))
    }

    pub(crate) fn value_from_term(self, term: MachineTerm) -> ProgramValue {
        let term = term.in_format32(self).in_narrow_format(self);
        match self {
            Self::Int8 => ProgramValue::Int8(term),
            Self::UInt8 => ProgramValue::UInt8(term),
            Self::Int16 => ProgramValue::Int16(term),
            Self::UInt16 => ProgramValue::UInt16(term),
            Self::Int32 => ProgramValue::Int32(term),
            Self::UInt32 => ProgramValue::UInt32(term),
            Self::Int64 => ProgramValue::Int64(term),
            Self::UInt64 => ProgramValue::UInt64(term),
            Self::Int128 => ProgramValue::Int128(term),
            Self::UInt128 => ProgramValue::UInt128(term),
        }
    }

    pub(crate) fn constant_from_term(self, value: &MachineTerm) -> Option<MachineIntegerConstant> {
        match (self, value) {
            (
                Self::Int8
                | Self::UInt8
                | Self::Int16
                | Self::UInt16
                | Self::Int128
                | Self::UInt128,
                native_constant!(format, bits),
            ) if *format == self => {
                Some(MachineIntegerConstant::from_term_bits(self.format(), *bits))
            }
            (Self::Int32, bits32_constant!(value)) => MachineIntegerConstant::from_signed(
                self.format(),
                i128::from(constant_u32(*value) as i32),
            ),
            (Self::UInt32, bits32_constant!(value)) => MachineIntegerConstant::from_unsigned(
                self.format(),
                u128::from(constant_u32(*value)),
            ),
            (Self::Int64, int64_constant!(value)) => {
                MachineIntegerConstant::from_signed(self.format(), i128::from(constant_i64(*value)))
            }
            (Self::UInt64, uint64_constant!(value)) => MachineIntegerConstant::from_unsigned(
                self.format(),
                u128::from(constant_u64(*value)),
            ),
            _ => None,
        }
    }

    pub(crate) fn constant_from_value(
        self,
        value: &ProgramValue,
    ) -> Option<MachineIntegerConstant> {
        if value.program_type() != self.program_type() {
            return None;
        }
        let term = match value {
            crate::kernel::integer_c_value!(term) => term,
            _ => return None,
        };
        self.constant_from_term(term)
    }
}

impl MachineTerm {
    /// Construct the exact read of `kind` at `pointer` in `memory`. The
    /// supplied memory is retained unchanged: this does not select a version
    /// point, publish an observation, or look up a stored value. Comparison
    /// identity selection and legacy selected-version retention live in
    /// `eval::memory_loads`, separately from this descriptor constructor.
    ///
    /// Every read is its own load at its own type (maintainer direction,
    /// 2026-10-30): the `int8` and `uint8` reads of one byte are two loads,
    /// neither a conversion of the other, related by the 8-bit sign cast
    /// when they read the same byte (R-mem).
    pub(crate) fn memory_read(
        memory: crate::kernel::SharedMemory,
        pointer: crate::kernel::Pointer,
        kind: crate::kernel::LoadKind,
    ) -> Self {
        Self::MemoryLoad(memory, Box::new(pointer), kind)
    }

    /// The `signed char` value of the byte whose `unsigned char` value is
    /// `unsigned`: its eight bits read in two's complement.
    pub(crate) fn signed_byte(unsigned: Self) -> Self {
        Self::machine_integer_cast(
            MachineIntegerType::UInt8,
            MachineIntegerType::Int8,
            unsigned,
        )
    }

    /// The 32-bit sign cast σ: `value`, an `int32` or `uint32` term, read at
    /// the other one of the two. It folds a constant (`machine_integer_cast`)
    /// and keeps σ of σ as written; R0 relates σ(σ(x)) to `x` in the
    /// e-graph. Every C conversion
    /// between `int` and `unsigned int` builds it
    /// (`design/machine-integers.md`, "Decisions", 2026-10-25).
    pub(crate) fn sign_cast32(
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: Self,
    ) -> Self {
        debug_assert!(is_sign_cast32(source, destination));
        Self::machine_integer_cast(source, destination, value)
    }

    /// The source format and operand of a 32-bit widening of an 8- or
    /// 16-bit value, if this term is one: a node of its own, whose word is
    /// its operand's (rule K8, a relation). One match on the root.
    pub(crate) fn narrow_widening32_operand(&self) -> Option<(MachineIntegerType, &Self)> {
        match self {
            Self::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } if is_narrow_widening32(*source, *destination) => Some((*source, value)),
            _ => None,
        }
    }

    /// The term whose 32 bits this term's are, read through one σ: σ(x)'s
    /// operand `x`, every other term itself. A 32-bit equality compares
    /// bits, so its fact identity and keys read each side through this
    /// (rule K6, a lookup-level equivalence); terms keep their σ. One match
    /// on the root.
    pub(crate) fn sign_cast32_bits(&self) -> &Self {
        self.sign_cast32_operand()
            .map_or(self, |(_, operand)| operand)
    }

    /// Whether the 32-bit equality `self == other` reads as `x == x` under
    /// rule K6: σ(x) and x, in either order, are the same bits. Such an
    /// equality is true of every `x` and names no rewrite: replacing x by
    /// σ(x) only stacks casts. A root without a σ costs one match on each
    /// side; a σ root compares its operand with the other side.
    pub(crate) fn is_sign_cast32_of(&self, other: &Self) -> bool {
        self.sign_cast32_operand()
            .is_some_and(|(_, operand)| operand == other)
            || other
                .sign_cast32_operand()
                .is_some_and(|(_, operand)| operand == self)
    }

    /// The source format and operand of a σ, if this term is one. One
    /// match on the root.
    pub(crate) fn sign_cast32_operand(&self) -> Option<(MachineIntegerType, &Self)> {
        match self {
            Self::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } if is_sign_cast32(*source, *destination) => Some((*source, value)),
            _ => None,
        }
    }

    /// The bits of a root 32-bit constant of either format.
    pub(crate) fn constant32(&self) -> Option<u32> {
        match self {
            bits32_constant!(value) => Some(constant_u32(*value)),
            _ => None,
        }
    }

    /// A `uint32` constant as its word's `Constant` (rule K1); every other
    /// term unchanged. The raw 32-bit operator builders apply it to their
    /// operands, so an operator never holds a formatted constant.
    #[track_caller]
    pub(crate) fn constant_word32(self) -> Self {
        match self {
            uint32_constant!(value) => {
                format_audit::record(
                    WordIdentity::UInt32ConstantPeeled,
                    std::panic::Location::caller(),
                );
                Self::constant(constant_u32(value))
            }
            term => term,
        }
    }

    /// `self` as a value of `ty`: a root 32-bit constant takes `ty`'s
    /// format, `uint32` at `uint32` and `int32` at every other
    /// format. Both name one word (rule K1), so this changes no meaning;
    /// it lets a `uint32` constant print as itself. One match on the root.
    pub(crate) fn in_format32(self, ty: MachineIntegerType) -> Self {
        match (ty, self) {
            (MachineIntegerType::UInt32, int32_constant!(value)) => {
                Self::uint32_constant(constant_u32(value))
            }
            (MachineIntegerType::UInt32, term) => term,
            (_, uint32_constant!(value)) => Self::constant(constant_u32(value)),
            (_, term) => term,
        }
    }

    /// `self` as a value of `ty`: at an 8- or 16-bit `ty`, a 32-bit constant
    /// is read as the word of a `ty` value, its sign or zero extension, and
    /// becomes that value's own constant; every other term is unchanged. One
    /// match on the root.
    pub(crate) fn in_narrow_format(self, ty: MachineIntegerType) -> Self {
        match self {
            bits32_constant!(word) if ty.format().bits() < 32 => {
                debug_assert!(
                    ty.constant_from_term(&Self::narrow_constant(
                        ty,
                        u128::from(constant_u32(word))
                    ))
                    .is_some_and(|value| {
                        value.to_i128().is_some_and(|value| {
                            if ty.format().is_signed() {
                                value == i128::from(constant_u32(word) as i32)
                            } else {
                                value == i128::from(constant_u32(word))
                            }
                        })
                    }),
                    "{word:#x} is not the word of a {ty:?} value",
                    word = constant_u32(word)
                );
                Self::narrow_constant(ty, u128::from(constant_u32(word)))
            }
            term => term,
        }
    }

    /// A `uint32` constant as its word's `Constant`; every other term,
    /// σ included, unchanged. The signed 32-bit operator, comparison and
    /// overflow constructors read their operands through it. σ is a node of
    /// its own ("Every format its own nodes", step 4b); a 32-bit constant
    /// keeps one spelling per format until constants carry their format
    /// (decision G9). One match on the root.
    #[track_caller]
    pub(crate) fn into_word32(self) -> Self {
        self.constant_word32()
    }

    /// The word an element index names in `int32` index coordinates: σ is
    /// peeled, so a sign-cleared `unsigned` index's σ to `int32` indexes by
    /// its word, and a `uint32` constant is its word's `Constant`. Index
    /// coordinates stay words, the address-only exception decision G1 names
    /// (`design/machine-integers.md`); everywhere else σ is a node of its
    /// own. One match on the root.
    #[track_caller]
    pub(crate) fn into_index_word32(self) -> Self {
        match self {
            Self::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } if is_sign_cast32(source, destination) => {
                format_audit::record(WordIdentity::SignCastPeeled, std::panic::Location::caller());
                *value
            }
            term => term.constant_word32(),
        }
    }

    /// The unsigned byte a [`Self::signed_byte`] term converts, if this is one.
    pub(crate) fn signed_byte_operand(&self) -> Option<&Self> {
        match self {
            Self::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: MachineIntegerType::UInt8,
                to: MachineIntegerType::Int8,
            } => Some(value),
            _ => None,
        }
    }

    /// Fold only a constant at the operand root. Symbolic conversion records
    /// both formats, and construction does not scan or clone the operand tree.
    pub(crate) fn machine_integer_cast(
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: Self,
    ) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        if source == destination {
            return value;
        }
        if let Some(constant) = source.constant_from_term(&value) {
            return destination
                .constant_term(constant.convert_modulo(destination.format()))
                .expect("matching destination format");
        }
        // A 32-to-64-bit extension has one spelling, the typed extension
        // node lowering builds; a generic node would be a second term for
        // the same conversion.
        if crate::kernel::machine_integer::conversion::extension_encoding(source, destination)
            .is_some()
        {
            return crate::kernel::machine_integer::conversion::convert_term(
                source,
                destination,
                value,
            );
        }
        // The established 32-bit word rules identify chains of narrow
        // conversions. Keep that representation convention local to the
        // word carrier; it must not erase a wide intermediate cast. σ of σ
        // is kept as written: R0 relates σ(σ(x)) to `x` in the e-graph.
        if let Self::Cast {
            spelling: MachineCastSpelling::Generic,
            from: original,
            to: intermediate,
            value: operand,
        } = value
        {
            if original.carrier_bytes() == 4
                && source.carrier_bytes() == 4
                && destination.carrier_bytes() == 4
                && intermediate == source
                && destination.format().bits() <= intermediate.format().bits()
                && !(original == destination && is_sign_cast32(original, intermediate))
            {
                return Self::machine_integer_cast(original, destination, *operand);
            }
            return Self::Cast {
                spelling: MachineCastSpelling::Generic,
                value: Box::new(Self::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: operand,
                    from: original,
                    to: intermediate,
                }),
                from: source,
                to: destination,
            };
        }
        // Keep symbolic cast composition structural; a 32-to-64-bit
        // extension was given its typed node above.
        Self::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(value),
            from: source,
            to: destination,
        }
    }
}

/// Whether a conversion from `source` to `destination` widens an 8- or
/// 16-bit value into `int32` or `uint32`. Where the widening is a node (a
/// value at rest; the constructors still peel it inside an operator,
/// comparison or observation until K8's peel goes), the equality graph and
/// the difference graph relate it to its operand's word (rule K8, a
/// relation: the operand's word is the canonical carrier of its value, the
/// Stage 0 invariant). One comparison.
pub(crate) fn is_narrow_widening32(
    source: MachineIntegerType,
    destination: MachineIntegerType,
) -> bool {
    source.format().bits() < 32 && destination.format().bits() == 32
}

/// Whether a conversion from `source` to `destination` is the 32-bit sign
/// cast σ: `int32` to `uint32` or back, which keeps every bit.
pub(crate) fn is_sign_cast32(source: MachineIntegerType, destination: MachineIntegerType) -> bool {
    matches!(
        (source, destination),
        (MachineIntegerType::Int32, MachineIntegerType::UInt32)
            | (MachineIntegerType::UInt32, MachineIntegerType::Int32)
    )
}

#[cfg(test)]
mod tests {

    use super::*;

    /// A 32-to-64-bit extension is built as the typed node C lowering
    /// builds, whichever constructor builds it, and rule W reads the
    /// value-preserving ones as their operand; `UInt64FromInt32` keeps no
    /// value of a negative operand and is not read through.
    #[test]
    fn a_32_to_64_bit_extension_has_one_spelling_and_its_value_reading() {
        use crate::kernel::{IntegerTerm, Variable};
        use MachineIntegerType as M;
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(149_101));
        for (source, destination, preserving) in [
            (M::Int32, M::Int64, true),
            (M::UInt32, M::Int64, true),
            (M::UInt32, M::UInt64, true),
            (M::Int32, M::UInt64, false),
        ] {
            let lowered = crate::kernel::machine_integer::conversion::convert_term(
                source,
                destination,
                x.clone(),
            );
            assert!(!matches!(
                lowered,
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    ..
                }
            ));
            assert_eq!(
                MachineTerm::machine_integer_cast(source, destination, x.clone()),
                lowered
            );
            let operand = IntegerTerm::from_machine(source, x.clone()).unwrap();
            let IntegerTerm::Machine(machine) = &operand else {
                unreachable!()
            };
            let widened = machine.cast_operand(destination);
            assert_eq!(widened.value(), &lowered);
            let observed = IntegerTerm::from_machine(destination, lowered).unwrap();
            assert_eq!(
                observed.value_read() == operand.value_read(),
                preserving,
                "{source:?} -> {destination:?}"
            );
        }
    }

    /// A constant is one node at every format (decision G9) and debug-prints
    /// as the per-format variant it replaced, so diagnostics that print a
    /// term with `{:?}` are unchanged.
    #[test]
    fn a_formatted_constant_debug_prints_its_former_variant() {
        use MachineIntegerType as M;
        let wide = MachineIntegerConstant::from_signed(M::Int8.format(), -56).unwrap();
        for (term, spelling) in [
            (MachineTerm::constant(u32::MAX), "Constant(4294967295)"),
            (MachineTerm::uint32_constant(3), "UInt32Constant(3)"),
            (MachineTerm::int64_constant(-1), "Int64Constant(-1)"),
            (
                MachineTerm::uint64_constant(u64::MAX),
                "UInt64Constant(18446744073709551615)",
            ),
            (
                MachineTerm::machine_constant(wide),
                "MachineIntegerConstant(MachineIntegerConstant { format: MachineIntegerFormat { width: Bits8, signed: true }, bits: 200 })",
            ),
        ] {
            assert_eq!(format!("{term:?}"), spelling);
        }
        assert_eq!(
            MachineTerm::int64_constant(-1),
            MachineTerm::Constant {
                format: M::Int64,
                bits: u128::from(u64::MAX)
            }
        );
        assert_eq!(
            MachineTerm::machine_constant(wide).as_machine_constant(),
            Some(wide)
        );
    }

    /// Per format: a 32-bit constant at rest takes the `uint32` format at
    /// `uint32` and `int32` everywhere else (`in_format32`,
    /// `constant_term`), conversions between `int32` and `uint32` fold a
    /// constant to the other format, and the word of either is the `int32`
    /// constant.
    #[test]
    fn a_32_bit_constant_takes_its_value_s_format() {
        use MachineIntegerType as M;
        for bits in [0u32, 1, 0x7FFF_FFFF, 0x8000_0000, 4_000_000_000, u32::MAX] {
            let word = MachineTerm::constant(bits);
            let formatted = MachineTerm::uint32_constant(bits);
            assert_eq!(word.clone().in_format32(M::UInt32), formatted);
            assert_eq!(formatted.clone().in_format32(M::UInt32), formatted);
            for ty in [M::Int8, M::Int16, M::Int32, M::UInt8, M::UInt16, M::Int64] {
                assert_eq!(formatted.clone().in_format32(ty), word, "{ty:?}");
                assert_eq!(word.clone().in_format32(ty), word, "{ty:?}");
            }
            assert_eq!(formatted.clone().into_word32(), word);
            assert_eq!(formatted.constant32(), Some(bits));
            assert_eq!(formatted.as_const(), Some(bits));
            let unsigned = M::UInt32.constant_from_term(&formatted).unwrap();
            assert_eq!(M::UInt32.constant_term(unsigned), Some(formatted.clone()));
            assert_eq!(M::UInt32.constant_from_term(&word), Some(unsigned));
            let signed = M::Int32.constant_from_term(&word).unwrap();
            assert_eq!(M::Int32.constant_term(signed), Some(word.clone()));
            assert_eq!(
                MachineTerm::sign_cast32(M::Int32, M::UInt32, word.clone()),
                formatted
            );
            assert_eq!(
                MachineTerm::sign_cast32(M::UInt32, M::Int32, formatted.clone()),
                word
            );
            assert_eq!(
                MachineTerm::add(formatted.clone(), MachineTerm::constant(1)),
                MachineTerm::constant(bits.wrapping_add(1))
            );
            assert_eq!(
                M::UInt32.value_from_term(word.clone()),
                ProgramValue::UInt32(formatted.clone())
            );
            assert_eq!(
                M::Int32.value_from_term(formatted.clone()),
                ProgramValue::Int32(word.clone())
            );
        }
        // A narrow constant is a native constant of its own width, and a
        // 32-bit word is not one.
        let native = MachineTerm::narrow_constant(M::UInt8, 200);
        let byte = M::UInt8.constant_from_term(&native).unwrap();
        assert_eq!(M::UInt8.constant_term(byte), Some(native));
        assert_eq!(
            M::UInt8.constant_from_term(&MachineTerm::constant(200)),
            None
        );
    }

    #[test]
    fn wide_cast_symbolic_and_constant_conversions_match_independent_exact_oracle() {
        use crate::kernel::Variable;
        use crate::kernel::reasoning::substitute_bitvector_variable_in_program_value;
        use MachineIntegerType::*;
        let types = [
            Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, UInt128,
        ];
        let variable = Variable(149_001);
        for source in types {
            let (min, max) = source.format().bounds();
            let mut samples = vec![
                min.clone(),
                &min + 1,
                &max - 1,
                max.clone(),
                0.into(),
                1.into(),
            ];
            if source.format().is_signed() {
                samples.push((-1).into());
            }
            for bit in [7, 15, 31, 63, 64, 100, 126, 127] {
                for delta in [-1, 0, 1] {
                    let value: BigInt = (BigInt::from(1) << bit) + delta;
                    for value in [value.clone(), -value] {
                        if value >= min && value <= max {
                            samples.push(value);
                        }
                    }
                }
            }
            for destination in types {
                if source.format().bits() != 128 && destination.format().bits() != 128 {
                    continue;
                }
                let symbolic = crate::kernel::machine_integer::conversion::convert_value(
                    source.value_from_term(MachineTerm::Variable(variable)),
                    destination,
                )
                .unwrap();
                for integer in &samples {
                    let input =
                        MachineIntegerConstant::from_integer(source.format(), integer).unwrap();
                    let actual = substitute_bitvector_variable_in_program_value(
                        &symbolic,
                        variable,
                        &source.constant_term(input).unwrap(),
                    );
                    let literal = crate::kernel::machine_integer::conversion::convert_value(
                        source.constant_value(input).unwrap(),
                        destination,
                    )
                    .unwrap();
                    let modulus = BigInt::from(1) << destination.format().bits();
                    let mut expected = ((integer % &modulus) + &modulus) % &modulus;
                    if destination.format().is_signed() && expected >= (&modulus >> 1) {
                        expected -= &modulus;
                    }
                    assert_eq!(
                        destination
                            .constant_from_value(&actual)
                            .unwrap()
                            .to_integer(),
                        expected,
                        "{source:?}->{destination:?}: {integer}"
                    );
                    assert_eq!(actual, literal);
                }
            }
        }
    }

    #[test]
    fn nested_modulo_casts_match_an_independent_oracle_and_preserve_widening_sign() {
        use crate::kernel::Variable;
        use crate::kernel::reasoning::substitute_bitvector_variable_in_program_value;
        use MachineIntegerType::*;
        let types = [Int8, UInt8, Int32, UInt32, Int64, UInt64, Int128, UInt128];
        let variable = Variable(149_003);
        let modulo = |value: &BigInt, ty: MachineIntegerType| {
            let modulus = BigInt::from(1) << ty.format().bits();
            let mut result = ((value % &modulus) + &modulus) % &modulus;
            if ty.format().is_signed() && result >= (&modulus >> 1) {
                result -= modulus;
            }
            result
        };
        for source in types {
            let (min, max) = source.format().bounds();
            for intermediate in types {
                for destination in types {
                    let inner = MachineTerm::machine_integer_cast(
                        source,
                        intermediate,
                        MachineTerm::Variable(variable),
                    );
                    let term = MachineTerm::machine_integer_cast(intermediate, destination, inner);
                    let extension = |from, to| {
                        crate::kernel::machine_integer::conversion::extension_encoding(from, to)
                            .is_some()
                    };
                    // A 32-to-64-bit extension is its typed node instead.
                    if source != intermediate
                        && intermediate != destination
                        && !extension(source, intermediate)
                        && !extension(intermediate, destination)
                        && (source.carrier_bytes() > 4
                            || intermediate.carrier_bytes() > 4
                            || destination.carrier_bytes() > 4)
                    {
                        assert!(
                            matches!(&term, MachineTerm::Cast { spelling: MachineCastSpelling::Generic,
                            value, from: outer_source, to: outer_destination,
                        } if *outer_source == intermediate && *outer_destination == destination
                            && matches!(value.as_ref(), MachineTerm::Cast { spelling: MachineCastSpelling::Generic, .. }))
                        );
                    }
                    for input in [min.clone(), max.clone(), 0.into(), 1.into()] {
                        let constant =
                            MachineIntegerConstant::from_integer(source.format(), &input).unwrap();
                        let value = destination.value_from_term(term.clone());
                        let result = substitute_bitvector_variable_in_program_value(
                            &value,
                            variable,
                            &source.constant_term(constant).unwrap(),
                        );
                        let expected = modulo(&modulo(&input, intermediate), destination);
                        assert_eq!(
                            destination
                                .constant_from_value(&result)
                                .unwrap()
                                .to_integer(),
                            expected,
                            "{source:?}->{intermediate:?}->{destination:?}: {input}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn wide_cast_value_preserving_format_checks_match_exact_bounds() {
        for destination in formats() {
            for source in formats() {
                let (source_min, source_max) = source.bounds();
                let (dest_min, dest_max) = destination.bounds();
                assert_eq!(
                    destination.contains(source),
                    dest_min <= source_min && source_max <= dest_max
                );
            }
        }
    }

    #[test]
    fn symbolic_modulo_conversions_match_exact_numeric_oracle_after_substitution() {
        use crate::kernel::reasoning::substitute_bitvector_variable_in_term;
        use crate::kernel::{Term, Variable};
        let types = [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ];
        let variable = Variable(138_001);
        for source in types {
            let format = source.format();
            let (min, max) = format.bounds();
            let mut samples = vec![
                min.clone(),
                min + 1,
                max.clone() - 1,
                max,
                BigInt::from(0),
                BigInt::from(1),
            ];
            if format.is_signed() {
                samples.push(BigInt::from(-1));
            }
            if format.bits() == 8 {
                samples.extend((0..=255).map(|bits| {
                    if format.is_signed() {
                        BigInt::from(bits as u8 as i8)
                    } else {
                        BigInt::from(bits)
                    }
                }));
            }
            for destination in types {
                let symbolic = crate::kernel::machine_integer::conversion::convert_value(
                    source.value_from_term(MachineTerm::Variable(variable)),
                    destination,
                )
                .unwrap();
                assert_eq!(symbolic.program_type(), destination.program_type());
                for integer in &samples {
                    let constant = MachineIntegerConstant::from_integer(format, integer).unwrap();
                    let substituted = substitute_bitvector_variable_in_term(
                        &Term::ProgramValue(symbolic.clone()),
                        variable,
                        &source.constant_term(constant).unwrap(),
                    );
                    let Term::ProgramValue(actual) = substituted else {
                        unreachable!()
                    };
                    let modulus = BigInt::from(1u8) << destination.format().bits();
                    let mut expected = ((integer % &modulus) + &modulus) % &modulus;
                    if destination.format().is_signed() && expected >= (&modulus >> 1) {
                        expected -= &modulus;
                    }
                    let term = match actual {
                        crate::kernel::integer64_c_value!(t) => t,
                        _ => unreachable!(),
                    };
                    let observed = match (
                        destination.format().bits(),
                        destination.format().is_signed(),
                    ) {
                        (64, true) => term.int64_as_const().map(BigInt::from),
                        (64, false) => term.uint64_as_const().map(BigInt::from),
                        // An 8- or 16-bit result is a native constant.
                        (8 | 16, _) => term.narrow_constant_bits(destination).map(|bits| {
                            MachineIntegerConstant::from_bits(destination.format(), bits)
                                .unwrap()
                                .to_integer()
                        }),
                        (_, true) => term.as_const().map(|bits| BigInt::from(bits as i32)),
                        (_, false) => term.as_const().map(BigInt::from),
                    };
                    assert_eq!(
                        observed.as_ref(),
                        Some(&expected),
                        "{source:?} -> {destination:?}: {integer}; {term:?}"
                    );
                }
            }
        }
    }

    fn formats() -> impl Iterator<Item = MachineIntegerFormat> {
        use MachineIntegerWidth::*;
        [Bits8, Bits16, Bits32, Bits64, Bits128]
            .into_iter()
            .flat_map(|width| [false, true].map(|signed| MachineIntegerFormat::new(width, signed)))
    }

    fn types() -> impl Iterator<Item = MachineIntegerType> {
        use MachineIntegerType::*;
        [Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64].into_iter()
    }

    fn check_truncating_division(left: MachineIntegerConstant, right: MachineIntegerConstant) {
        use num_traits::{Signed, Zero};
        let a = left.to_integer();
        let b = right.to_integer();
        let result = left.truncating_div_rem(right);
        if b.is_zero() {
            assert_eq!(result, Err(MachineIntegerDivisionError::DivisionByZero));
            return;
        }
        let quotient = &a / &b;
        let remainder = &a % &b;
        let (min, max) = left.format().bounds();
        if quotient < min || quotient > max {
            assert_eq!(result, Err(MachineIntegerDivisionError::SignedOverflow));
            return;
        }
        let (q, r) = result.unwrap();
        assert_eq!(q.format(), left.format());
        assert_eq!(r.format(), left.format());
        assert_eq!(q.to_integer(), quotient, "{a} / {b}");
        assert_eq!(r.to_integer(), remainder, "{a} % {b}");
        assert_eq!(&b * &quotient + &remainder, a);
        assert!(remainder.abs() < b.abs());
        assert!(remainder.is_zero() || remainder.sign() == a.sign());
    }

    #[test]
    fn truncating_machine_division_matches_exact_oracle_at_every_width() {
        for format in formats() {
            let (min, max) = format.bounds();
            let mut values = vec![min.clone(), &min + 1, max.clone(), &max - 1];
            for value in [
                -7i128,
                -3,
                -2,
                -1,
                0,
                1,
                2,
                3,
                7,
                1i128 << 64,
                (1i128 << 100) + 1,
            ] {
                if let Some(value) = MachineIntegerConstant::from_signed(format, value) {
                    values.push(value.to_integer());
                }
            }
            for left in &values {
                for right in &values {
                    check_truncating_division(
                        MachineIntegerConstant::from_integer(format, left).unwrap(),
                        MachineIntegerConstant::from_integer(format, right).unwrap(),
                    );
                }
            }
        }
    }

    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn truncating_machine_division_exhausts_signed_and_unsigned_bytes() {
        for signed in [false, true] {
            let format = MachineIntegerFormat::new(MachineIntegerWidth::Bits8, signed);
            for left in 0..=255 {
                for right in 0..=255 {
                    check_truncating_division(
                        MachineIntegerConstant::from_bits(format, left).unwrap(),
                        MachineIntegerConstant::from_bits(format, right).unwrap(),
                    );
                }
            }
        }
    }

    #[test]
    fn truncating_machine_division_refuses_format_retagging() {
        for left in formats() {
            for right in formats() {
                if left != right {
                    let a = MachineIntegerConstant::from_unsigned(left, 1).unwrap();
                    // Mismatch takes precedence even if the divisor is zero.
                    for bits in [0, 1] {
                        let b = MachineIntegerConstant::from_unsigned(right, bits).unwrap();
                        assert_eq!(
                            a.truncating_div_rem(b),
                            Err(MachineIntegerDivisionError::FormatMismatch)
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn machine_integer_formats_have_exact_bounds_and_literal_limits() {
        for format in formats() {
            let (lo, hi) = format.bounds();
            let power = BigInt::from(1) << (format.bits() - u32::from(format.is_signed()));
            assert_eq!(hi, &power - 1);
            assert_eq!(lo, if format.is_signed() { -power } else { 0.into() });
            assert_eq!(format.byte_width() * 8, format.bits());
            for value in [lo.clone(), hi.clone(), 0.into(), 1.into()] {
                let number = MachineIntegerConstant::from_integer(format, &value).unwrap();
                assert_eq!(number.format(), format);
                assert_eq!(number.to_integer(), value);
                assert_eq!(
                    MachineIntegerConstant::parse_decimal(format, &value.to_string()),
                    Some(number)
                );
            }
            for value in [&lo - 1, &hi + 1] {
                assert!(MachineIntegerConstant::from_integer(format, &value).is_none());
                assert!(
                    MachineIntegerConstant::parse_decimal(format, &value.to_string()).is_none()
                );
            }
            for text in ["", " 1", "1 ", "0xff", "1.0", "NaN", "++1"] {
                assert!(MachineIntegerConstant::parse_decimal(format, text).is_none());
            }
        }
    }

    #[test]
    fn machine_integer_raw_representations_preserve_sign_and_reject_oversized_payloads() {
        for format in formats() {
            let mask = format.mask();
            let all_ones = MachineIntegerConstant::from_bits(format, mask).unwrap();
            assert_eq!(all_ones.bits(), mask);
            assert_eq!(
                all_ones.to_integer(),
                if format.is_signed() {
                    (-1).into()
                } else {
                    mask.into()
                }
            );
            if format.bits() != 128 {
                assert!(MachineIntegerConstant::from_bits(format, mask + 1).is_none());
            }
        }
        let signed = MachineIntegerFormat::new(MachineIntegerWidth::Bits8, true);
        let unsigned = MachineIntegerFormat::new(MachineIntegerWidth::Bits8, false);
        for bits in 0..=255u128 {
            let signed = MachineIntegerConstant::from_bits(signed, bits).unwrap();
            let unsigned = MachineIntegerConstant::from_bits(unsigned, bits).unwrap();
            assert_eq!(signed.to_i128(), Some(i128::from(bits as u8 as i8)));
            assert_eq!(unsigned.to_u128(), Some(bits));
            assert_ne!(
                signed, unsigned,
                "format is part of identity even for equal positive values"
            );
        }
    }

    fn check_conversions(source: MachineIntegerConstant) {
        let numeric = source.to_integer();
        for destination in formats() {
            let (lo, hi) = destination.bounds();
            let checked = source.checked_convert(destination);
            let fits = lo <= numeric && numeric <= hi;
            assert_eq!(checked.is_some(), fits);
            if let Some(checked) = checked {
                assert_eq!(checked.to_integer(), numeric);
                assert_eq!(checked.format(), destination);
            }
            // Independent exact arithmetic oracle; no host shifts, sign
            // extension, or reinterpretation from the implementation.
            let modulus = BigInt::from(1) << destination.bits();
            let residue = ((&numeric % &modulus) + &modulus) % &modulus;
            let expected = if destination.is_signed() && residue >= (&modulus / 2) {
                residue - &modulus
            } else {
                residue
            };
            let converted = source.convert_modulo(destination);
            assert_eq!(converted.to_integer(), expected);
            assert_eq!(converted.format(), destination);
            if let Some(checked) = checked {
                assert_eq!(converted, checked);
            }
            assert_eq!(converted.convert_modulo(destination), converted);
        }
    }

    #[test]
    fn machine_integer_checked_and_modulo_conversions_match_independent_exact_arithmetic() {
        for source in formats() {
            let (lo, hi) = source.bounds();
            for value in [
                lo.clone(),
                &lo + 1,
                (-1).into(),
                0.into(),
                1.into(),
                &hi - 1,
                hi,
            ] {
                if let Some(value) = MachineIntegerConstant::from_integer(source, &value) {
                    check_conversions(value);
                }
            }
            if source.bits() == 8 {
                for bits in 0..=255 {
                    check_conversions(MachineIntegerConstant::from_bits(source, bits).unwrap());
                }
            }
        }
    }

    #[test]
    fn machine_integer_128_bit_widening_and_narrowing_keep_numeric_and_modulo_policies_distinct() {
        let i128_format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, true);
        let u128_format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, false);
        let i64_format = MachineIntegerType::Int64.format();
        let u64_format = MachineIntegerType::UInt64.format();
        let negative = MachineIntegerConstant::from_signed(i64_format, -1).unwrap();
        let widened = negative.checked_convert(i128_format).unwrap();
        assert_eq!(widened.to_i128(), Some(-1));
        assert_eq!(widened.bits(), u128::MAX);
        assert!(negative.checked_convert(u128_format).is_none());
        assert_eq!(
            negative.convert_modulo(u128_format).to_u128(),
            Some(u128::MAX)
        );
        let unsigned =
            MachineIntegerConstant::from_unsigned(u64_format, u128::from(u64::MAX)).unwrap();
        assert_eq!(
            unsigned.checked_convert(i128_format).unwrap().to_i128(),
            Some(i128::from(u64::MAX))
        );
        let signed_min = MachineIntegerConstant::from_signed(i128_format, i128::MIN).unwrap();
        assert_eq!(signed_min.to_i128(), Some(i128::MIN));
        assert_eq!(signed_min.to_u128(), None);
        assert!(signed_min.checked_convert(i64_format).is_none());
        assert_eq!(signed_min.convert_modulo(i64_format).to_i128(), Some(0));
        let unsigned_max = MachineIntegerConstant::from_unsigned(u128_format, u128::MAX).unwrap();
        assert_eq!(unsigned_max.to_i128(), None);
        assert!(unsigned_max.checked_convert(i128_format).is_none());
        assert_eq!(unsigned_max.convert_modulo(i128_format).to_i128(), Some(-1));
        assert_eq!(
            unsigned_max.convert_modulo(u64_format).to_u128(),
            Some(u128::from(u64::MAX))
        );
    }

    #[test]
    fn machine_integer_runtime_carriers_round_trip_and_reject_wrong_width_or_signedness() {
        for ty in types() {
            let (lo, hi) = ty.format().bounds();
            for value in [lo, hi, 0.into(), 1.into()] {
                let constant = MachineIntegerConstant::from_integer(ty.format(), &value).unwrap();
                let term = ty.constant_term(constant).unwrap();
                assert_eq!(ty.constant_from_term(&term), Some(constant));
                let runtime = ty.constant_value(constant).unwrap();
                assert_eq!(runtime.program_type(), ty.program_type());
                assert_eq!(ty.constant_from_value(&runtime), Some(constant));
                for other in types().filter(|other| *other != ty) {
                    assert!(other.constant_value(constant).is_none());
                    assert!(other.constant_term(constant).is_none());
                    assert!(other.constant_from_value(&runtime).is_none());
                }
            }
        }
        let ty = MachineIntegerType::Int8;
        // A narrow signed constant is its own 8 bits; no 32-bit word is
        // one, whether or not its low bits are the value's.
        assert!(ty.constant_from_term(&MachineTerm::constant(255)).is_none());
        assert!(
            ty.constant_from_term(&MachineTerm::constant(u32::MAX))
                .is_none()
        );
        assert_eq!(
            ty.constant_from_term(&MachineTerm::narrow_constant(ty, 0xFF))
                .unwrap()
                .to_i128(),
            Some(-1)
        );
        assert!(
            MachineIntegerType::Int64
                .constant_from_term(&MachineTerm::uint64_constant(u64::MAX))
                .is_none()
        );
        for format in formats().filter(|format| format.bits() == 128) {
            let wide = MachineIntegerConstant::from_unsigned(format, 0).unwrap();
            for ty in types() {
                assert!(ty.constant_value(wide).is_none());
            }
        }
    }

    /// `Bits32 @ f` binds the matched 32-bit format, so a rule that rebuilds
    /// the operator over new operands keeps it (`binary_node!(@ f, ..)`).
    #[test]
    fn a_rebuilt_32_bit_operator_keeps_its_format() {
        use crate::kernel::{binary_node, binary_term};
        let rebuild = |term: &MachineTerm| match term {
            binary_term!(Bits32 @ format, Add, left, right) => Some(binary_node!(
                @ *format,
                Add,
                right.clone(),
                left.clone()
            )),
            _ => None,
        };
        let (a, b) = (
            Box::new(MachineTerm::Variable(crate::kernel::Variable(186_021))),
            Box::new(MachineTerm::Variable(crate::kernel::Variable(186_022))),
        );
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let sum = binary_node!(@ format, Add, a.clone(), b.clone());
            assert_eq!(
                rebuild(&sum),
                Some(binary_node!(@ format, Add, b.clone(), a.clone()))
            );
        }
        assert_eq!(
            rebuild(&binary_node!(@ MachineIntegerType::Int64, Add, a, b)),
            None
        );
    }

    /// A rule that reads only an operation's bits reads it at either 32-bit
    /// format (`binary_term!(Bits32, ..)`): the constant value of a `uint32`
    /// sum is its bits, and a `uint32` mask is a canonical byte carrier.
    #[test]
    fn bit_readers_read_a_32_bit_operator_at_either_format() {
        use crate::kernel::{binary_node, unary_node};
        let constant = |value| Box::new(MachineTerm::constant(value));
        for (signed, unsigned) in [
            (
                binary_node!(Int32, Add, constant(7), constant(u32::MAX)),
                binary_node!(UInt32, Add, constant(7), constant(u32::MAX)),
            ),
            (
                binary_node!(Int32, BitwiseXor, constant(5), constant(3)),
                binary_node!(UInt32, BitwiseXor, constant(5), constant(3)),
            ),
            (
                unary_node!(Int32, BitwiseNot, constant(0)),
                unary_node!(UInt32, BitwiseNot, constant(0)),
            ),
        ] {
            assert!(signed.as_const().is_some());
            assert_eq!(unsigned.as_const(), signed.as_const(), "{unsigned:?}");
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/machine_integer/tests.rs");
    }
}
