//! Width and numeric interpretation of fixed-width integer constants.
//!
//! These are representation values, not execution certificates. A format may
//! describe 128 bits before a frontend or symbolic runtime supports that width.
//! Checked conversions preserve the numeric value; modulo conversions are an
//! explicit, separate policy for languages that specify them.

use super::{Bitvector32Term, CValue, MachineIntegerType};
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

    const fn mask(self) -> u128 {
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

    /// Produce only the supported runtime carrier, with signed narrow values
    /// sign-extended to the legacy 32-bit term representation.
    pub(crate) fn constant_term(self, value: MachineIntegerConstant) -> Option<Bitvector32Term> {
        if value.format != self.format() {
            return None;
        }
        Some(match self {
            Self::Int8 | Self::Int16 | Self::Int32 => {
                Bitvector32Term::Constant(value.to_i128()? as u32)
            }
            Self::UInt8 | Self::UInt16 | Self::UInt32 => {
                Bitvector32Term::Constant(value.to_u128()? as u32)
            }
            Self::Int64 => Bitvector32Term::Int64Constant(value.to_i128()? as i64),
            Self::UInt64 => Bitvector32Term::UInt64Constant(value.to_u128()? as u64),
            Self::Int128 | Self::UInt128 => Bitvector32Term::MachineIntegerConstant(value),
        })
    }

    /// Convert an evaluated, typed machine value modulo this type's width.
    /// Only root constants fold here; symbolic operands are retained in the
    /// existing term arena. The value wrapper supplies source signedness.
    pub(crate) fn convert_modulo_value(self, value: CValue) -> Option<CValue> {
        crate::instrumentation::record_deterministic_work(1);
        // Boolean values are normalized 0/1 and have their own storage type.
        // Integer conversion observes that numeric value without retagging
        // arbitrary bytes as a Boolean.
        let value = match value {
            CValue::Bool(term) => CValue::UInt8(term),
            value => value,
        };
        let source = Self::from_c_type(value.c_type())?;
        // Root validation stays local even when an operand contains a large
        // legacy expression. Wide operands cannot reinterpret word nodes.
        if source.format().bits() == 128 || self.format().bits() == 128 {
            let term = match value {
                crate::kernel::integer_c_value!(term) => term,
                _ => return None,
            };
            if !source.accepts_cast_operand(&term) {
                return None;
            }
            return Some(
                self.value_from_term(Bitvector32Term::machine_integer_cast(source, self, term)),
            );
        }
        if let Some(constant) = source.constant_from_value(&value) {
            return self.constant_value(constant.convert_modulo(self.format()));
        }
        if source == self {
            return Some(value);
        }
        let term = match value {
            crate::kernel::integer_c_value!(term) => term,
            _ => return None,
        };
        let source_format = source.format();
        let destination = self.format();
        let term = if destination.bits() == 64 {
            match (
                destination.is_signed(),
                source_format.bits(),
                source_format.is_signed(),
            ) {
                (true, 64, _) => Bitvector32Term::int64_from_uint64_bits(term),
                (false, 64, _) => Bitvector32Term::uint64_from_int64(term),
                (true, _, true) => Bitvector32Term::int64_from_32(term),
                (true, _, false) => Bitvector32Term::int64_from_uint32(term),
                (false, _, true) => Bitvector32Term::uint64_from_int32(term),
                (false, _, false) => Bitvector32Term::uint64_from_32(term),
            }
        } else {
            let word = if source_format.bits() == 64 {
                Bitvector32Term::uint32_from_64(term)
            } else {
                term
            };
            if destination.bits() == 32 {
                word
            } else if destination.is_signed() {
                // The narrow signed value still uses a sign-extended word.
                // Mask first, flip the sign bit, then subtract it. The masked
                // intermediate is at most 65535, so subtraction cannot
                // overflow the 32-bit carrier (unlike a signed left shift).
                let mask = (1u32 << destination.bits()) - 1;
                let sign = 1u32 << (destination.bits() - 1);
                Bitvector32Term::subtract(
                    Bitvector32Term::bitwise_xor(
                        Bitvector32Term::bitwise_and(word, Bitvector32Term::Constant(mask)),
                        Bitvector32Term::Constant(sign),
                    ),
                    Bitvector32Term::Constant(sign),
                )
            } else {
                Bitvector32Term::bitwise_and(
                    word,
                    Bitvector32Term::Constant((1u32 << destination.bits()) - 1),
                )
            }
        };
        Some(self.value_from_term(term))
    }

    /// Root validation for the bounded wide runtime profile. The term arena
    /// is shared, but its legacy arithmetic nodes must not acquire a wide
    /// interpretation merely by changing a value wrapper.
    pub(crate) fn accepts_wide_term(self, value: &Bitvector32Term) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if self.format().bits() != 128 {
            return false;
        }
        match value {
            Bitvector32Term::MachineIntegerConstant(value) => value.format() == self.format(),
            Bitvector32Term::Variable(_) => true,
            Bitvector32Term::MemoryLoad(_, _, kind) => {
                crate::kernel::LoadKind::of_type(self.c_type()) == Some(*kind)
            }
            Bitvector32Term::IntegerToMachine { destination, .. } => *destination == self,
            Bitvector32Term::MachineIntegerCast {
                value,
                source,
                destination,
            } => *destination == self && source.accepts_cast_operand(value),
            _ => false,
        }
    }

    pub(in crate::kernel) fn accepts_cast_operand(self, value: &Bitvector32Term) -> bool {
        let (mut ty, mut value) = (self, value);
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match value {
                Bitvector32Term::Constant(_)
                | Bitvector32Term::Int64Constant(_)
                | Bitvector32Term::UInt64Constant(_)
                | Bitvector32Term::MachineIntegerConstant(_) => {
                    return ty.constant_from_term(value).is_some();
                }
                Bitvector32Term::Variable(_) => return true,
                Bitvector32Term::MemoryLoad(_, _, kind) if ty.format().bits() == 128 => {
                    return crate::kernel::LoadKind::of_type(ty.c_type()) == Some(*kind);
                }
                Bitvector32Term::IntegerToMachine { destination, .. } => return *destination == ty,
                Bitvector32Term::MachineIntegerCast {
                    value: operand,
                    source,
                    destination,
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

    pub(crate) fn constant_value(self, value: MachineIntegerConstant) -> Option<CValue> {
        Some(self.value_from_term(self.constant_term(value)?))
    }

    pub(in crate::kernel) fn value_from_term(self, term: Bitvector32Term) -> CValue {
        match self {
            Self::Int8 => CValue::Int8(term),
            Self::UInt8 => CValue::UInt8(term),
            Self::Int16 => CValue::Int16(term),
            Self::UInt16 => CValue::UInt16(term),
            Self::Int32 => CValue::Int32(term),
            Self::UInt32 => CValue::UInt32(term),
            Self::Int64 => CValue::Int64(term),
            Self::UInt64 => CValue::UInt64(term),
            Self::Int128 => CValue::Int128(term),
            Self::UInt128 => CValue::UInt128(term),
        }
    }

    pub(crate) fn constant_from_term(
        self,
        value: &Bitvector32Term,
    ) -> Option<MachineIntegerConstant> {
        match (self, value) {
            (Self::Int128 | Self::UInt128, Bitvector32Term::MachineIntegerConstant(value))
                if value.format() == self.format() =>
            {
                Some(*value)
            }
            (Self::Int8 | Self::Int16 | Self::Int32, Bitvector32Term::Constant(value)) => {
                MachineIntegerConstant::from_signed(self.format(), i128::from(*value as i32))
            }
            (Self::UInt8 | Self::UInt16 | Self::UInt32, Bitvector32Term::Constant(value)) => {
                MachineIntegerConstant::from_unsigned(self.format(), u128::from(*value))
            }
            (Self::Int64, Bitvector32Term::Int64Constant(value)) => {
                MachineIntegerConstant::from_signed(self.format(), i128::from(*value))
            }
            (Self::UInt64, Bitvector32Term::UInt64Constant(value)) => {
                MachineIntegerConstant::from_unsigned(self.format(), u128::from(*value))
            }
            _ => None,
        }
    }

    pub(crate) fn constant_from_value(self, value: &CValue) -> Option<MachineIntegerConstant> {
        if value.c_type() != self.c_type() {
            return None;
        }
        let term = match value {
            crate::kernel::integer_c_value!(term) => term,
            _ => return None,
        };
        self.constant_from_term(term)
    }
}

impl Bitvector32Term {
    /// The term a read of `kind` at `pointer` in `memory` denotes. This is
    /// the one place a symbolic read term is formed from a kind.
    ///
    /// One byte, one name: a byte of memory has a single term, its unsigned
    /// (`UInt8`) read. A signed (`Int8`) read of the byte is the
    /// two's-complement conversion of that one term, [`Self::signed_byte`],
    /// never an unknown of its own, so a signed and an unsigned read of the
    /// same byte are related by construction. Every other kind is its own
    /// `MemoryLoad`. A `MemoryLoad` of kind `Int8` is never formed; the load
    /// registry refuses to name one (`load_variable_for_term`), so a
    /// producer that bypassed this constructor gets no name and no fact.
    pub(crate) fn memory_read(
        memory: crate::kernel::SharedCMemory,
        pointer: crate::kernel::Pointer,
        kind: crate::kernel::LoadKind,
    ) -> Self {
        use crate::kernel::LoadKind;
        match kind {
            LoadKind::Int8 => {
                Self::signed_byte(Self::MemoryLoad(memory, Box::new(pointer), LoadKind::UInt8))
            }
            kind => Self::MemoryLoad(memory, Box::new(pointer), kind),
        }
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

    /// The unsigned byte a [`Self::signed_byte`] term converts, if this is one.
    pub(crate) fn signed_byte_operand(&self) -> Option<&Self> {
        match self {
            Self::MachineIntegerCast {
                value,
                source: MachineIntegerType::UInt8,
                destination: MachineIntegerType::Int8,
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
        // The outer conversion keeps only bits the intermediate preserved.
        // If it widens again, retain the intermediate signed interpretation.
        if let Self::MachineIntegerCast {
            source: original,
            destination: intermediate,
            value: operand,
        } = value
        {
            if intermediate == source && destination.format().bits() <= intermediate.format().bits()
            {
                return Self::machine_integer_cast(original, destination, *operand);
            }
            return Self::MachineIntegerCast {
                value: Box::new(Self::MachineIntegerCast {
                    source: original,
                    destination: intermediate,
                    value: operand,
                }),
                source,
                destination,
            };
        }
        Self::MachineIntegerCast {
            value: Box::new(value),
            source,
            destination,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wide_cast_symbolic_and_constant_conversions_match_independent_exact_oracle() {
        use crate::kernel::Variable;
        use crate::kernel::reasoning::substitute_bitvector_variable_in_c_value;
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
                let symbolic = destination
                    .convert_modulo_value(
                        source.value_from_term(Bitvector32Term::Variable(variable)),
                    )
                    .unwrap();
                for integer in &samples {
                    let input =
                        MachineIntegerConstant::from_integer(source.format(), integer).unwrap();
                    let actual = substitute_bitvector_variable_in_c_value(
                        &symbolic,
                        variable,
                        &source.constant_term(input).unwrap(),
                    );
                    let literal = destination
                        .convert_modulo_value(source.constant_value(input).unwrap())
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
        use crate::kernel::reasoning::substitute_bitvector_variable_in_c_value;
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
                    let inner = Bitvector32Term::machine_integer_cast(
                        source,
                        intermediate,
                        Bitvector32Term::Variable(variable),
                    );
                    let term =
                        Bitvector32Term::machine_integer_cast(intermediate, destination, inner);
                    if destination == source
                        && intermediate.format().bits() >= source.format().bits()
                    {
                        assert_eq!(term, Bitvector32Term::Variable(variable));
                    }
                    for input in [min.clone(), max.clone(), 0.into(), 1.into()] {
                        let constant =
                            MachineIntegerConstant::from_integer(source.format(), &input).unwrap();
                        let value = destination.value_from_term(term.clone());
                        let result = substitute_bitvector_variable_in_c_value(
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
    fn wide_cast_construction_and_validation_do_constant_work_on_large_operands() {
        use crate::kernel::Variable;
        for size in [16, 64, 256, 1024] {
            let mut operand = Bitvector32Term::Variable(Variable(149_002));
            for _ in 0..size {
                operand = Bitvector32Term::Int64Add(
                    Box::new(operand),
                    Box::new(Bitvector32Term::Int64Constant(1)),
                );
            }
            let (converted, work) = crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerType::Int128.convert_modulo_value(CValue::Int64(operand))
            });
            let CValue::Int128(term) = converted.unwrap() else {
                unreachable!()
            };
            assert_eq!(work, 3, "size {size}");
            let (accepted, validation_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    MachineIntegerType::Int128.accepts_wide_term(&term)
                });
            assert!(accepted);
            assert_eq!(validation_work, 2);
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
                let symbolic = destination
                    .convert_modulo_value(
                        source.value_from_term(Bitvector32Term::Variable(variable)),
                    )
                    .unwrap();
                assert_eq!(symbolic.c_type(), destination.c_type());
                for integer in &samples {
                    let constant = MachineIntegerConstant::from_integer(format, integer).unwrap();
                    let substituted = substitute_bitvector_variable_in_term(
                        &Term::CValue(symbolic.clone()),
                        variable,
                        &source.constant_term(constant).unwrap(),
                    );
                    let Term::CValue(actual) = substituted else {
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

    #[test]
    fn symbolic_modulo_conversion_work_is_independent_of_operand_depth() {
        for right_nested in [false, true] {
            for size in [16, 64, 256, 1024] {
                let mut term = Bitvector32Term::Variable(super::super::Variable(138_002));
                for _ in 0..size {
                    let one = Bitvector32Term::UInt64Constant(1);
                    term = if right_nested {
                        Bitvector32Term::UInt64Add(Box::new(one), Box::new(term))
                    } else {
                        Bitvector32Term::UInt64Add(Box::new(term), Box::new(one))
                    };
                }
                let (converted, work) = crate::instrumentation::measure_deterministic_work(|| {
                    MachineIntegerType::Int16.convert_modulo_value(CValue::UInt64(term))
                });
                assert_eq!(converted.unwrap().c_type(), super::super::CType::Int16);
                assert_eq!(work, 1, "size {size}, right nested {right_nested}");
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
    fn truncating_machine_division_work_scales_with_explicit_operations() {
        for format in formats() {
            let left = MachineIntegerConstant::from_bits(format, format.mask()).unwrap();
            let right = MachineIntegerConstant::from_unsigned(format, 3).unwrap();
            for size in [2usize, 8, 32, 128] {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        left.truncating_div_rem(right).unwrap();
                    }
                });
                assert!(work <= 4 * size, "{format:?}, {size}: {work}");
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
                assert_eq!(runtime.c_type(), ty.c_type());
                assert_eq!(ty.constant_from_value(&runtime), Some(constant));
                for other in types().filter(|other| *other != ty) {
                    assert!(other.constant_value(constant).is_none());
                    assert!(other.constant_term(constant).is_none());
                    assert!(other.constant_from_value(&runtime).is_none());
                }
            }
        }
        let ty = MachineIntegerType::Int8;
        // Narrow signed terms are sign-extended to 32 bits, never truncated
        // from a malformed carrier that merely shares their low bits.
        assert!(
            ty.constant_from_term(&Bitvector32Term::Constant(255))
                .is_none()
        );
        assert_eq!(
            ty.constant_from_term(&Bitvector32Term::Constant(u32::MAX))
                .unwrap()
                .to_i128(),
            Some(-1)
        );
        assert!(
            MachineIntegerType::Int64
                .constant_from_term(&Bitvector32Term::UInt64Constant(u64::MAX))
                .is_none()
        );
        for format in formats().filter(|format| format.bits() == 128) {
            let wide = MachineIntegerConstant::from_unsigned(format, 0).unwrap();
            for ty in types() {
                assert!(ty.constant_value(wide).is_none());
            }
        }
    }

    #[test]
    fn machine_integer_constant_work_is_linear_and_oversized_integer_rejection_is_constant() {
        let format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, true);
        let source =
            MachineIntegerConstant::from_signed(MachineIntegerType::Int64.format(), -1).unwrap();
        let mut previous = None;
        for size in [4, 16, 64, 256, 1024] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    let widened = source.checked_convert(format).unwrap();
                    assert_eq!(widened.checked_convert(source.format()), Some(source));
                    assert_eq!(widened.convert_modulo(source.format()), source);
                }
            });
            if let Some(previous) = previous {
                assert_eq!(work, previous * 4);
            }
            assert!(work > 0);
            previous = Some(work);
        }
        let mut previous = None;
        for bits in [256usize, 1024, 4096, 16384, 65536] {
            let value = BigInt::from(1) << bits;
            let (rejected, work) = crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerConstant::from_integer(format, &value).is_none()
            });
            assert!(rejected);
            assert!(work > 0);
            if let Some(previous) = previous {
                assert_eq!(work, previous);
            }
            previous = Some(work);
        }
        let mut previous = None;
        for size in [16, 64, 256, 1024] {
            let spelling = format!("{}1", "0".repeat(size));
            let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerConstant::parse_decimal(format, &spelling)
            });
            assert_eq!(value.unwrap().to_i128(), Some(1));
            assert_eq!(work, size + 3);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
    }
}
