//! Conversion: `to_integer(cast(S -> F, v)) == to_integer(v)` when
//! `to_integer(v)` lies in `F`. Every conversion is modular, so its result
//! is the one element of `F` congruent to `v` modulo `2^w`; when `v` lies
//! in `F` that element is `v`. When `F` contains `S` every value of `S`
//! lies in `F`, so widening needs no premise; a narrowing needs the range.
//!
//! Both the root-local `close()` rule and the compatibility certificate
//! `integer_cast_identity` check this statement for
//! the conversion its observation names ([`cast`] gives the format the
//! operand's two bounds must lie in). A widening's bounds are the operand's
//! own range, which the type-range rule states with no premise. Which nodes spell a conversion is the term
//! representation's business (`representation::low_word`,
//! `representation::has_legacy_conversions`).
//!
//! The Integer-to-machine conversion `to_T(z)` is read the same way:
//! `to_integer(to_T(z)) == z` when `z` lies in `T` ([`integer_conversion`]).
//! Its meaning is an element of `T` that is `z` whenever `z` lies in `T`
//! (the evaluator owes `z`'s range wherever it lowers `to_T(z)`), so the rule
//! states exactly that meaning, once for every format, with the same two
//! bounds a narrowing's identity takes.
//!
//! It is also the one conversion table of the languages
//! (`design/machine-integers.md`, "Conversions in the languages"): [`lower`]
//! says, for a source and destination format and a policy, which node a
//! conversion builds and whether it owes its range, and [`convert_term`]
//! builds that node. C's conversions (`narrow_integer`), C++20 integral
//! conversions and Rust `as` (`conversion::convert_value`)
//! build their terms here, so one conversion has one term in every
//! language. The policy changes only what the conversion owes, never its
//! term.

use super::representation;
use crate::kernel::MachineCastSpelling;
use crate::kernel::binary_term;
use crate::kernel::{IntegerTerm, MachineIntegerType, MachineTerm, ProgramValue};
use crate::kernel::{bits32_constant, constant_u32};

/// What a language conversion asks of its operand.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConversionPolicy {
    /// The value modulo 2^w of the destination width, owing nothing: C's
    /// conversion as GCC and Clang compile it (signed narrowing included,
    /// `design/machine-integers.md`, Decisions 2026-10-21), C++20 integral
    /// conversions and Rust `as`.
    Modular,
    /// A specification's conversion between machine types: the same term,
    /// owing the destination's range where [`Conversion::owes_range`] says.
    Checked,
}

/// The node a conversion builds, by source and destination format.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConversionLowering {
    /// The same format: the operand itself.
    Identity,
    /// `int32` to `uint32` or back: the sign cast σ (rules K1 to K4).
    SignCast,
    /// The generic `Cast`: every conversion into an 8- or 16-bit format
    /// (its word is rule K7's), every widening of an 8- or 16-bit value into
    /// a 32-bit format (whose word is its operand's, rule K8), and every
    /// conversion involving 128 bits.
    Cast,
    /// A 64-bit value into a 32-bit format: its low word, `UInt32From64`.
    LowWord,
    /// A value of at most 32 bits into a 64-bit format: the legacy
    /// extension node of the source's and destination's signedness.
    Extend64,
    /// `int64` to `uint64` or back: the same 64 bits.
    Reinterpret64,
}

/// One entry of the conversion table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Conversion {
    pub(crate) lowering: ConversionLowering,
    /// Whether the conversion owes its operand's destination range: only a
    /// [`ConversionPolicy::Checked`] conversion that can change the value,
    /// into a signed destination other than by σ, or into an 8- or 16-bit
    /// unsigned one from at most 64 bits. Every other conversion is modular.
    pub(crate) owes_range: bool,
}

/// The conversion table: the node a conversion from `source` to
/// `destination` builds, and what it owes under `policy`. Width and
/// signedness checks only; no term is inspected.
pub(crate) fn lower(
    source: MachineIntegerType,
    destination: MachineIntegerType,
    policy: ConversionPolicy,
) -> Conversion {
    use ConversionLowering as L;
    let (from, to) = (source.format(), destination.format());
    let lowering = if source == destination {
        L::Identity
    } else if from.bits() == 128 || to.bits() == 128 || to.bits() < 32 || from.bits() < 32 {
        L::Cast
    } else if to.bits() == 32 {
        match from.bits() {
            64 => L::LowWord,
            32 => L::SignCast,
            _ => L::Cast,
        }
    } else if from.bits() == 64 {
        L::Reinterpret64
    } else {
        L::Extend64
    };
    let owes_range = policy == ConversionPolicy::Checked
        && !to.contains(from)
        && lowering != L::SignCast
        && (to.is_signed() || (to.bits() < 32 && from.bits() <= 64));
    Conversion {
        lowering,
        owes_range,
    }
}

/// C11 6.3.1.8, the usual arithmetic conversions, over formats in the LP64
/// model Click targets: the format two integer operands of formats `left`
/// and `right` are converted to. Each is first promoted (6.3.1.1): a format
/// of fewer than 32 bits, every value of which `int32` holds, to `int32`.
/// Then the two agree; or, of one signedness, the wider is taken; or the
/// unsigned one is taken when it is at least as wide as the signed one; or
/// the signed one when it holds every value of the unsigned one; or else
/// the unsigned format of the signed one's width. `None` for a 128-bit
/// operand, which no C operation here takes. Width and signedness checks
/// only.
pub(crate) fn usual_arithmetic_format(
    left: MachineIntegerType,
    right: MachineIntegerType,
) -> Option<MachineIntegerType> {
    let promote = |ty: MachineIntegerType| {
        if ty.format().bits() < 32 {
            MachineIntegerType::Int32
        } else {
            ty
        }
    };
    let (left, right) = (promote(left), promote(right));
    let (l, r) = (left.format(), right.format());
    if l.bits() > 64 || r.bits() > 64 {
        return None;
    }
    if left == right {
        return Some(left);
    }
    if l.is_signed() == r.is_signed() {
        return Some(if l.bits() >= r.bits() { left } else { right });
    }
    let (signed, unsigned) = if l.is_signed() {
        (left, right)
    } else {
        (right, left)
    };
    Some(if unsigned.format().bits() >= signed.format().bits() {
        unsigned
    } else if signed.format().contains(unsigned.format()) {
        signed
    } else {
        match signed {
            MachineIntegerType::Int32 => MachineIntegerType::UInt32,
            _ => MachineIntegerType::UInt64,
        }
    })
}

/// The typed extension node of a 32-to-64-bit conversion from `source` to
/// `destination`, if it is one ([`ConversionLowering::Extend64`]). Such a
/// conversion has this one spelling: lowering builds it, and so does every
/// kernel query that widens a 32-bit operand to 64 bits. Width and
/// signedness checks only.
pub(crate) fn extension_encoding(
    source: MachineIntegerType,
    destination: MachineIntegerType,
) -> Option<crate::kernel::MachineCastSpelling> {
    use crate::kernel::MachineCastSpelling as E;
    if lower(source, destination, ConversionPolicy::Modular).lowering
        != ConversionLowering::Extend64
    {
        return None;
    }
    Some(
        match (
            source.format().is_signed(),
            destination.format().is_signed(),
        ) {
            (true, true) => E::Int64From32,
            (false, true) => E::Int64FromUInt32,
            (true, false) => E::UInt64FromInt32,
            (false, false) => E::UInt64From32,
        },
    )
}

/// Whether rule W reads a typed extension node with `encoding`, from
/// `source` to `destination`, as its operand: the extension keeps every
/// value of its source. `UInt64FromInt32` does not, and neither does a
/// generic node, which the readings handle on their own.
pub(crate) fn reads_as_operand(
    encoding: crate::kernel::MachineCastSpelling,
    source: MachineIntegerType,
    destination: MachineIntegerType,
) -> bool {
    use crate::kernel::MachineCastSpelling as E;
    matches!(
        encoding,
        E::Int64From32 | E::Int64FromUInt32 | E::UInt64From32
    ) && destination.format().contains(source.format())
}

/// The term of the conversion of `value`, a term of `source`, to
/// `destination`, as [`lower`] says. A constant operand folds (the
/// constructors fold a root constant); nothing else is inspected, so the
/// work is constant whatever the operand's size, charged by the node's
/// constructor.
pub(crate) fn convert_term(
    source: MachineIntegerType,
    destination: MachineIntegerType,
    value: MachineTerm,
) -> MachineTerm {
    use ConversionLowering as L;
    let (from, to) = (source.format(), destination.format());
    match lower(source, destination, ConversionPolicy::Modular).lowering {
        L::Identity => value,
        L::SignCast => MachineTerm::sign_cast32(source, destination, value),
        L::Cast => MachineTerm::machine_integer_cast(source, destination, value),
        // A folded low word is a constant of the destination's format.
        L::LowWord => MachineTerm::uint32_from_64(value).in_format32(destination),
        L::Reinterpret64 if to.is_signed() => MachineTerm::int64_from_uint64_bits(value),
        L::Reinterpret64 => MachineTerm::uint64_from_int64(value),
        L::Extend64 => match (to.is_signed(), from.is_signed()) {
            (true, true) => MachineTerm::int64_from_32(value),
            (true, false) => MachineTerm::int64_from_uint32(value),
            (false, true) => MachineTerm::uint64_from_int32(value),
            (false, false) => MachineTerm::uint64_from_32(value),
        },
    }
}

/// The modular conversion of an evaluated, typed machine value to
/// `destination`: the one entry point of C++20 integral conversions and
/// Rust `as` (`conversion::convert_value`), and of C's
/// conversions involving 128 bits. A Boolean source observes its 0-or-1
/// value. A root constant folds exactly; a 128-bit conversion first checks
/// its operand's root (`accepts_cast_operand`). `None` for a value that is
/// not an integer.
pub(crate) fn convert_value(
    value: ProgramValue,
    destination: MachineIntegerType,
) -> Option<ProgramValue> {
    crate::instrumentation::record_deterministic_work(1);
    let value = value.numeric_value().clone();
    // Rule C1: a `Bool` converted to an integer is its cast at the
    // destination's format, 1 when it holds and 0 otherwise. It owes
    // nothing under either policy.
    if let ProgramValue::Bool(word) = &value {
        return ProgramValue::from_bitvector_term(
            destination.program_type(),
            crate::kernel::MachineTerm::bool_word_as(destination, word),
        );
    }
    let source = MachineIntegerType::from_program_type(value.program_type())?;
    let wide = source.format().bits() == 128 || destination.format().bits() == 128;
    if !wide {
        if let Some(constant) = source.constant_from_value(&value) {
            return destination.constant_value(constant.convert_modulo(destination.format()));
        }
        if source == destination {
            return Some(value);
        }
    }
    let term = match value {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    // Root validation stays local even when an operand contains a large
    // legacy expression. Wide operands cannot reinterpret word nodes.
    if wide && !source.accepts_cast_operand(&term) {
        return None;
    }
    Some(destination.value_from_term(convert_term(source, destination, term)))
}

/// The candidate operands a cast identity for `observed` may name: each
/// observation `to_integer(x)` with `observed` the modulo conversion of `x`
/// this rule accepts. A 64-to-32-bit word narrowing does not record its
/// operand's signedness, so it has both readings.
pub(crate) fn cast_operands(observed: &IntegerTerm) -> Vec<IntegerTerm> {
    use MachineIntegerType as Ty;
    // An observation of σ names the conversion its value reading does
    // (rule W): `count as uint32 as int32` converts `count`.
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return Vec::new();
    };
    use crate::kernel::MachineCastSpelling as E;
    let Some((encoding, source, _, operand)) = machine.operand_view().cast() else {
        return Vec::new();
    };
    let candidates = match encoding {
        E::Generic => vec![source],
        E::UInt32From64 => vec![Ty::UInt64, Ty::Int64],
        E::Int64From32 | E::UInt64From32 | E::Int64FromUInt32 | E::UInt64FromInt32 => {
            vec![Ty::Int32, Ty::UInt32]
        }
        E::UInt64FromInt64 => vec![Ty::Int64],
    };
    candidates
        .into_iter()
        .filter_map(|ty| operand.observe(ty))
        .filter(|original| {
            original.value_read() != observed.value_read() && cast(observed, original).is_some()
        })
        .collect()
}

/// The Integer operand `z` and format `T` of an observation
/// `to_integer(to_T(z))` read at `T` itself. One match on the observation's
/// root selects the destination before a caller requests the native Integer operand.
pub(crate) fn integer_conversion(
    observed: &IntegerTerm,
) -> Option<(crate::kernel::SharedIntegerTerm, MachineIntegerType)> {
    let IntegerTerm::Machine(machine) = observed else {
        return None;
    };
    let operand = machine.operand_view();
    let destination = operand.integer_conversion_destination()?;
    if destination != machine.ty() {
        return None;
    }
    let term = match operand {
        crate::kernel::MachineOperandView::Shared(term) => term.machine_conversion_leaf()?,
        crate::kernel::MachineOperandView::Legacy(term) => term,
    };
    let MachineTerm::IntegerToMachine { value, .. } = term else {
        unreachable!("selected Integer conversion");
    };
    Some((value.clone(), destination))
}

/// The word through which `observed`, at a format of more than 16 bits,
/// may read a narrow value: its own word up to 32 bits, or the operand of
/// a 32-to-64-bit conversion. A narrow observation of that word is the
/// candidate operand of a widening identity ([`narrow_widening`]).
pub(crate) fn widened_narrow_word(
    observed: &IntegerTerm,
) -> Option<crate::kernel::MachineOperandView<'_>> {
    use crate::kernel::MachineCastSpelling as E;
    let IntegerTerm::Machine(machine) = observed else {
        return None;
    };
    let view = machine.operand_view();
    match machine.ty().format().bits() {
        16 | 32 => Some(match view.cast() {
            Some((E::Generic, source, destination, operand))
                if crate::kernel::is_narrow_widening32(source, destination) =>
            {
                operand
            }
            _ => view,
        }),
        64 => match view.cast()? {
            (
                E::Int64From32 | E::UInt64FromInt32 | E::Int64FromUInt32 | E::UInt64From32,
                _,
                _,
                operand,
            ) => Some(operand),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `observed` reads the narrow value `original` at a format that
/// contains it: its widening, which holds the same value (rule K8, a
/// relation across widths). A narrow value is a value of its own format, so
/// its widening needs no bounds; the certificate's two bounds are still
/// checked as for any cast.
pub(crate) fn narrow_widening(observed: &IntegerTerm, original: &IntegerTerm) -> bool {
    let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) = (observed, original)
    else {
        return false;
    };
    let (source, destination) = (operand.ty().format(), machine.ty().format());
    if source.bits() >= 32 || destination == source || !destination.contains(source) {
        return false;
    }
    match machine.operand_view().cast() {
        Some((MachineCastSpelling::Generic, from, _, value)) => {
            from == operand.ty() && value.retain(operand.ty()) == *operand
        }
        _ => false,
    }
}

pub(crate) fn cast(
    observed: &IntegerTerm,
    original: &IntegerTerm,
) -> Option<crate::kernel::primitives::MachineIntegerFormat> {
    cast_through_readings(observed, original)
        .or_else(|| cast_of_written_sign_cast(observed, original))
}

/// [`cast`] of an `original` that observes σ as written: rule W reads it
/// as σ's operand, but a conversion of the original as written names σ
/// itself (`count as uint32 as int32 as uint64` converts `count as uint32
/// as int32`, σ of the low word). The observed conversion is compared with
/// the conversion of the written term; the caller still checks the bounds
/// on the original. One match on the original's root and one conversion.
fn cast_of_written_sign_cast(
    observed: &IntegerTerm,
    original: &IntegerTerm,
) -> Option<crate::kernel::primitives::MachineIntegerFormat> {
    let (IntegerTerm::Machine(machine), IntegerTerm::Machine(written)) =
        (observed.value_read(), original)
    else {
        return None;
    };
    let (encoding, source, destination, _) = written.operand_view().cast()?;
    if encoding != MachineCastSpelling::Generic
        || source.format().bits() != 32
        || destination.format().bits() != 32
        || source == destination
    {
        return None;
    }
    if !representation::has_legacy_conversions(written.ty())
        || !representation::has_legacy_conversions(machine.ty())
    {
        return None;
    }
    if let crate::kernel::MachineOperandView::Shared(term) = written.operand_view() {
        let converted = term.checking_legacy_machine_conversion(written.ty(), machine.ty());
        let exact = matches_kernel(machine, &converted);
        let numeric = match converted.node() {
            crate::kernel::KernelTermNode::MachineCast {
                encoding: MachineCastSpelling::Generic,
                source,
                destination,
                operand,
            } if source.format().bits() == 32
                && destination.format().bits() == 32
                && source != destination =>
            {
                matches_kernel(machine, operand)
            }
            _ => exact,
        };
        return (exact || numeric).then(|| machine.ty().format());
    }
    let converted = convert_value(
        written.ty().value_from_term(written.value().clone()),
        machine.ty(),
    )?;
    (matches_converted_value(machine, &converted)
        || matches!(
            converted.numeric_value(),
            crate::kernel::integer_c_value!(term) if matches_word(machine, term)
        ))
    .then(|| machine.ty().format())
}

fn cast_through_readings(
    observed: &IntegerTerm,
    original: &IntegerTerm,
) -> Option<crate::kernel::primitives::MachineIntegerFormat> {
    if narrow_widening(observed, original) {
        let IntegerTerm::Machine(machine) = observed else {
            unreachable!("a widening observes a machine value");
        };
        return Some(machine.ty().format());
    }
    // Each side is read through its value relations (rule W): an
    // observation of σ is its operand read at the observation's format.
    let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) =
        (observed.value_read(), original.value_read())
    else {
        return None;
    };
    // A C conversion node over a 32-bit carrier whose type contains the
    // destination (`(uint16)(int32)w`) is transparent here: every value
    // of the destination has the same word in both types, so once the
    // inner carrier is shown below to be the source's value inside the
    // destination range, the conversion leaves that word unchanged.
    // The same bounds are still required.
    if let Some((MachineCastSpelling::Generic, through, destination, inner)) =
        machine.operand_view().cast()
        && destination == machine.ty()
        && through.format().bits() <= 32
        && through.format().contains(destination.format())
        && let Some(peeled) = inner.observe(machine.ty())
        && let Some(format) = cast(&peeled, original)
    {
        return Some(format);
    }
    if let crate::kernel::MachineOperandView::Shared(term) = operand.operand_view() {
        return cast_shared_operand(machine, operand, term);
    }
    if !operand.ty().accepts_cast_operand(operand.value()) {
        return None;
    }
    // Compare with the canonical conversion of the *observed* source.
    // A narrowing cast can discard an intermediate widening/reinterpretation
    // node, so inspecting only the outer node loses the source named by the
    // certificate. The canonical cast still has exactly its modulo semantics;
    // the bounds below establish that this conversion preserves the value.
    let converted =
        MachineTerm::machine_integer_cast(operand.ty(), machine.ty(), operand.value().clone());
    // An `int32` or `uint32` observation reads σ(x) as `x` (rule K2), so
    // the canonical conversion is compared by its word. Only σ: a narrow
    // widening's word (rule K8) is its operand only for a canonical
    // carrier, which `narrow_widening` above establishes; comparing by that
    // word here would accept any word merely tagged narrow.
    if matches_word(machine, &converted)
        || converted
            .sign_cast32_operand()
            .is_some_and(|(_, word)| matches_word(machine, word))
        || machine
            .operand_view()
            .literal()
            .and_then(|value| value.constant32())
            .is_some_and(|bits| converted.constant32() == Some(bits))
    {
        return Some(machine.ty().format());
    }
    // Ordinary C and the 32/64-bit modulo boundary retain legacy cast
    // terms. Compare against that same typed conversion policy, rather
    // than treating their numeric observation as a typed wide cast. The
    // explicit source bounds below remain mandatory for either spelling.
    let legacy_type = representation::has_legacy_conversions;
    // A narrowed byte/short value can retain the same 32-bit carrier, or
    // the low word of a 64-bit source, instead of an explicit narrowing
    // node. This direction still owes bounds on the word observation,
    // checked below against the narrow destination range; within it the
    // carrier is the destination's value, signed or unsigned. Bounds on
    // the narrow observation alone cannot justify interpreting an
    // arbitrary carrier as a word.
    let carrier = representation::low_word(operand.ty(), operand.value());
    if carrier
        .as_ref()
        .is_some_and(|word| matches_word(machine, word))
        && machine.ty().format().bits() < 32
    {
        return Some(machine.ty().format());
    }
    // Sub-word byte stores retain an unsigned low-bit mask in their
    // 32-bit carrier. Promoting that canonical carrier to a word keeps
    // its mathematical value. An arbitrary sub-word-tagged variable is
    // insufficient: its carrier has not established the narrow range.
    let narrow_unsigned =
        |ty: MachineIntegerType| ty.format().bits() < 32 && !ty.format().is_signed();
    let masked_unsigned_source = match (operand.ty(), operand.value()) {
        (ty, binary_term!(Bits32, BitwiseAnd, left, right)) if narrow_unsigned(ty) => {
            let mask = (1u32 << operand.ty().format().bits()) - 1;
            matches!(left.as_ref(), bits32_constant!(value) if constant_u32(*value) == mask)
                || matches!(right.as_ref(), bits32_constant!(value) if constant_u32(*value) == mask)
        }
        _ => false,
    };
    let promoted_unsigned_source = masked_unsigned_source && machine.ty().format().bits() == 32;
    if (legacy_type(operand.ty()) && legacy_type(machine.ty())) || promoted_unsigned_source {
        let legacy = convert_value(
            operand.ty().value_from_term(operand.value().clone()),
            machine.ty(),
        );
        if legacy.as_ref().is_some_and(|value| matches_converted_value(machine, value))
            || legacy.as_ref().is_some_and(|value| {
                matches!(
                    value.numeric_value(),
                    crate::kernel::integer_c_value!(term) if matches_word(machine, term)
                        || machine.operand_view().literal().and_then(|value| value.constant32()).is_some_and(|bits| term.constant32() == Some(bits))
                )
            })
        {
            return Some(machine.ty().format());
        }
    }
    // Typed byte stores/readback represent unsigned sub-word values by
    // retaining their low bits. This is the same modulo conversion from a
    // u32 word, with the source bounds still required below.
    if masked_narrowing(machine, operand) {
        return Some(machine.ty().format());
    }
    None
}

fn matches_word(machine: &crate::kernel::SharedMachineIntegerTerm, word: &MachineTerm) -> bool {
    match machine.operand_view() {
        crate::kernel::MachineOperandView::Legacy(actual) => actual == word,
        crate::kernel::MachineOperandView::Shared(_) => {
            let expected = crate::kernel::KernelTerm::retained_machine_operand(
                machine.ty(),
                crate::kernel::MachineOperandView::Legacy(word),
            );
            matches_kernel(machine, &expected)
        }
    }
}

fn matches_kernel(
    machine: &crate::kernel::SharedMachineIntegerTerm,
    word: &crate::kernel::KernelTerm,
) -> bool {
    // Compare written observations at one format. The numeric opaque-leaf key
    // is independent of the exact producer handle, and never peels a cast.
    let expected = crate::kernel::SharedMachineIntegerTerm::observe_shared(
        machine.ty(),
        word.with_machine_observation_type(machine.ty()),
    );
    let actual =
        crate::kernel::KernelTerm::retained_machine_operand(machine.ty(), machine.operand_view());
    let actual = crate::kernel::SharedMachineIntegerTerm::observe_shared(machine.ty(), actual);
    actual
        .zip(expected)
        .is_some_and(|(actual, expected)| actual == expected)
}

fn matches_converted_value(
    machine: &crate::kernel::SharedMachineIntegerTerm,
    value: &ProgramValue,
) -> bool {
    if let Some(literal) = machine.operand_view().literal() {
        return *value == machine.ty().value_from_term(literal);
    }
    matches!(value, crate::kernel::integer_c_value!(word) if value.program_type() == machine.ty().program_type() && matches_word(machine, word))
}

fn masked_narrowing(
    machine: &crate::kernel::SharedMachineIntegerTerm,
    operand: &crate::kernel::SharedMachineIntegerTerm,
) -> bool {
    use crate::kernel::MachineBinaryOp;
    if operand.ty() != MachineIntegerType::UInt32
        || machine.ty().format().bits() >= 32
        || machine.ty().format().is_signed()
    {
        return false;
    }
    let Some((format, MachineBinaryOp::BitwiseAnd, [left, right])) =
        machine.operand_view().binary()
    else {
        return false;
    };
    if format.format().bits() != 32 {
        return false;
    }
    let mask = (1u32 << machine.ty().format().bits()) - 1;
    let is_mask = |bits: crate::kernel::MachineOperandView<'_>| {
        bits.literal().and_then(|bits| bits.constant32()) == Some(mask)
    };
    let source = operand.operand_view().retain(MachineIntegerType::Int32);
    (is_mask(right) && left.retain(MachineIntegerType::Int32) == source)
        || (is_mask(left) && right.retain(MachineIntegerType::Int32) == source)
}

fn cast_shared_operand(
    machine: &crate::kernel::SharedMachineIntegerTerm,
    operand: &crate::kernel::SharedMachineIntegerTerm,
    term: &crate::kernel::KernelTerm,
) -> Option<crate::kernel::MachineIntegerFormat> {
    use crate::kernel::{KernelTermNode as N, MachineBinaryOp, MachineCastSpelling as E};
    let (source, destination) = (operand.ty(), machine.ty());
    if !operand.operand_view().accepts_cast_operand(source) {
        return None;
    }
    let converted = term.checking_machine_cast(source, destination);
    let sign_word = |word: &crate::kernel::KernelTerm| match word.node() {
        N::MachineCast {
            encoding: E::Generic,
            source,
            destination,
            operand,
        } if lower(*source, *destination, ConversionPolicy::Modular).lowering
            == ConversionLowering::SignCast =>
        {
            Some(operand.clone())
        }
        _ => None,
    };
    let same_literal = |word: &crate::kernel::KernelTerm| {
        let N::MachineLiteral(literal) = word.node() else {
            return false;
        };
        machine
            .operand_view()
            .literal()
            .and_then(|value| value.constant32())
            .is_some_and(|bits| literal.legacy_term().constant32() == Some(bits))
    };
    if matches_kernel(machine, &converted)
        || sign_word(&converted).is_some_and(|word| matches_kernel(machine, &word))
        || same_literal(&converted)
    {
        return Some(destination.format());
    }
    if destination.format().bits() < 32 {
        let low_word = match source.format().bits() {
            32 => Some(term.clone()),
            64 => Some(term.checking_low_word()),
            _ => None,
        };
        if low_word.is_some_and(|word| matches_kernel(machine, &word)) {
            return Some(destination.format());
        }
    }
    let promoted_unsigned = source.format().bits() < 32
        && !source.format().is_signed()
        && destination.format().bits() == 32
        && operand
            .operand_view()
            .binary()
            .is_some_and(|(format, op, children)| {
                format.format().bits() == 32
                    && op == MachineBinaryOp::BitwiseAnd
                    && children.into_iter().any(|child| {
                        child.literal().and_then(|bits| bits.constant32())
                            == Some((1u32 << source.format().bits()) - 1)
                    })
            });
    if (representation::has_legacy_conversions(source)
        && representation::has_legacy_conversions(destination))
        || promoted_unsigned
    {
        let converted = term.checking_legacy_machine_conversion(source, destination);
        if matches_kernel(machine, &converted)
            || sign_word(&converted).is_some_and(|word| matches_kernel(machine, &word))
            || same_literal(&converted)
        {
            return Some(destination.format());
        }
    }
    masked_narrowing(machine, operand).then_some(destination.format())
}

#[cfg(test)]
mod shared_operand_tests {
    use super::*;

    #[test]
    fn inspecting_an_integer_conversion_does_not_prepare_a_word() {
        use crate::kernel::{KernelTerm, KernelType, MachineOperandView, Variable};
        let _session = crate::kernel::VerificationSession::enter();
        let operand = KernelTerm::variable(KernelType::Integer, Variable(992_596));
        let root = KernelTerm::integer_to_machine(MachineIntegerType::Int64, operand).unwrap();
        let view = MachineOperandView::Shared(&root);
        assert_eq!(
            view.integer_conversion_destination(),
            Some(MachineIntegerType::Int64)
        );
        assert!(view.accepts_cast_operand(MachineIntegerType::Int64));
        assert!(!view.accepts_cast_operand(MachineIntegerType::UInt64));
        assert!(view.variable().is_none());
        assert!(view.literal().is_none());
        assert!(view.read().is_none());
        assert!(view.cast().is_none());
        assert!(!root.has_cached_machine_leaf());
        let observed = IntegerTerm::Machine(view.retain(MachineIntegerType::Int64));
        let (integer, destination) = integer_conversion(&observed).unwrap();
        assert_eq!(integer.as_ref(), &IntegerTerm::Variable(Variable(992_596)));
        assert_eq!(destination, MachineIntegerType::Int64);
    }

    fn legacy_cast_reference(
        observed: &IntegerTerm,
        original: &IntegerTerm,
    ) -> Option<crate::kernel::primitives::MachineIntegerFormat> {
        if narrow_widening(observed, original) {
            let IntegerTerm::Machine(machine) = observed else {
                unreachable!("a widening observes a machine value");
            };
            return Some(machine.ty().format());
        }
        // Each side is read through its value relations (rule W): an
        // observation of σ is its operand read at the observation's format.
        let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) =
            (observed.value_read(), original.value_read())
        else {
            return None;
        };
        // A C conversion node over a 32-bit carrier whose type contains the
        // destination (`(uint16)(int32)w`) is transparent here: every value
        // of the destination has the same word in both types, so once the
        // inner carrier is shown below to be the source's value inside the
        // destination range, the conversion leaves that word unchanged.
        // The same bounds are still required.
        if let MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: inner,
            from: through,
            to: destination,
        } = machine.value()
            && *destination == machine.ty()
            && through.format().bits() <= 32
            && through.format().contains(destination.format())
            && let Some(peeled) = IntegerTerm::from_machine(machine.ty(), inner.as_ref().clone())
            && let Some(format) = legacy_cast_reference(&peeled, original)
        {
            return Some(format);
        }
        if !operand.ty().accepts_cast_operand(operand.value()) {
            return None;
        }
        // Compare with the canonical conversion of the *observed* source.
        // A narrowing cast can discard an intermediate widening/reinterpretation
        // node, so inspecting only the outer node loses the source named by the
        // certificate. The canonical cast still has exactly its modulo semantics;
        // the bounds below establish that this conversion preserves the value.
        let converted =
            MachineTerm::machine_integer_cast(operand.ty(), machine.ty(), operand.value().clone());
        // An `int32` or `uint32` observation reads σ(x) as `x` (rule K2), so
        // the canonical conversion is compared by its word. Only σ: a narrow
        // widening's word (rule K8) is its operand only for a canonical
        // carrier, which `narrow_widening` above establishes; comparing by that
        // word here would accept any word merely tagged narrow.
        if machine.value() == &converted
            || converted
                .sign_cast32_operand()
                .is_some_and(|(_, word)| machine.value() == word)
            || machine
                .value()
                .constant32()
                .is_some_and(|bits| converted.constant32() == Some(bits))
        {
            return Some(machine.ty().format());
        }
        // Ordinary C and the 32/64-bit modulo boundary retain legacy cast
        // terms. Compare against that same typed conversion policy, rather
        // than treating their numeric observation as a typed wide cast. The
        // explicit source bounds below remain mandatory for either spelling.
        let legacy_type = representation::has_legacy_conversions;
        // A narrowed byte/short value can retain the same 32-bit carrier, or
        // the low word of a 64-bit source, instead of an explicit narrowing
        // node. This direction still owes bounds on the word observation,
        // checked below against the narrow destination range; within it the
        // carrier is the destination's value, signed or unsigned. Bounds on
        // the narrow observation alone cannot justify interpreting an
        // arbitrary carrier as a word.
        let carrier = representation::low_word(operand.ty(), operand.value());
        if carrier.as_ref() == Some(machine.value()) && machine.ty().format().bits() < 32 {
            return Some(machine.ty().format());
        }
        // Sub-word byte stores retain an unsigned low-bit mask in their
        // 32-bit carrier. Promoting that canonical carrier to a word keeps
        // its mathematical value. An arbitrary sub-word-tagged variable is
        // insufficient: its carrier has not established the narrow range.
        let narrow_unsigned =
            |ty: MachineIntegerType| ty.format().bits() < 32 && !ty.format().is_signed();
        let masked_unsigned_source = match (operand.ty(), operand.value()) {
            (ty, binary_term!(Bits32, BitwiseAnd, left, right)) if narrow_unsigned(ty) => {
                let mask = (1u32 << operand.ty().format().bits()) - 1;
                matches!(left.as_ref(), bits32_constant!(value) if constant_u32(*value) == mask)
                    || matches!(right.as_ref(), bits32_constant!(value) if constant_u32(*value) == mask)
            }
            _ => false,
        };
        let promoted_unsigned_source = masked_unsigned_source && machine.ty().format().bits() == 32;
        if (legacy_type(operand.ty()) && legacy_type(machine.ty())) || promoted_unsigned_source {
            let legacy = convert_value(
                operand.ty().value_from_term(operand.value().clone()),
                machine.ty(),
            );
            if legacy == Some(machine.ty().value_from_term(machine.value().clone()))
            || legacy.as_ref().is_some_and(|value| {
                matches!(
                    value.numeric_value(),
                    crate::kernel::integer_c_value!(term) if term == machine.value()
                        || machine.value().constant32().is_some_and(|bits| term.constant32() == Some(bits))
                )
            })
        {
            return Some(machine.ty().format());
        }
        }
        // Typed byte stores/readback represent unsigned sub-word values by
        // retaining their low bits. This is the same modulo conversion from a
        // u32 word, with the source bounds still required below.
        if operand.ty() == MachineIntegerType::UInt32
            && narrow_unsigned(machine.ty())
            && let binary_term!(Bits32, BitwiseAnd, left, right) = machine.value()
        {
            let mask = (1u32 << machine.ty().format().bits()) - 1;
            let matches = |value: &MachineTerm, bits: &MachineTerm| {
                value == operand.value() && bits.constant32() == Some(mask)
            };
            if matches(left, right) || matches(right, left) {
                return Some(machine.ty().format());
            }
        }
        None
    }

    #[test]
    fn shared_cast_rule_matches_legacy_candidates() {
        use crate::kernel::{MachineBinaryOp, MachineIntegerConstant, Variable};
        let _session = crate::kernel::VerificationSession::enter();
        for source in super::super::FORMATS {
            let mut words = vec![MachineTerm::Variable(Variable(982105))];
            if source.format().bits() < 128 {
                for op in [
                    MachineBinaryOp::Add,
                    MachineBinaryOp::Subtract,
                    MachineBinaryOp::BitwiseAnd,
                ] {
                    words.push(MachineTerm::Binary {
                        format: source,
                        op,
                        left: Box::new(words[0].clone()),
                        right: Box::new(
                            source
                                .constant_term(
                                    MachineIntegerConstant::from_integer(
                                        source.format(),
                                        &7.into(),
                                    )
                                    .unwrap(),
                                )
                                .unwrap(),
                        ),
                    });
                }
            }
            if matches!(source.format().bits(), 32 | 64) {
                words.push(MachineTerm::PureFunctionApplication {
                    name: "cast_opaque_word".to_string(),
                    arguments: vec![MachineTerm::Variable(Variable(982105))],
                });
                words.push(MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: source,
                    to: source,
                    value: Box::new(MachineTerm::Variable(Variable(982105))),
                });
            }
            for destination in super::super::FORMATS {
                for word in &words {
                    let original = IntegerTerm::from_machine(source, word.clone()).unwrap();
                    let mut candidates = vec![
                        word.clone(),
                        MachineTerm::Variable(Variable(982106)),
                        MachineTerm::machine_integer_cast(source, destination, word.clone()),
                        convert_term(source, destination, word.clone()),
                    ];
                    if let Some(low) = representation::low_word(source, word) {
                        candidates.push(low);
                    }
                    for candidate in candidates {
                        let Some(observed) =
                            IntegerTerm::from_machine(destination, candidate.clone())
                        else {
                            continue;
                        };
                        assert_eq!(
                            cast(&observed, &original),
                            legacy_cast_reference(&observed, &original),
                            "{source:?} -> {destination:?}: {word:?} => {candidate:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn shared_cast_construction_matches_legacy_format_matrix() {
        use crate::kernel::{
            KernelTermExport, KernelTermImport, MachineBinaryOp, MachineIntegerConstant, Variable,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for source in super::super::FORMATS {
            let mut words = vec![MachineTerm::Variable(Variable(982104))];
            let (min, max) = source.format().bounds();
            for n in [0.into(), 1.into(), min, max] {
                words.push(
                    source
                        .constant_term(
                            MachineIntegerConstant::from_integer(source.format(), &n).unwrap(),
                        )
                        .unwrap(),
                );
            }
            if source.format().bits() < 128 {
                for op in [
                    MachineBinaryOp::Add,
                    MachineBinaryOp::Subtract,
                    MachineBinaryOp::Multiply,
                ] {
                    for n in [0, 1, 7] {
                        words.push(MachineTerm::Binary {
                            format: source,
                            op,
                            left: Box::new(MachineTerm::Variable(Variable(982104))),
                            right: Box::new(
                                source
                                    .constant_term(
                                        MachineIntegerConstant::from_integer(
                                            source.format(),
                                            &n.into(),
                                        )
                                        .unwrap(),
                                    )
                                    .unwrap(),
                            ),
                        });
                    }
                }
            }
            if source == MachineIntegerType::UInt64 {
                for op in [MachineBinaryOp::Add, MachineBinaryOp::Subtract] {
                    words.push(MachineTerm::Binary {
                        format: source,
                        op,
                        left: Box::new(MachineTerm::uint64_constant(u64::MAX)),
                        right: Box::new(MachineTerm::uint64_constant(1)),
                    });
                }
                words.push(MachineTerm::Binary {
                    format: source,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::uint64_constant(7)),
                    right: Box::new(MachineTerm::Variable(Variable(982104))),
                });
            }
            for destination in super::super::FORMATS {
                for word in &words {
                    let shared = KernelTermImport::default().machine(source, word);
                    let cast = shared.checking_machine_cast(source, destination);
                    assert_eq!(
                        KernelTermExport::machine(&cast).unwrap(),
                        MachineTerm::machine_integer_cast(source, destination, word.clone()),
                        "generic {source:?} -> {destination:?}"
                    );
                    let cast = shared.checking_legacy_machine_conversion(source, destination);
                    let expected =
                        convert_value(source.value_from_term(word.clone()), destination).unwrap();
                    let crate::kernel::integer_c_value!(expected) = expected.numeric_value() else {
                        unreachable!()
                    };
                    assert_eq!(
                        &KernelTermExport::machine(&cast).unwrap(),
                        expected,
                        "legacy {source:?} -> {destination:?}: {word:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn narrow_widening_matches_retained_source_without_changing_cast_identity() {
        use crate::kernel::Variable;
        let _session = crate::kernel::VerificationSession::enter();
        let source = MachineIntegerType::Int8;
        let destination = MachineIntegerType::Int32;
        let word = MachineTerm::Variable(Variable(982102));
        let original = IntegerTerm::from_machine(source, word.clone()).unwrap();
        let other =
            IntegerTerm::from_machine(source, MachineTerm::Variable(Variable(982103))).unwrap();
        let widened = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: source,
            to: destination,
            value: Box::new(word),
        };
        let observed = IntegerTerm::from_machine(destination, widened).unwrap();
        assert!(narrow_widening(&observed, &original));
        assert!(!narrow_widening(&observed, &other));
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/machine_integer/conversion/tests.rs");
    }
}
