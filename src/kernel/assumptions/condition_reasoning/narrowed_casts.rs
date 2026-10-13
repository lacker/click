//! A narrowing integer conversion denotes its operand inside the
//! destination's range.
//!
//! C converts an integer to a narrower type, or between the two signednesses
//! of one width, modulo 2^N (`Bitvector32Term::MachineIntegerCast`; see
//! `narrow_integer_modulo`). When the operand's value lies in the
//! destination's range the conversion changes nothing, and its result is the
//! operand's own carrier: the same 32-bit word for a source that fits in 32
//! bits, the low word for a 64-bit source. This module states that identity
//! once, as the range conditions the context must decide, and both the smart
//! search and the checked proof reach it through the one
//! `PureFactContext::decide` (by way of `simplify_bitvector_under_assumptions`)
//! and `signed_interval` they already share.
//!
//! Soundness. Let `n` be the source value the operand carrier `v` denotes and
//! `[lo, hi]` the destination range, with the destination one or two bytes
//! wide. If `lo <= n <= hi` then `n mod 2^N` read in the destination is `n`,
//! and the destination's 32-bit carrier of `n` is `n` sign-extended to 32
//! bits. A source of at most 32 bits carries `n` exactly in its word (signed
//! sources sign-extend, unsigned ones zero-extend, and an unsigned 32-bit `n`
//! at most `hi < 2^31` has the same word); a 64-bit source's low word is `n`
//! because `|n| < 2^31`. The conditions below are exactly `lo <= n` (omitted
//! for an unsigned source, whose `n` is never below `lo <= 0`) and `n <= hi`
//! in the source's own comparison. Each is one memoized decision about the
//! operand; nothing else in the context is visited.
use super::*;
use crate::kernel::MachineIntegerType as Ty;

/// One bound a narrowing conversion's operand must meet to be unchanged.
/// Any one of `conditions` establishes it: a bound on a one- or two-byte
/// unsigned value may be stated in either order.
pub(in crate::kernel) struct NarrowedCastBound {
    pub(in crate::kernel) lower: bool,
    pub(in crate::kernel) conditions: Vec<ConditionTerm>,
}

/// The bounds under which `cast(value)` from `source` to `destination`
/// denotes its operand, and the carrier it then equals. A bound the source
/// type already meets is omitted: `(unsigned char)c` for a `signed char` `c`
/// needs only `c >= 0`. `None` for a conversion this rule does not cover: a
/// destination wider than two bytes, a 128-bit source, or a conversion
/// that cannot change the value (whose node `IntegerTerm::from_machine`
/// already unwraps).
pub(in crate::kernel) fn narrowed_cast_identity(
    value: &Bitvector32Term,
    source: Ty,
    destination: Ty,
) -> Option<(Vec<NarrowedCastBound>, Bitvector32Term)> {
    let bits = destination.format().bits();
    if !matches!(bits, 8 | 16)
        || destination.format().contains(source.format())
        || source.format().bits() > 64
    {
        return None;
    }
    let (lo, hi) = if destination.format().is_signed() {
        (-(1i64 << (bits - 1)), (1i64 << (bits - 1)) - 1)
    } else {
        (0, (1i64 << bits) - 1)
    };
    let source_signed = source.format().is_signed();
    let source_bits = source.format().bits();
    // Unsigned sources are never below `lo <= 0`; a signed source is below
    // it only when its own minimum is.
    let needs_lower = source_signed && -(1i128 << (source_bits - 1)) < i128::from(lo);
    let source_max = if source_signed {
        (1i128 << (source_bits - 1)) - 1
    } else {
        (1i128 << source_bits) - 1
    };
    let needs_upper = source_max > i128::from(hi);
    let word = |bound: i64| Bitvector32Term::Constant(bound as i32 as u32);
    // A constant operand keeps its comparison unfolded, so a checked
    // conversion that fails on it names the value and the endpoint rather
    // than `false`; a symbolic one keeps the established spelling.
    let constant = value.as_const().is_some()
        || value.int64_as_const().is_some()
        || value.uint64_as_const().is_some();
    let signed_ge = |v: &Bitvector32Term, b: i64| {
        if constant {
            ConditionTerm::Bitvector32SignedGreaterEqual(v.clone().into(), word(b).into())
        } else {
            ConditionTerm::signed_greater_equal(v.clone(), word(b))
        }
    };
    let signed_le = |v: &Bitvector32Term, b: i64| {
        if constant {
            ConditionTerm::Bitvector32SignedLessEqual(v.clone().into(), word(b).into())
        } else {
            ConditionTerm::signed_less_equal(v.clone(), word(b))
        }
    };
    let unsigned_le = |v: &Bitvector32Term, b: i64| match v.as_const() {
        Some(c) => ConditionTerm::Bitvector64UnsignedLessEqual(
            Bitvector32Term::UInt64Constant(u64::from(c)).into(),
            Bitvector32Term::UInt64Constant(b as u64).into(),
        ),
        None => ConditionTerm::unsigned_less_equal(v.clone(), word(b)),
    };
    let int64_ge = |v: &Bitvector32Term, b: i64| {
        if constant {
            ConditionTerm::Bitvector64SignedGreaterEqual(
                v.clone().into(),
                Bitvector32Term::Int64Constant(b).into(),
            )
        } else {
            ConditionTerm::int64_signed_greater_equal(v.clone(), Bitvector32Term::Int64Constant(b))
        }
    };
    let int64_le = |v: &Bitvector32Term, b: i64| {
        if constant {
            ConditionTerm::Bitvector64SignedLessEqual(
                v.clone().into(),
                Bitvector32Term::Int64Constant(b).into(),
            )
        } else {
            ConditionTerm::int64_signed_less_equal(v.clone(), Bitvector32Term::Int64Constant(b))
        }
    };
    let uint64_le = |v: &Bitvector32Term, b: i64| {
        if constant {
            ConditionTerm::Bitvector64UnsignedLessEqual(
                v.clone().into(),
                Bitvector32Term::UInt64Constant(b as u64).into(),
            )
        } else {
            ConditionTerm::uint64_less_equal(v.clone(), Bitvector32Term::UInt64Constant(b as u64))
        }
    };
    let value = value.clone();
    let (lower, upper, carrier) = match source {
        Ty::Int8 | Ty::Int16 | Ty::Int32 => (
            vec![signed_ge(&value, lo)],
            vec![signed_le(&value, hi)],
            value,
        ),
        // The word of a one- or two-byte unsigned value is its zero
        // extension, so the signed order reads the value itself.
        Ty::UInt8 | Ty::UInt16 => (
            Vec::new(),
            vec![signed_le(&value, hi), unsigned_le(&value, hi)],
            value,
        ),
        Ty::UInt32 => (Vec::new(), vec![unsigned_le(&value, hi)], value),
        Ty::Int64 => (
            vec![int64_ge(&value, lo)],
            vec![int64_le(&value, hi)],
            Bitvector32Term::uint32_from_64(value),
        ),
        Ty::UInt64 => (
            Vec::new(),
            vec![uint64_le(&value, hi)],
            Bitvector32Term::uint32_from_64(value),
        ),
        Ty::Int128 | Ty::UInt128 => return None,
    };
    let mut bounds = Vec::new();
    if needs_lower {
        bounds.push(NarrowedCastBound {
            lower: true,
            conditions: lower,
        });
    }
    if needs_upper {
        bounds.push(NarrowedCastBound {
            lower: false,
            conditions: upper,
        });
    }
    Some((bounds, carrier))
}

impl PureFactContext {
    /// The carrier a narrowing conversion equals when the context decides
    /// every range condition of [`narrowed_cast_identity`].
    pub(in crate::kernel) fn narrowed_cast_carrier(
        &self,
        term: &Bitvector32Term,
    ) -> Option<Bitvector32Term> {
        let Bitvector32Term::MachineIntegerCast {
            value,
            source,
            destination,
        } = term
        else {
            return None;
        };
        let (bounds, carrier) = narrowed_cast_identity(value, *source, *destination)?;
        bounds
            .iter()
            .all(|bound| {
                bound
                    .conditions
                    .iter()
                    .any(|condition| self.decide(condition) == Some(true))
            })
            .then_some(carrier)
    }

    /// The signed interval of a narrowing conversion of a source of at most
    /// 32 bits: the operand's interval moved by the multiple of 2^N that
    /// brings it into the destination range, when one multiple does for the
    /// whole interval, and otherwise the destination range.
    pub(super) fn narrowed_cast_interval(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        let Bitvector32Term::MachineIntegerCast {
            value,
            source,
            destination,
        } = term
        else {
            return None;
        };
        narrowed_cast_identity(value, *source, *destination)?;
        let bits = destination.format().bits();
        let modulus = 1i64 << bits;
        let lo = if destination.format().is_signed() {
            -(modulus / 2)
        } else {
            0
        };
        let full = (lo, lo + modulus - 1);
        let operand = match source {
            Ty::Int8 | Ty::Int16 | Ty::Int32 | Ty::UInt8 | Ty::UInt16 => {
                self.signed_interval(value)
            }
            // A nonnegative signed reading of a 32-bit unsigned word is its
            // value; a word whose sign bit may be set is not bounded here.
            Ty::UInt32 => self.signed_interval(value).filter(|(lower, _)| *lower >= 0),
            _ => None,
        };
        let Some((lower, upper)) = operand else {
            return Some(full);
        };
        let shift = (lower - lo).div_euclid(modulus);
        if (upper - lo).div_euclid(modulus) != shift {
            return Some(full);
        }
        Some((lower - shift * modulus, upper - shift * modulus))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MachineIntegerConstant, Variable};

    const NARROW: [Ty; 4] = [Ty::Int8, Ty::UInt8, Ty::Int16, Ty::UInt16];
    const SOURCES: [Ty; 8] = [
        Ty::Int8,
        Ty::UInt8,
        Ty::Int16,
        Ty::UInt16,
        Ty::Int32,
        Ty::UInt32,
        Ty::Int64,
        Ty::UInt64,
    ];

    fn constant(ty: Ty, value: i128) -> Option<Bitvector32Term> {
        ty.constant_term(MachineIntegerConstant::from_signed(ty.format(), value)?)
    }

    fn samples(ty: Ty) -> Vec<i128> {
        let (min, max) = ty.format().bounds();
        let (min, max) = (i128::try_from(min).unwrap(), i128::try_from(max).unwrap());
        let mut values = vec![min, min + 1, max - 1, max, 0, 1, -1];
        for edge in [128i128, 256, 32768, 65536, 1 << 31, 1 << 32] {
            values.extend([-edge - 1, -edge, -edge + 1, edge - 1, edge, edge + 1]);
        }
        values.retain(|value| (min..=max).contains(value));
        values
    }

    // Oracle: the bounds hold exactly when the source value is in the
    // destination range, and then the carrier is the modulo conversion,
    // which is the value itself.
    #[test]
    fn narrowed_cast_bounds_hold_exactly_inside_the_destination_range() {
        let _session = crate::kernel::VerificationSession::enter();
        for source in SOURCES {
            for destination in NARROW {
                if destination.format().contains(source.format()) {
                    assert!(
                        narrowed_cast_identity(
                            &Bitvector32Term::Variable(Variable(1)),
                            source,
                            destination
                        )
                        .is_none()
                    );
                    continue;
                }
                let (lo, hi) = destination.format().bounds();
                let (lo, hi) = (i128::try_from(lo).unwrap(), i128::try_from(hi).unwrap());
                for value in samples(source) {
                    let term = constant(source, value).unwrap();
                    let (bounds, carrier) =
                        narrowed_cast_identity(&term, source, destination).unwrap();
                    let holds = bounds.iter().all(|bound| {
                        bound.conditions.iter().any(|condition| {
                            PureFactContext::decide_intrinsically(condition) == Some(true)
                        })
                    });
                    let inside = (lo..=hi).contains(&value);
                    assert_eq!(holds, inside, "{source:?} -> {destination:?} at {value}");
                    if inside {
                        let converted =
                            Bitvector32Term::machine_integer_cast(source, destination, term);
                        assert_eq!(
                            PureFactContext::new().simplify_bitvector_under_assumptions(&carrier),
                            converted,
                            "{source:?} -> {destination:?} at {value}"
                        );
                        assert_eq!(converted, constant(destination, value).unwrap());
                    }
                }
            }
        }
    }

    // One byte, one name: C's conversion of an unsigned byte to `signed
    // char` is the signed read of that byte, and converting the signed read
    // back is the byte itself.
    #[test]
    fn byte_conversions_are_the_one_byte_one_name_terms() {
        let _session = crate::kernel::VerificationSession::enter();
        let byte = Bitvector32Term::Variable(Variable(170_010));
        let signed = Bitvector32Term::machine_integer_cast(Ty::UInt8, Ty::Int8, byte.clone());
        assert_eq!(signed, Bitvector32Term::signed_byte(byte.clone()));
        assert_eq!(
            Bitvector32Term::machine_integer_cast(Ty::Int8, Ty::UInt8, signed),
            byte
        );
    }

    #[test]
    fn a_narrowed_cast_is_its_operand_only_when_the_context_proves_the_range() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(170_001));
        let byte = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::UInt8, x.clone());
        let is_x = ConditionTerm::equal(byte.clone(), x.clone());
        let at_least_zero =
            ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0));
        let at_most_255 =
            ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(255));
        let at_most_256 =
            ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(256));
        let bounded = PureFactContext::new()
            .assume_condition(at_least_zero.clone(), true)
            .assume_condition(at_most_255, true);
        assert_eq!(bounded.decide(&is_x), Some(true));
        // One bound short, or a bound one past the range, is not enough.
        let lower_only = PureFactContext::new().assume_condition(at_least_zero.clone(), true);
        assert_ne!(lower_only.decide(&is_x), Some(true));
        let past = PureFactContext::new()
            .assume_condition(at_least_zero, true)
            .assume_condition(at_most_256, true);
        assert_ne!(past.decide(&is_x), Some(true));
        // A known value outside the range converts to its residue.
        let wrapped = PureFactContext::new().assume_condition(
            ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(300)),
            true,
        );
        assert_eq!(
            wrapped.decide(&ConditionTerm::equal(
                byte.clone(),
                Bitvector32Term::Constant(44)
            )),
            Some(true)
        );
        assert_eq!(
            wrapped.decide(&ConditionTerm::equal(byte, Bitvector32Term::Constant(300))),
            Some(false)
        );
    }

    // An equality naming a conversion whose operand the context already
    // bounds also relates the name to the operand; an operand bounded only
    // past the range is not related, and a known constant folds.
    #[test]
    fn an_equality_with_an_in_range_conversion_relates_its_operand() {
        let _session = crate::kernel::VerificationSession::enter();
        let y = Bitvector32Term::Variable(Variable(170_020));
        let result = Bitvector32Term::Variable(Variable(170_021));
        let byte = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::UInt8, y.clone());
        let bounded = |upper: u32| {
            PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), y.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(y.clone(), Bitvector32Term::Constant(upper)),
                    true,
                )
                .assume_condition(ConditionTerm::equal(result.clone(), byte.clone()), true)
        };
        let same = ConditionTerm::equal(result.clone(), y.clone());
        assert_eq!(bounded(255).decide(&same), Some(true));
        assert_ne!(bounded(300).decide(&same), Some(true));
        let known = PureFactContext::new()
            .assume_condition(
                ConditionTerm::equal(y.clone(), Bitvector32Term::Constant(44)),
                true,
            )
            .assume_condition(ConditionTerm::equal(result.clone(), byte.clone()), true);
        assert_eq!(known.decide(&same), Some(true));
        assert_eq!(
            known.decide(&ConditionTerm::equal(
                result.clone(),
                Bitvector32Term::Constant(44)
            )),
            Some(true)
        );
        let wrapped = PureFactContext::new()
            .assume_condition(
                ConditionTerm::equal(y.clone(), Bitvector32Term::Constant(300)),
                true,
            )
            .assume_condition(ConditionTerm::equal(result.clone(), byte), true);
        assert_ne!(wrapped.decide(&same), Some(true));
    }

    #[test]
    fn a_narrowed_cast_interval_moves_one_residue_class_or_covers_the_range() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(170_002));
        let signed = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::Int8, x.clone());
        let within = |lower: i32, upper: i32| {
            PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_greater_equal(
                        x.clone(),
                        Bitvector32Term::Constant(lower as u32),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(
                        x.clone(),
                        Bitvector32Term::Constant(upper as u32),
                    ),
                    true,
                )
        };
        assert_eq!(within(128, 255).signed_interval(&signed), Some((-128, -1)));
        assert_eq!(within(-20, 20).signed_interval(&signed), Some((-20, 20)));
        assert_eq!(within(100, 200).signed_interval(&signed), Some((-128, 127)));
        assert_eq!(
            PureFactContext::new().signed_interval(&signed),
            Some((-128, 127))
        );
    }

    #[test]
    fn cited_bounds_reduce_a_narrowed_cast_and_missing_ones_do_not() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(170_003));
        let short = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::Int16, x.clone());
        let goal = Proposition::ConditionIs(ConditionTerm::equal(short, x.clone()), true);
        let lower = ConditionTerm::signed_greater_equal(
            x.clone(),
            Bitvector32Term::Constant(-32768i32 as u32),
        );
        let upper = ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(32767));
        let guards = crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(&goal);
        assert!(guards.contains(&lower) && guards.contains(&upper));
        let rewrite = |conditions: &std::collections::HashMap<ConditionTerm, bool>| {
            crate::kernel::proof::term_rewrite::TermRewrite::for_conditions(conditions)
                .proposition(&goal)
        };
        let both = std::collections::HashMap::from([(lower.clone(), true), (upper.clone(), true)]);
        assert_eq!(
            rewrite(&both),
            Proposition::ConditionIs(ConditionTerm::equal(x.clone(), x.clone()), true)
        );
        let one = std::collections::HashMap::from([(lower, true)]);
        assert_eq!(rewrite(&one), goal);
    }

    // The rule decides two bounds about the operand and visits nothing else:
    // its work does not grow with unrelated facts in the context.
    #[test]
    fn narrowed_cast_identity_work_is_independent_of_unrelated_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(170_004));
        let byte = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::UInt8, x.clone());
        let mut work = Vec::new();
        for unrelated in [4u32, 64, 1024] {
            let mut context = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(255)),
                    true,
                );
            for index in 0..unrelated {
                context = context.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(171_000 + u64::from(index))),
                        Bitvector32Term::Constant(index),
                    ),
                    true,
                );
            }
            let (carrier, cost) = crate::instrumentation::measure_deterministic_work(|| {
                context.narrowed_cast_carrier(&byte)
            });
            assert_eq!(carrier, Some(x.clone()));
            // Filing an equality that names the conversion relates it to
            // its operand with the same bounded decisions.
            let name = Bitvector32Term::Variable(Variable(170_005));
            let (related, filing) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .clone()
                    .assume_condition(ConditionTerm::equal(name.clone(), byte.clone()), true)
            });
            assert_eq!(
                related.decide(&ConditionTerm::equal(name, x.clone())),
                Some(true)
            );
            work.push(cost.saturating_add(filing));
        }
        assert!(
            work[2] <= work[0] * 2 + 16,
            "narrowed cast identity work grew with unrelated facts: {work:?}"
        );
    }
}
