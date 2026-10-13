//! A modulo integral cast preserves its mathematical value inside the
//! destination range. The certificate names exactly two source bounds.

use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, Proposition, SharedIntegerTerm};

fn order(proposition: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) => Some((a, b)),
        _ => None,
    }
}

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    let invalid = || Error::InvalidIntegerCastIdentity(node);
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 2 {
        return Err(invalid());
    }
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = result else {
        return Err(invalid());
    };
    fn cast(
        observed: &IntegerTerm,
        original: &IntegerTerm,
    ) -> Option<crate::kernel::primitives::MachineIntegerFormat> {
        let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) = (observed, original)
        else {
            return None;
        };
        // A C conversion node over a 32-bit carrier whose type contains the
        // destination (`(uint16)(int32)w`) is transparent here: every value
        // of the destination has the same word in both types, so once the
        // inner carrier is shown below to be the source's value inside the
        // destination range, the conversion leaves that word unchanged.
        // The same bounds are still required.
        if let Bitvector32Term::MachineIntegerCast {
            value: inner,
            source: through,
            destination,
        } = machine.value()
            && *destination == machine.ty()
            && through.format().bits() <= 32
            && through.format().contains(destination.format())
            && let Some(peeled) = IntegerTerm::from_machine(machine.ty(), inner.as_ref().clone())
            && let Some(format) = cast(&peeled, original)
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
        let converted = Bitvector32Term::machine_integer_cast(
            operand.ty(),
            machine.ty(),
            operand.value().clone(),
        );
        if machine.value() == &converted {
            return Some(machine.ty().format());
        }
        // Ordinary C and the 32/64-bit modulo boundary retain legacy cast
        // terms. Compare against that same typed conversion policy, rather
        // than treating their numeric observation as a typed wide cast. The
        // explicit source bounds below remain mandatory for either spelling.
        let legacy_type = |ty| {
            matches!(
                ty,
                crate::kernel::MachineIntegerType::Int32
                    | crate::kernel::MachineIntegerType::UInt32
                    | crate::kernel::MachineIntegerType::Int64
                    | crate::kernel::MachineIntegerType::UInt64
            )
        };
        // A narrowed byte/short value can retain the same 32-bit carrier, or
        // the low word of a 64-bit source, instead of an explicit narrowing
        // node. This direction still owes bounds on the word observation,
        // checked below against the narrow destination range; within it the
        // carrier is the destination's value, signed or unsigned. Bounds on
        // the narrow observation alone cannot justify interpreting an
        // arbitrary carrier as a word.
        let carrier = match operand.ty() {
            crate::kernel::MachineIntegerType::Int32
            | crate::kernel::MachineIntegerType::UInt32 => Some(operand.value().clone()),
            crate::kernel::MachineIntegerType::Int64
            | crate::kernel::MachineIntegerType::UInt64 => {
                Some(Bitvector32Term::uint32_from_64(operand.value().clone()))
            }
            _ => None,
        };
        if carrier.as_ref() == Some(machine.value())
            && matches!(
                machine.ty(),
                crate::kernel::MachineIntegerType::Int8
                    | crate::kernel::MachineIntegerType::UInt8
                    | crate::kernel::MachineIntegerType::Int16
                    | crate::kernel::MachineIntegerType::UInt16
            )
        {
            return Some(machine.ty().format());
        }
        // Sub-word byte stores retain an unsigned low-bit mask in their
        // 32-bit carrier. Promoting that canonical carrier to a word keeps
        // its mathematical value. An arbitrary sub-word-tagged variable is
        // insufficient: its carrier has not established the narrow range.
        let masked_unsigned_source = match (operand.ty(), operand.value()) {
            (
                crate::kernel::MachineIntegerType::UInt8
                | crate::kernel::MachineIntegerType::UInt16,
                Bitvector32Term::BitwiseAnd(left, right),
            ) => {
                let mask = (1u32 << operand.ty().format().bits()) - 1;
                matches!(left.as_ref(), Bitvector32Term::Constant(value) if *value == mask)
                    || matches!(right.as_ref(), Bitvector32Term::Constant(value) if *value == mask)
            }
            _ => false,
        };
        let promoted_unsigned_source = masked_unsigned_source
            && matches!(
                machine.ty(),
                crate::kernel::MachineIntegerType::Int32
                    | crate::kernel::MachineIntegerType::UInt32
            );
        if (legacy_type(operand.ty()) && legacy_type(machine.ty())) || promoted_unsigned_source {
            let legacy = machine
                .ty()
                .convert_modulo_value(operand.ty().value_from_term(operand.value().clone()));
            if legacy == Some(machine.ty().value_from_term(machine.value().clone())) {
                return Some(machine.ty().format());
            }
        }
        // Typed byte stores/readback represent unsigned sub-word values by
        // retaining their low bits. This is the same modulo conversion from a
        // u32 word, with the source bounds still required below.
        if operand.ty() == crate::kernel::MachineIntegerType::UInt32
            && matches!(
                machine.ty(),
                crate::kernel::MachineIntegerType::UInt8
                    | crate::kernel::MachineIntegerType::UInt16
            )
            && let Bitvector32Term::BitwiseAnd(left, right) = machine.value()
        {
            let mask = (1u32 << machine.ty().format().bits()) - 1;
            let matches = |value: &Bitvector32Term, bits: &Bitvector32Term| {
                value == operand.value() && bits == &Bitvector32Term::Constant(mask)
            };
            if matches(left, right) || matches(right, left) {
                return Some(machine.ty().format());
            }
        }
        None
    }
    let (original, destination) = if let Some(destination) = cast(a, b) {
        (b, destination)
    } else if let Some(destination) = cast(b, a) {
        (a, destination)
    } else {
        return Err(invalid());
    };
    let lower = premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?;
    let upper = premises
        .get(bounds[1])
        .ok_or(Error::InvalidPremise(bounds[1]))?;
    let (lo, operand) = order(lower).ok_or_else(invalid)?;
    let (other_operand, hi) = order(upper).ok_or_else(invalid)?;
    if operand != original || other_operand != original {
        return Err(invalid());
    }
    let (lo, hi) = lo.as_const().zip(hi.as_const()).ok_or_else(invalid)?;
    // Endpoints supplied by the certificate may have arbitrary bit length.
    let work = usize::try_from(lo.bits())
        .unwrap_or(usize::MAX)
        .saturating_add(usize::try_from(hi.bits()).unwrap_or(usize::MAX))
        .saturating_add(512);
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        return Err(Error::WorkLimitExceeded);
    }
    let (min, max) = destination.bounds();
    if lo > hi || lo < &min || hi > &max {
        return Err(invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };
    use crate::kernel::{MachineIntegerConstant, MachineIntegerType as Ty, Variable};
    use num_bigint::BigInt;

    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(a, b), true)
    }
    fn inputs(source: Ty, destination: Ty) -> (Vec<Proposition>, Proposition) {
        let value = Bitvector32Term::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(source, value.clone()).unwrap();
        let cast = Bitvector32Term::machine_integer_cast(source, destination, value);
        let observed = IntegerTerm::from_machine(destination, cast).unwrap();
        let (lo, hi) = destination.format().bounds();
        (
            vec![
                le(IntegerTerm::constant(lo), original.clone()),
                le(original.clone(), IntegerTerm::constant(hi)),
            ],
            Proposition::ConditionIs(ConditionTerm::integer_equal(observed, original), true),
        )
    }
    fn certificate(result: Proposition, bounds: Vec<usize>) -> SpecialArithmeticCertificate {
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerCastIdentity { bounds, result }],
            conclusion: 0,
        }
    }

    #[test]
    fn integer_cast_identity_promotes_only_canonical_unsigned_subword_carriers() {
        let word = Bitvector32Term::Variable(Variable(168_010));
        let observation = |ty, value| IntegerTerm::from_machine(ty, value).unwrap();
        let claim = |source, destination, carrier: Bitvector32Term| {
            let original = observation(source, carrier.clone());
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(observation(destination, carrier), original.clone()),
                true,
            );
            let premises = vec![
                le(IntegerTerm::constant_i64(0), original.clone()),
                le(original, IntegerTerm::constant_i64(65535)),
            ];
            (premises, goal)
        };
        for source in [Ty::UInt8, Ty::UInt16] {
            let mask = (1u32 << source.format().bits()) - 1;
            for destination in [Ty::Int32, Ty::UInt32] {
                for reversed in [false, true] {
                    let carrier = if reversed {
                        Bitvector32Term::bitwise_and(Bitvector32Term::Constant(mask), word.clone())
                    } else {
                        Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask))
                    };
                    let (mut premises, goal) = claim(source, destination, carrier);
                    let mut costs = Vec::new();
                    for ambient in [0, 16, 64, 256, 1024] {
                        premises.resize_with(ambient + 2, || {
                            Proposition::ConditionIs(
                                ConditionTerm::Variable(Variable(168_011)),
                                true,
                            )
                        });
                        let cert = certificate(goal.clone(), vec![0, 1]);
                        let (result, work) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                cert.check(&goal, &premises)
                            });
                        result.unwrap();
                        costs.push(work);
                        assert!(
                            certificate(goal.clone(), vec![0, 2])
                                .check(&goal, &premises)
                                .is_err()
                        );
                    }
                    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
                }
                for carrier in [
                    word.clone(),
                    Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask + 1)),
                ] {
                    let (premises, goal) = claim(source, destination, carrier);
                    assert!(
                        certificate(goal.clone(), vec![0, 1])
                            .check(&goal, &premises)
                            .is_err()
                    );
                }
            }
        }
        // A signed sub-word observation of 0xffff is negative, while a raw
        // word promotion of that mask is positive. Never admit that retagging.
        let (premises, goal) = claim(
            Ty::Int16,
            Ty::Int32,
            Bitvector32Term::bitwise_and(word, Bitvector32Term::Constant(65535)),
        );
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn unsigned_subword_read_observations_require_bounds_on_the_word() {
        let carrier = Bitvector32Term::Variable(Variable(168_012));
        for source in [Ty::Int32, Ty::UInt32] {
            for destination in [Ty::UInt8, Ty::UInt16] {
                let original = IntegerTerm::from_machine(source, carrier.clone()).unwrap();
                let observed = IntegerTerm::from_machine(destination, carrier.clone()).unwrap();
                let goal = Proposition::ConditionIs(
                    ConditionTerm::integer_equal(observed.clone(), original.clone()),
                    true,
                );
                let (_, maximum) = destination.format().bounds();
                let bounds = |value: IntegerTerm, upper: BigInt| {
                    vec![
                        le(IntegerTerm::constant_i64(0), value.clone()),
                        le(value, IntegerTerm::constant(upper)),
                    ]
                };
                let cert = certificate(goal.clone(), vec![0, 1]);
                cert.check(&goal, &bounds(original.clone(), maximum.clone()))
                    .unwrap();
                // A bound on the byte observation cannot grant the word's
                // interpretation, and a word outside the byte range wraps.
                assert!(
                    cert.check(&goal, &bounds(observed, maximum.clone()))
                        .is_err()
                );
                assert!(cert.check(&goal, &bounds(original, &maximum + 1)).is_err());
                for number in [BigInt::from(0), maximum.clone(), &maximum + 1] {
                    let value =
                        MachineIntegerConstant::from_integer(source.format(), &number).unwrap();
                    assert_eq!(
                        value.convert_modulo(destination.format()).to_integer() == number,
                        number <= maximum,
                    );
                }
            }
        }
    }

    #[test]
    fn narrowed_subword_carriers_require_destination_bounds_on_the_source() {
        let word = Bitvector32Term::Variable(Variable(168_013));
        let wide = Bitvector32Term::Variable(Variable(168_014));
        for (source, original_carrier, carrier) in [
            (Ty::Int32, word.clone(), word.clone()),
            (Ty::UInt32, word.clone(), word.clone()),
            (
                Ty::Int64,
                wide.clone(),
                Bitvector32Term::uint32_from_64(wide.clone()),
            ),
            (
                Ty::UInt64,
                wide.clone(),
                Bitvector32Term::uint32_from_64(wide.clone()),
            ),
        ] {
            for destination in [Ty::Int8, Ty::UInt8, Ty::Int16, Ty::UInt16] {
                let original = IntegerTerm::from_machine(source, original_carrier.clone()).unwrap();
                let observed = IntegerTerm::from_machine(destination, carrier.clone()).unwrap();
                let goal = Proposition::ConditionIs(
                    ConditionTerm::integer_equal(observed.clone(), original.clone()),
                    true,
                );
                let (minimum, maximum) = destination.format().bounds();
                let bounds = |value: IntegerTerm, lower: BigInt, upper: BigInt| {
                    vec![
                        le(IntegerTerm::constant(lower), value.clone()),
                        le(value, IntegerTerm::constant(upper)),
                    ]
                };
                let cert = certificate(goal.clone(), vec![0, 1]);
                cert.check(
                    &goal,
                    &bounds(original.clone(), minimum.clone(), maximum.clone()),
                )
                .unwrap();
                assert!(
                    cert.check(&goal, &bounds(observed, minimum.clone(), maximum.clone()))
                        .is_err()
                );
                assert!(
                    cert.check(
                        &goal,
                        &bounds(original.clone(), minimum.clone(), &maximum + 1)
                    )
                    .is_err()
                );
                assert!(
                    cert.check(
                        &goal,
                        &bounds(original.clone(), &minimum - 1, maximum.clone())
                    )
                    .is_err()
                );
                // A 64-bit source is narrowed only through its low word.
                if source.format().bits() == 64 {
                    let untruncated = IntegerTerm::from_machine(destination, wide.clone()).unwrap();
                    let goal = Proposition::ConditionIs(
                        ConditionTerm::integer_equal(untruncated, original.clone()),
                        true,
                    );
                    assert!(
                        certificate(goal.clone(), vec![0, 1])
                            .check(&goal, &bounds(original, minimum, maximum))
                            .is_err()
                    );
                }
            }
        }
    }

    #[test]
    fn integer_cast_identity_matches_exact_modulo_oracle_at_destination_boundaries() {
        for source in [Ty::Int128, Ty::UInt128] {
            for destination in [
                Ty::Int8,
                Ty::UInt8,
                Ty::Int16,
                Ty::UInt16,
                Ty::Int32,
                Ty::UInt32,
                Ty::Int64,
                Ty::UInt64,
            ] {
                let (premises, goal) = inputs(source, destination);
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &premises)
                        .is_ok()
                );
                let (min, max) = destination.format().bounds();
                for number in [
                    min.clone() - 1,
                    min.clone(),
                    BigInt::from(0),
                    max.clone(),
                    max.clone() + 1,
                ] {
                    let Some(value) =
                        MachineIntegerConstant::from_integer(source.format(), &number)
                    else {
                        continue;
                    };
                    let bits = BigInt::from(1u8) << destination.format().bits();
                    let mut expected = ((&number % &bits) + &bits) % &bits;
                    if destination.format().is_signed() && expected > max {
                        expected -= bits;
                    }
                    assert_eq!(
                        value.convert_modulo(destination.format()).to_integer(),
                        expected
                    );
                    assert_eq!(expected == number, min <= number && number <= max);
                }
                let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = &goal
                else {
                    unreachable!()
                };
                let reversed = Proposition::ConditionIs(
                    ConditionTerm::integer_equal(b.as_ref().clone(), a.as_ref().clone()),
                    true,
                );
                assert!(
                    certificate(reversed.clone(), vec![0, 1])
                        .check(&reversed, &premises)
                        .is_ok()
                );
            }
        }
    }

    #[test]
    fn integer_cast_identity_checks_legacy_conversions_and_rejects_wrong_carriers() {
        let types = [Ty::Int32, Ty::UInt32, Ty::Int64, Ty::UInt64];
        let value = Bitvector32Term::Variable(Variable(168_001));
        for source in types {
            for destination in types {
                let original = IntegerTerm::from_machine(source, value.clone()).unwrap();
                let converted = destination
                    .convert_modulo_value(source.value_from_term(value.clone()))
                    .unwrap();
                let converted = match converted {
                    crate::kernel::integer64_c_value!(v) => v,
                    _ => panic!("wrong carrier"),
                };
                let observed = IntegerTerm::from_machine(destination, converted.clone()).unwrap();
                let goal = Proposition::ConditionIs(
                    ConditionTerm::integer_equal(observed, original.clone()),
                    true,
                );
                let (lo, hi) = destination.format().bounds();
                let premises = vec![
                    le(IntegerTerm::constant(lo.clone()), original.clone()),
                    le(original.clone(), IntegerTerm::constant(hi.clone())),
                ];
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .unwrap_or_else(|e| panic!("{source:?}/{destination:?}: {e:?}"));
                for wrong in [
                    vec![
                        le(IntegerTerm::constant(lo - 1), original.clone()),
                        premises[1].clone(),
                    ],
                    vec![
                        premises[0].clone(),
                        le(original.clone(), IntegerTerm::constant(hi + 1)),
                    ],
                    vec![premises[1].clone(), premises[0].clone()],
                ] {
                    assert!(
                        certificate(goal.clone(), vec![0, 1])
                            .check(&goal, &wrong)
                            .is_err()
                    );
                }
                if source != destination {
                    let unrelated = Bitvector32Term::Variable(Variable(168_002));
                    let wrong = Proposition::ConditionIs(
                        ConditionTerm::integer_equal(
                            IntegerTerm::from_machine(destination, unrelated).unwrap(),
                            original.clone(),
                        ),
                        true,
                    );
                    assert!(
                        certificate(wrong.clone(), vec![0, 1])
                            .check(&wrong, &premises)
                            .is_err()
                    );
                }
            }
        }
    }

    #[test]
    fn integer_cast_identity_checks_normalized_nested_conversions() {
        let variable = Bitvector32Term::Variable(Variable(168_001));
        for (source, intermediate, destination) in [
            (Ty::Int32, Ty::UInt32, Ty::UInt16),
            (Ty::UInt32, Ty::Int32, Ty::UInt16),
            (Ty::UInt8, Ty::UInt32, Ty::UInt16),
            (Ty::Int128, Ty::UInt64, Ty::Int32),
        ] {
            let widened =
                Bitvector32Term::machine_integer_cast(source, intermediate, variable.clone());
            let narrowed =
                Bitvector32Term::machine_integer_cast(intermediate, destination, widened.clone());
            let original = IntegerTerm::from_machine(intermediate, widened).unwrap();
            let observed = IntegerTerm::from_machine(destination, narrowed).unwrap();
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(observed.clone(), original.clone()),
                true,
            );
            let premises = vec![
                le(IntegerTerm::constant(0.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(255.into())),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .is_ok()
            );
            let wrong_source = vec![
                le(
                    IntegerTerm::constant(0.into()),
                    IntegerTerm::var(Variable(168_002)),
                ),
                premises[1].clone(),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &wrong_source)
                    .is_err()
            );
            // The bounds must describe the source observation in the equality,
            // even when the constructor has removed that intermediate cast.
            let underlying = IntegerTerm::from_machine(source, variable.clone()).unwrap();
            if underlying == original {
                continue;
            }
            let wrong_goal =
                Proposition::ConditionIs(ConditionTerm::integer_equal(observed, underlying), true);
            assert!(
                certificate(wrong_goal.clone(), vec![0, 1])
                    .check(&wrong_goal, &premises)
                    .is_err()
            );
        }

        // Widening after a truncation cannot be treated as a direct cast of the
        // pre-truncation value, even if that value fits the final destination.
        let truncated =
            Bitvector32Term::machine_integer_cast(Ty::UInt32, Ty::UInt8, variable.clone());
        let widened = Bitvector32Term::machine_integer_cast(Ty::UInt8, Ty::UInt16, truncated);
        let original = IntegerTerm::from_machine(Ty::UInt32, variable).unwrap();
        let observed = IntegerTerm::from_machine(Ty::UInt16, widened).unwrap();
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(observed, original.clone()),
            true,
        );
        let premises = vec![
            le(IntegerTerm::constant(0.into()), original.clone()),
            le(original, IntegerTerm::constant(65535.into())),
        ];
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn integer_cast_identity_checks_unsigned_byte_readback_masks() {
        let value = Bitvector32Term::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(Ty::UInt32, value.clone()).unwrap();
        for destination in [Ty::UInt8, Ty::UInt16] {
            let mask = (1u32 << destination.format().bits()) - 1;
            let goal_with_mask = |mask| {
                let narrowed = Bitvector32Term::BitwiseAnd(
                    Box::new(value.clone()),
                    Box::new(Bitvector32Term::Constant(mask)),
                );
                let observed = IntegerTerm::from_machine(destination, narrowed).unwrap();
                Proposition::ConditionIs(
                    ConditionTerm::integer_equal(observed, original.clone()),
                    true,
                )
            };
            let goal = goal_with_mask(mask);
            let premises = vec![
                le(IntegerTerm::constant(0.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(mask.into())),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .is_ok()
            );
            for incorrect in [mask - 1, mask + 1, 0, u32::MAX] {
                let wrong = goal_with_mask(incorrect);
                assert!(
                    certificate(wrong.clone(), vec![0, 1])
                        .check(&wrong, &premises)
                        .is_err()
                );
            }
            let outside = vec![
                premises[0].clone(),
                le(
                    original.clone(),
                    IntegerTerm::constant((u64::from(mask) + 1).into()),
                ),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &outside)
                    .is_err()
            );
            let wrong_source = vec![
                premises[0].clone(),
                le(
                    IntegerTerm::var(Variable(168_002)),
                    IntegerTerm::constant(mask.into()),
                ),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &wrong_source)
                    .is_err()
            );
            for number in [0, 1, mask - 1, mask, mask + 1, i32::MAX as u32, u32::MAX] {
                let converted = match destination {
                    Ty::UInt8 => u32::from(number as u8),
                    Ty::UInt16 => u32::from(number as u16),
                    _ => unreachable!(),
                };
                assert_eq!(converted, number & mask);
                assert_eq!(converted == number, number <= mask);
            }
        }
    }

    #[test]
    fn integer_cast_identity_refuses_missing_wrong_and_out_of_range_bounds() {
        let (premises, goal) = inputs(Ty::Int128, Ty::Int64);
        for bounds in [
            vec![],
            vec![0],
            vec![1],
            vec![0, 0],
            vec![1, 0],
            vec![0, 1, 1],
            vec![0, 2],
        ] {
            assert!(
                certificate(goal.clone(), bounds)
                    .check(&goal, &premises)
                    .is_err()
            );
        }
        let original =
            IntegerTerm::from_machine(Ty::Int128, Bitvector32Term::Variable(Variable(168_001)))
                .unwrap();
        let (lo, hi) = Ty::Int64.format().bounds();
        for altered in [
            vec![
                le(IntegerTerm::constant(lo.clone() - 1), original.clone()),
                premises[1].clone(),
            ],
            vec![
                premises[0].clone(),
                le(original.clone(), IntegerTerm::constant(hi.clone() + 1)),
            ],
            vec![
                le(IntegerTerm::constant(5.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(4.into())),
            ],
            vec![
                le(
                    IntegerTerm::constant(lo.clone()),
                    IntegerTerm::var(Variable(168_002)),
                ),
                premises[1].clone(),
            ],
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(IntegerTerm::constant(lo), original.clone()),
                    false,
                ),
                premises[1].clone(),
            ],
        ] {
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &altered)
                    .is_err()
            );
        }
        let stronger = vec![
            le(IntegerTerm::constant((-3).into()), original.clone()),
            le(original, IntegerTerm::constant(4.into())),
        ];
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&goal, &stronger)
                .is_ok()
        );
        let (_, other_goal) = inputs(Ty::UInt128, Ty::Int64);
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&other_goal, &premises)
                .is_err()
        );
        assert!(
            certificate(other_goal.clone(), vec![0, 1])
                .check(&other_goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn integer_cast_identity_rejects_forged_format_payload_and_goal_polarity() {
        use crate::kernel::SharedMachineIntegerTerm;
        let (premises, _) = inputs(Ty::Int128, Ty::Int64);
        let original =
            IntegerTerm::from_machine(Ty::Int128, Bitvector32Term::Variable(Variable(168_001)))
                .unwrap();
        for (ty, source, destination, value) in [
            (
                Ty::Int32,
                Ty::Int128,
                Ty::Int64,
                Bitvector32Term::Variable(Variable(168_001)),
            ),
            (
                Ty::Int64,
                Ty::Int128,
                Ty::Int64,
                Bitvector32Term::Constant(1),
            ),
            (
                Ty::Int64,
                Ty::UInt128,
                Ty::Int64,
                Ty::Int128
                    .constant_term(
                        MachineIntegerConstant::from_integer(Ty::Int128.format(), &1.into())
                            .unwrap(),
                    )
                    .unwrap(),
            ),
        ] {
            let cast = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                ty,
                Bitvector32Term::MachineIntegerCast {
                    source,
                    destination,
                    value: Box::new(value),
                },
            ));
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(cast, original.clone()),
                true,
            );
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .is_err()
            );
        }
        let (_, goal) = inputs(Ty::Int128, Ty::Int64);
        let Proposition::ConditionIs(condition, _) = goal else {
            unreachable!()
        };
        let false_goal = Proposition::ConditionIs(condition, false);
        assert!(
            certificate(false_goal.clone(), vec![0, 1])
                .check(&false_goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn legacy_integer_cast_identity_work_depends_on_nodes_and_explicit_bounds() {
        let value = Bitvector32Term::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(Ty::Int64, value.clone()).unwrap();
        let observed =
            IntegerTerm::from_machine(Ty::UInt64, Bitvector32Term::UInt64FromInt64(value.into()))
                .unwrap();
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(observed, original.clone()),
            true,
        );
        let mut premises = vec![
            le(IntegerTerm::constant_i64(0), original.clone()),
            le(original, IntegerTerm::constant_i64(i64::MAX)),
        ];
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            premises.resize_with(size, || {
                Proposition::ConditionIs(ConditionTerm::Variable(Variable(168_003)), true)
            });
            let cert = certificate(goal.clone(), vec![0, 1]);
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 32,
            "{samples:?}"
        );
        let mut previous = None;
        for size in [2usize, 8, 32, 128] {
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerCastIdentity {
                        bounds: vec![0, 1],
                        result: goal.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            assert!(work <= 4096 * size, "{size}: {work}");
            if let Some(before) = previous {
                assert!(work <= 4 * before + 64);
            }
            previous = Some(work);
        }
    }

    #[test]
    fn integer_cast_identity_checks_only_explicit_premises_and_scales_with_nodes() {
        let (mut premises, goal) = inputs(Ty::Int128, Ty::Int64);
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            premises.resize_with(size, || {
                Proposition::ConditionIs(ConditionTerm::Variable(Variable(168_003)), true)
            });
            let cert = certificate(goal.clone(), vec![0, 1]);
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 32,
            "{samples:?}"
        );
        let mut previous = None;
        for size in [2usize, 8, 32, 128] {
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerCastIdentity {
                        bounds: vec![0, 1],
                        result: goal.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            assert!(work <= 4096 * size, "{size}: {work}");
            if let Some(before) = previous {
                assert!(work <= 4 * before + 64);
            }
            previous = Some(work);
        }
    }
}
