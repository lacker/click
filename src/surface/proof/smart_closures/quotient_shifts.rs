//! Guarded quotient translations through the ordinary truncation library.
use super::*;
fn number(n: i64) -> SyntaxTerm {
    super::super::surface_synthesis::integer_typed_expression(surface_signed_integer_literal(
        &BigInt::from(n),
    ))
}
fn compare(a: SyntaxTerm, operator: ComparisonOperator, b: SyntaxTerm) -> SyntaxProposition {
    SyntaxProposition::Comparison {
        left: a,
        operator,
        right: b,
    }
}
fn le(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxProposition {
    compare(a, ComparisonOperator::LessEqual, b)
}
fn eq(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxProposition {
    compare(a, ComparisonOperator::Equal, b)
}
fn add(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Add(Box::new(a), Box::new(b))
}
fn mul(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Multiply(Box::new(a), Box::new(b))
}
fn quotient(n: SyntaxTerm, d: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Call {
        name: "truncating_quotient".into(),
        arguments: vec![n, d],
    }
}
fn arguments(e: &SyntaxTerm) -> Option<(&SyntaxTerm, &SyntaxTerm)> {
    let SyntaxTerm::Call { name, arguments } = e else {
        return None;
    };
    if name.rsplit("::").next() != Some("truncating_quotient") {
        return None;
    }
    let [a, b] = arguments.as_slice() else {
        return None;
    };
    Some((a, b))
}
// Plain solve proposes only the guards named by the goal's shift shape.
// The selected emitter checks their availability and writes them explicitly.
pub(super) fn guard_candidates(goal: &SyntaxProposition) -> Vec<Vec<SyntaxProposition>> {
    let SyntaxProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = goal
    else {
        return Vec::new();
    };
    let mut candidates = Vec::new();
    for (lhs, rhs) in [(left, right), (right, left)] {
        if arguments(lhs).is_none() {
            continue;
        }
        let SyntaxTerm::Add(a, b) = rhs else {
            continue;
        };
        for (q, k) in [(a.as_ref(), b.as_ref()), (b.as_ref(), a.as_ref())] {
            if let Some((x, _)) = arguments(q) {
                candidates.push(vec![le(number(0), x.clone()), le(number(0), k.clone())]);
            }
        }
    }
    candidates
}
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_quotient_shift_using(
        input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_quotient_shift_using");
        if !matches!(&input.goal(), Some(condition_source_0 @ Proposition::ConditionIs(
                _,
                true
            )) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::IntegerEqual(..), _))))
        {
            return Ok(None);
        }
        let Some(SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        }) = input.surface_goal()
        else {
            return Ok(None);
        };
        let mut selected = Vec::new();
        for p in premises {
            let kernel = input.lower_cited_surface_proposition(p, "quotient shift premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
            selected.push(kernel);
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
        for (lhs, rhs) in [(left, right), (right, left)] {
            let Some((numerator, divisor)) = arguments(lhs) else {
                continue;
            };
            let SyntaxTerm::Add(a, b) = rhs else {
                continue;
            };
            for (q, k) in [(a.as_ref(), b.as_ref()), (b.as_ref(), a.as_ref())] {
                let Some((x, d)) = arguments(q) else {
                    continue;
                };
                let kernel = input.lower_integer_surface_proposition(
                    &eq(d.clone(), d.clone()),
                    "quotient shift divisor",
                )?;
                let Some((OldConditionTerm::IntegerEqual(value, _), true)) = kernel.old_condition()
                else {
                    continue;
                };
                let Some(value) = value.as_const() else {
                    continue;
                };
                if !value.is_positive() {
                    continue;
                }
                if crate::instrumentation::deadline_exceeded_with_work(value.bits() as usize + 1) {
                    return Ok(None);
                }
                let mut proof = input.clone();
                let mut guards = Vec::new();
                let mut applicable = true;
                for guard in [le(number(0), x.clone()), le(number(0), k.clone())] {
                    let kernel =
                        input.lower_cited_surface_proposition(&guard, "quotient shift guard")?;
                    let scope = proof.driver().open_have(guard.clone())?;
                    proof = if facts.pure_known_available(&kernel)
                        || crate::kernel::proof::fact_reasoning::computes_leaf(&kernel)
                    {
                        scope.driver().apply_step(ProofStep::Known)?.join()?
                    } else if let Some(closed) =
                        scope.driver().try_integer_composition_using(premises)?
                    {
                        closed.join()?
                    } else {
                        applicable = false;
                        break;
                    };
                    guards.push(guard);
                }
                if !applicable {
                    continue;
                }
                for guard in [
                    compare(d.clone(), ComparisonOperator::NotEqual, number(0)),
                    le(number(1), d.clone()),
                ] {
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            guard.clone(),
                            vec![ProofStep::Known],
                        ))?;
                    guards.push(guard);
                }
                let n = add(x.clone(), mul(d.clone(), k.clone()));
                let identity = eq(numerator.clone(), n.clone());
                let scope = proof.driver().open_have(identity.clone())?;
                let Some(closed) = scope.driver().try_integer_algebra()? else {
                    continue;
                };
                proof = closed.join()?;
                let d_identity = eq(divisor.clone(), d.clone());
                let kernel = input
                    .lower_integer_surface_proposition(&d_identity, "quotient shift denominator")?;
                if !crate::kernel::proof::fact_reasoning::computes_leaf(&kernel) {
                    continue;
                }
                proof = proof
                    .driver()
                    .apply_step(super::super::wide_arithmetic::have(
                        d_identity.clone(),
                        vec![ProofStep::Known],
                    ))?;
                let shifted = eq(
                    quotient(n, d.clone()),
                    add(quotient(x.clone(), d.clone()), k.clone()),
                );
                proof = proof
                    .driver()
                    .apply_step(super::super::wide_arithmetic::have(
                        shifted.clone(),
                        vec![
                            ProofStep::ApplyPlannedTheorem {
                                application: TheoremApplication {
                                    name: "click::integer::nonnegative_quotient_shift".into(),
                                    arguments: vec![x.clone(), d.clone(), k.clone()],
                                },
                                premises: guards,
                            },
                            ProofStep::Known,
                        ],
                    ))?;
                if proof.focused_discharged() {
                    return Ok(Some(proof));
                }
                if let Ok(closed) = proof.driver().apply_step(ProofStep::Known) {
                    return Ok(Some(closed));
                }
                proof = proof.driver().apply_step(ProofStep::Rewrite(identity))?;
                proof = proof.driver().apply_step(ProofStep::Rewrite(d_identity))?;
                proof = proof.driver().apply_step(ProofStep::Rewrite(shifted))?;
                return proof.driver().apply_step(ProofStep::Known).map(Some);
            }
        }
        Ok(None)
    }
}
