//! Ordinary selected-premise proofs for the specialized arithmetic planner.
//! Plans select explicit inputs; only ordinary steps establish their results.
use super::*;

fn multiply(a: ContractExpression, b: ContractExpression) -> ContractExpression {
    ContractExpression::Multiply(Box::new(a), Box::new(b))
}

/// Select one mathematical distributivity rewrite in written source. Native
/// observations, calls, reads and other opaque expressions are never opened.
fn distribution(
    expression: &ContractExpression,
) -> Option<(ContractExpression, ContractExpression)> {
    use ContractExpression as E;
    match expression {
        E::Add(a, b) | E::Subtract(a, b) | E::Multiply(a, b) => {
            if let Some(step) = distribution(a).or_else(|| distribution(b)) {
                return Some(step);
            }
            if !matches!(expression, E::Multiply(..)) {
                return None;
            }
            for (sum, factor, left) in [(a, b, true), (b, a, false)] {
                let (p, q, subtract) = match sum.as_ref() {
                    E::Add(p, q) => (p, q, false),
                    E::Subtract(p, q) => (p, q, true),
                    _ => continue,
                };
                let product = |x: &E| {
                    if left {
                        multiply(x.clone(), factor.as_ref().clone())
                    } else {
                        multiply(factor.as_ref().clone(), x.clone())
                    }
                };
                let (u, v) = (Box::new(product(p)), Box::new(product(q)));
                return Some((
                    expression.clone(),
                    if subtract {
                        E::Subtract(u, v)
                    } else {
                        E::Add(u, v)
                    },
                ));
            }
            None
        }
        E::Negate(inner) => distribution(inner),
        E::At {
            selector,
            expression,
        } => distribution(expression).map(|(a, b)| {
            (
                E::At {
                    selector: selector.clone(),
                    expression: Box::new(a),
                },
                E::At {
                    selector: selector.clone(),
                    expression: Box::new(b),
                },
            )
        }),
        E::Old(inner) => {
            distribution(inner).map(|(a, b)| (E::Old(Box::new(a)), E::Old(Box::new(b))))
        }
        _ => None,
    }
}

pub(super) fn needs_distribution(goal: &ClickProposition) -> bool {
    matches!(goal, ClickProposition::Comparison {left,right,..}
        if distribution(left).is_some() || distribution(right).is_some())
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn apply_specialized_composition(
        proof: &Proof<'a>,
        plan: &SpecializedCompositionPlan,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_specialized_composition");
        // Current specialized plans consist of one primitive rule. This is a
        // syntax adapter for that planner, not an interpreter for authored
        // compatibility certificates.
        let [node] = plan.nodes.as_slice() else {
            return Ok(None);
        };
        use SpecialArithmeticNode::*;
        let (indices, result, polynomial) = match node {
            IntegerCastIdentity { bounds, result } | UnsignedSumBound { bounds, result } => {
                (bounds.clone(), result, false)
            }
            IntegerPolynomialIdentity { result, .. } => (Vec::new(), result, true),
            PointerTranslation {
                relation,
                bounds,
                result,
            } => (
                std::iter::once(*relation)
                    .chain(bounds.iter().copied())
                    .collect(),
                result,
                false,
            ),
            PointerAlignment { premise, result } => {
                (premise.iter().copied().collect(), result, false)
            }
            PointerWordEquality {
                relation,
                alignments,
                result,
            } => (
                std::iter::once(*relation)
                    .chain(alignments.iter().copied())
                    .collect(),
                result,
                false,
            ),
            PointerWordFromAlignment { alignments, result } => (alignments.clone(), result, false),
            FloatReflexive { finite, result }
            | FloatBound {
                premise: finite,
                result,
            } => (vec![*finite], result, false),
            SignedDefined { width, .. } => {
                return Self::try_signed_definedness_bounds(proof, *width, plan.premises.clone());
            }
        };
        let Some(premises) = indices
            .iter()
            .map(|i| plan.premises.get(*i).cloned())
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        if matches!(node, PointerTranslation { .. }) {
            return Self::try_pointer_translation_using(proof, &premises);
        }
        if matches!(node, UnsignedSumBound { .. }) {
            return Self::try_widened_unsigned_sum_using(proof, &premises);
        }
        if matches!(node, IntegerCastIdentity { .. }) {
            if proof
                .goal()
                .is_some_and(crate::surface::planning::solve::computes_with_known)
                || Self::known_bridge_using(proof, &premises)?
            {
                return proof.driver().apply_step(ProofStep::Known).map(Some);
            }
            if let Some(closed) = attempt::candidate_outcome(
                Self::try_bounded_observation_identity_using(proof, &premises),
            )?
            .flatten()
            {
                return Ok(Some(closed));
            }
            // Read-over-write cast identities still use the read adapter.
            if !super::signed_intervals::has_retained_read_source(result)
                && !premises
                    .iter()
                    .any(super::signed_intervals::has_retained_read_source)
            {
                return Ok(None);
            }
        }
        let scope = proof.driver().open_have(result.clone())?;
        if matches!(node, FloatReflexive { .. }) {
            if !Self::known_bridge_using(scope.body(), &premises)? {
                return Ok(None);
            }
            let closed = scope.driver().apply_step(ProofStep::Known)?;
            return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
        }
        if matches!(
            node,
            PointerAlignment { .. } | PointerWordEquality { .. } | PointerWordFromAlignment { .. }
        ) && let Some(closed) = scope.driver().try_address_words_using(&premises)?
        {
            return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
        }
        if polynomial {
            let Some(closed) = scope.driver().try_integer_algebra()? else {
                return Ok(None);
            };
            return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
        }

        if !polynomial {
            // Select a rule using only its explicit inputs. Ordinary normalize
            // may use the ambient equality graph; restricted solve must not
            // turn an inapplicable rule candidate into an ambient proof.
            let selected = premises
                .iter()
                .map(|premise| {
                    proof.lower_cited_surface_proposition(premise, "specialized arithmetic input")
                })
                .collect::<Result<Vec<_>, _>>()?;
            let Some(goal) = scope.body().goal() else {
                return Ok(None);
            };
            if crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                goal,
                &selected,
                &crate::kernel::proof::PureFactStore::from_ordered(&selected),
            )
            .is_err()
            {
                return Ok(None);
            }
        }
        if let Ok(closed) = scope
            .driver()
            .apply_step(ProofStep::CompatibilityNormalize(Some(premises)))
            && closed.is_complete()
        {
            return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
        }

        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::without_implicit_solve;
    use crate::surface::*;

    fn replay(parameters: &str, requirements: &str, goal: &str, listed: &str) {
        let source = format!(
            "theorem specialized({parameters}) {{ {requirements} ensures {goal} by {{ close() using {{ {listed} }}; }} }}"
        );
        let expanded = expand_c_claim_source_by_label(&source, &[], "specialized.ensures_0")
            .unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    fn pointer_word_laws_have_explicit_applications() {
        let source = r#"
        theorem mask(p: int32*, word: uint64) {
            requires aligned(p, 8);
            ensures ((address(p) + word) & 7u64) == (word & 7u64) by {
                apply(click::integer::uint64_mask_add_low(address(p), word, 7u64));
            }
        }
        theorem offset(p: int32*, i: int32) {
            ensures address(p + i) == ((address(p) + (i as uint64) * 4u64) as uint64) by {
                apply(click::integer::int32_pointer_add_address_int32(p, i));
            }
        }
        "#;
        without_implicit_solve(|| verify_c_sources(source, &[]))
            .unwrap_or_else(|e| panic!("{}", e.message()));
    }
    #[test]
    fn pointer_alignment_and_tagged_words_expand_without_normalize() {
        let mut failures = Vec::new();
        for (requirements, goal, listed) in [
            (
                "requires aligned(p,8);",
                "(address(p + 2) & 7u64) == 0u64",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "(address(p + 1) & 7u64) != 0u64",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "(address(p) & 3u64) == 0u64",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "(((word & 7u64) | address(p)) & 3u64) == (word & 3u64)",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "((address(p) | 3u64) & 18446744073709551612u64) == address(p)",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "((address(p) + 5u64) & 7u64) == 5u64",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "((address(p) + 5u64) & 18446744073709551612u64) == ((address(p) + 4u64) as uint64)",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8);",
                "(address(p) | 1u64) != (address(p) | 2u64)",
                "aligned(p,8);",
            ),
            (
                "requires aligned(p,8); requires word == (address(p) | 3u64);",
                "(word & 18446744073709551608u64) == address(p)",
                "aligned(p,8); word == (address(p) | 3u64);",
            ),
            (
                "requires aligned(p,8);",
                "(address(p + -2) & 7u64) == 0u64",
                "aligned(p,8);",
            ),
        ] {
            let source = format!(
                "theorem tagged(p: int32*, word: uint64) {{ {requirements} ensures {goal} by {{ close() using {{ {listed} }}; }} }}"
            );
            match expand_c_claim_source_by_label(&source, &[], "tagged.ensures_0") {
                Ok(expanded) => {
                    if expanded.contains("normalize(") || expanded.contains("solve(") {
                        failures.push(expanded);
                        continue;
                    }
                    if let Err(e) = without_implicit_solve(|| verify_c_sources(&expanded, &[])) {
                        failures.push(format!("{}\n{expanded}", e.message()));
                    }
                }
                Err(e) => failures.push(format!("{}\n{source}", e.message())),
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    }
    #[test]
    fn returning_pointer_alignment_replays_without_normalize() {
        let c = [("bump.c", "int32* bump(int32* p) { return p + 2; }")];
        let source = "verifying \"bump.c\"; int32* bump(int32* p) { requires viewable(p[0..3]); views p[0..3]; requires aligned(p,8); ensures aligned(result,8) by { step_until(function.exit); close() using { aligned(p,8); }; } }";
        let expanded = expand_c_claim_source_by_label(source, &c, "bump.ensures_0")
            .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &c))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    fn tagged_word_field_read_expands_without_normalize() {
        let c = [(
            "untag.c",
            "struct node { unsigned long word; }; unsigned long untag(struct node* node, struct node* next) { return node->word & ~7UL; }",
        )];
        let source = r#"verifying "untag.c";
        unsigned long untag(struct node* node, struct node* next) {
            requires node != 0;
            requires aligned(next,8);
            requires node->word == address(next) + 3;
            views node->word;
            ensures result == address(next) by {
                step_until(function.exit);
                close() using { node->word == address(next) + 3; aligned(next,8); };
            }
        }"#;
        let expanded = expand_c_claim_source_by_label(source, &c, "untag.ensures_0")
            .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &c))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    fn address_word_expansion_keeps_alignment_and_mask_guards() {
        for (requires, goal, listed) in [
            (
                "requires aligned(p,8);",
                "((address(p) + 5u64) & 7u64) == 5u64",
                "",
            ),
            (
                "requires aligned(q,8);",
                "((address(p) + 5u64) & 7u64) == 5u64",
                "aligned(q,8);",
            ),
            (
                "requires aligned(p,4);",
                "((address(p) + 5u64) & 7u64) == 5u64",
                "aligned(p,4);",
            ),
            (
                "requires aligned(p,8);",
                "((address(p) + 5u64) & 7u64) == 6u64",
                "aligned(p,8);",
            ),
        ] {
            let source = format!(
                "theorem bad(p: int32*,q: int32*) {{ {requires} ensures {goal} by {{ close() using {{ {listed} }}; }} }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
        }
        let source = "theorem bad(base: uint64,tag: uint64) { requires (base & 5u64) == 0u64; ensures ((base + tag) & 5u64) == (tag & 5u64) by { apply(click::integer::uint64_mask_add_low(base,tag,5u64)); } }";
        assert!(verify_c_sources(source, &[]).is_err());
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: scalar pointer widths and native index formats with strict expansion replay"]
    fn scalar_pointer_offset_laws_expand_across_supported_widths() {
        for (ty, width) in [
            ("uint8", 1),
            ("int8", 1),
            ("uint16", 2),
            ("int16", 2),
            ("uint32", 4),
            ("int32", 4),
            ("uint64", 8),
            ("int64", 8),
            ("float", 4),
            ("double", 8),
        ] {
            for index in ["int32", "int64"] {
                let alignment = width * 2;
                let mask = width - 1;
                let source = format!(
                    "theorem offset(p: {ty}*,i: {index}) {{ requires aligned(p,{alignment}); ensures (address(p + i) & {mask}u64) == 0u64 by {{ close() using {{ aligned(p,{alignment}); }}; }} }}"
                );
                let expanded = expand_c_claim_source_by_label(&source, &[], "offset.ensures_0")
                    .unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
                assert!(!expanded.contains("normalize("), "{expanded}");
                assert!(!expanded.contains("solve("), "{expanded}");
                without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
            }
        }
    }
    #[test]
    fn polynomial_distribution_expands_into_ordinary_rewrites() {
        replay(
            "a: Integer, b: Integer",
            "",
            "(a + b) * (a - b) == a * a - b * b",
            "",
        );
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: specialized arithmetic expansion and strict fresh replay matrix"]
    fn specialized_rules_expand_and_replay_without_certificates() {
        replay(
            "a: Integer, b: Integer, f: Integer",
            "requires a <= b; requires f <= 0;",
            "b * f <= a * f",
            "a <= b; f <= 0;",
        );
        replay(
            "n: Integer, d: Integer, b: Integer",
            "requires d != 0; requires 1 <= d; requires b * d <= n;",
            "b <= truncating_quotient(n,d)",
            "b * d <= n; 1 <= d;",
        );
        replay(
            "x: Integer, k: Integer",
            "requires 0 <= x; requires 0 <= k;",
            "truncating_quotient(x + 3 * k,3) == truncating_quotient(x,3) + k",
            "0 <= x; 0 <= k;",
        );
        replay(
            "p: int32*, word: uint64",
            "requires aligned(p,8);",
            "(((word & 7) | address(p)) & 3) == (word & 3)",
            "aligned(p,8);",
        );
        replay(
            "x: Integer, y: Integer",
            "requires -5 <= x; requires x <= 7; requires 2 <= y; requires y <= 4;",
            "truncating_quotient(x,y) <= 3",
            "-5 <= x; x <= 7; 2 <= y; y <= 4;",
        );
    }
    #[test]
    fn specialized_normalization_refuses_missing_evidence_and_false_identities() {
        for source in [
            "theorem bad(a: Integer,b: Integer,f: Integer) { requires a <= b; ensures b*f <= a*f by { normalize() using { a <= b; }; } }",
            "theorem bad(x: Integer,k: Integer) { requires 0 <= k; ensures truncating_quotient(x + 3*k,3) == truncating_quotient(x,3)+k by { normalize() using { 0 <= k; }; } }",
            "theorem bad(a: Integer,b: Integer) { ensures (a+b)*(a-b) == a*a+b*b by { close(); } }",
            "theorem bad(p: int32*, q: int32*, r: int32*) { requires p == q; requires q == r; ensures p == r by { close() using { p == q; }; } }",
        ] {
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod historical_read_tests {
    #[cfg(not(feature = "fast-gate"))]
    use crate::surface::*;
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: global entry observation identity and strict replay"]
    fn historical_global_observations_expand_from_range_guards() {
        let c = "int32 counter = 3; int32 bump() { counter = counter + 1; return counter; }";
        let source = r#"verifying "counter.c";
            int32 bump() {
                requires counter < 1000; owns counter;
                ensures result == old(counter) + 1;
            } by {
                step_until(function.exit);
                close();
            }"#;
        let expanded = expand_c_claim_source(
            source,
            &[("counter.c", c)],
            "bump",
            ContractProofClaim::Grouped,
        )
        .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[("counter.c", c)]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: historical loop measure expansion and strict replay"]
    fn historical_loop_measure_expands_and_replays_ordinary() {
        let c = "struct box { int32 len; }; int32 drain(struct box* box) { while (box->len > 0) { box->len = box->len - 1; } return box->len; }";
        let source = r#"verifying "drain.c";
            int32 drain(struct box* box) {
                owns box->len;
                requires box->len >= 0;
                ensures result == 0;
            } by {
                loop {
                    decreases box->len;
                    invariant 0 <= box->len;
                    initialize by close();
                    maintain by {
                        have 0 <= to_integer(box->len - 1);
                        step();
                    }
                }
                step();
                close();
            }"#;
        let expanded = expand_c_claim_source(
            source,
            &[("drain.c", c)],
            "drain",
            ContractProofClaim::Grouped,
        )
        .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[("drain.c", c)]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
}
