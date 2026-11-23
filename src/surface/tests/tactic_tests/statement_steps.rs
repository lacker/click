use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_00")]
fn proof_step_supports_explicit_fact_transport() {
    let c_source = r#"
            int32 set_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_is_seven(p: int32[]) {
                p[0] == 7
            }

            int32 set_second_return_first(int32 p[2]) {
                requires first_is_seven(p);
                owns p[0..2];
                ensures result == 7;
            } by {
                unfold(first_is_seven(p));
                step();
                transport(old(p[0]) == 7, p[0] == 7) using {
                    old(p[0]) == 7;
                }
                step();
                solve();
            }
        "#;

    verify_c_sources(click_source, &[("transport.c", c_source)])
        .expect("explicit fact transport should verify");

    let missing_source = click_source.replace(
        "transport(old(p[0]) == 7, p[0] == 7) using {
                    old(p[0]) == 7;
                }",
        "transport(old(p[0]) == 7, p[0] == 7) using {}",
    );
    let error = verify_c_sources(&missing_source, &[("transport.c", c_source)])
        .expect_err("explicit transport must not borrow its logical source from ambient facts");
    assert!(
        error
            .message()
            .contains("requires a source derivable from its explicit facts"),
        "{}",
        error.message()
    );
    // The source is available, only unlisted: the refusal names it as
    // written and does not print it as missing beside the facts holding it.
    assert!(
        error.message().contains(
            "its source `old(p[0]) == 7` is an available fact, but this check reads only the facts listed in `using`"
        ),
        "{}",
        error.message()
    );
    assert!(
        !error.message().contains("available pure facts"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_00")]
fn explicit_fact_transport_can_certify_a_derived_source() {
    let c_source = r#"
            int32 set_third_return_second(int32 p[3]) {
                p[2] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate ordered(p: int32[]) {
                0 <= p[0] and p[0] <= p[1]
            }

            int32 set_third_return_second(int32 p[3]) {
                requires ordered(p);
                owns p[0..3];
                ensures result >= 0;
            } by {
                unfold(ordered(p));
                step();
                transport(0 <= old(p[1]), 0 <= p[1]) using {
                    0 <= old(p[0]);
                    old(p[0]) <= old(p[1]);
                };
                step();
                solve();
            }
        "#;

    // A bare `transport` cites only its source, which is derived here, not
    // available: the facts that derive it are written in `using`.
    let bare = click_source.replace(
        "transport(0 <= old(p[1]), 0 <= p[1]) using {\n                    0 <= old(p[0]);\n                    old(p[0]) <= old(p[1]);\n                };",
        "transport(0 <= old(p[1]), 0 <= p[1]);",
    );
    assert_ne!(bare, click_source);
    let error = verify_c_sources(&bare, &[("transport.c", c_source)])
        .expect_err("a bare transport does not search for the facts deriving its source");
    assert!(
        error.message().contains("search miss"),
        "{}",
        error.message()
    );

    let (verified, planning_transitions) = collect_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("transport.c", c_source)])
    });
    let verified =
        verified.expect("transport should certify a source derived from exact state facts");
    assert!(
        planning_transitions
            .iter()
            .all(
                |(claim, tactic, name)| claim != "set_third_return_second.contract"
                    || *tactic != 1
                    || name != "step"
            ),
        "the selected raw-memory step must search on a checked Proof descendant: \
         {planning_transitions:#?}"
    );

    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked raw-memory step should retain its expansion");
    assert_eq!(expanded[1], ProofTactic::Step);

    let step_offset = click_source
        .find("step();")
        .expect("the smart store step should be present");
    let position = expansion::position_at_offset(click_source, step_offset);
    let rewritten = expand_c_tactic_source_at(
        click_source,
        &[("transport.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the checked raw-memory step should expand");
    assert!(rewritten.contains("step();"), "{rewritten}");
    verify_c_sources(&rewritten, &[("transport.c", c_source)])
        .expect("the rewritten raw-memory step should verify normally");

    // A bare step names no premise list to corrupt; the transport's own
    // explicit premise remains the independently checked evidence.
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_00")]
fn smart_step_starts_each_source_tactic_with_an_empty_step_delta() {
    // The broader smart-step selector treats the most recent checked
    // transition's added facts as premise candidates. That delta belongs to
    // one smart search; a preceding *source* tactic's delta (here the
    // `unfold`) must not leak into the next tactic's certificate step, and
    // the rule must hold on the direct driver exactly as on the interpreter.
    let c_source = r#"
            int32 set_third_return_second(int32 p[3]) {
                p[2] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "delta.c";

            predicate ordered(p: int32[]) {
                0 <= p[0] and p[0] <= p[1]
            }

            int32 set_third_return_second(int32 p[3]) {
                requires ordered(p);
                owns p[0..3];
                ensures result >= 0;
            } by {
                unfold(ordered(p));
                step();
                step();
                solve();
            }
        "#;

    let verified = { verify_c_sources(click_source, &[("delta.c", c_source)]) };
    let verified = verified.expect("the flat proof should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked smart steps should retain their expansion");
    assert_eq!(
        expanded[1],
        ProofTactic::Step,
        "the unfold's added facts leaked into the first smart step: {expanded:#?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn clone_field_stores_with_observed_source_resource_verify() {
    let c_source = r#"
        struct cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 clone_cursor(struct cursor* target, struct cursor* source) {
            target->pos = source->pos;
            target->len = source->len;
            target->data = source->data;
            return target->pos;
        }
    "#;
    let click_source = r#"
        resource readable(data: int32*, length: int32) {
            views data[0..length];
            fact 0 <= length;
        }

        resource cursor(owner: struct cursor*) {
            owns owner->pos;
            owns owner->len;
            owns owner->data;
            views readable(owner->data, owner->len);
            fact 0 <= owner->pos;
            fact owner->pos <= owner->len;
            fact separate(
                memory(*owner),
                memory(owner->data[0..owner->len])
            );
        }

        verifying "clone_cursor.c";

        int32 clone_cursor(struct cursor* target, struct cursor* source) {
            requires separate(memory(*target), memory(*source));
            requires separate(
                memory(*target),
                memory(source->data[0..source->len])
            );
            consumes *target;
            views cursor(source);
            ensures result == source->pos;
        } by {
            observe(cursor(source));
            step();
            step();
            step();
            step();
            solve();
        }
    "#;

    verify_c_sources(click_source, &[("clone_cursor.c", c_source)])
        .expect("clone field stores should verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_00")]
fn simple_statement_transition_does_not_transport_facts_automatically() {
    let base_memory = SymbolicMemory::new();
    let first = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let second = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(4),
    };
    let first_value = MachineTerm::MemoryLoad(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(base_memory.clone()))),
        Box::new(first.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let before_memory = base_memory
        .clone()
        .store(first.clone(), int32(first_value.clone()))
        .store(
            second.clone(),
            int32(MachineTerm::MemoryLoad(
                crate::kernel::ProgramPoint::at(
                    &(crate::kernel::intern_memory(base_memory.clone())),
                ),
                Box::new(second.clone()),
                crate::kernel::LoadKind::Int32,
            )),
        );
    let state = ExecutionState::new()
        .with_memory(before_memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(
                first.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(2),
            )),
        ));
    let fact = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(first_value),
            right: Box::new(MachineTerm::constant(7)),
        },
        true,
    );
    let statement = ProgramStatement::TypedStore {
        access_class: None,
        pointer: ProgramExpression::Value(ProgramValue::pointer(second)),
        value: ProgramExpression::Value(int32(9)),
        value_type: ProgramType::Int32,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    let mut next_opaque_call = 0;
    let mut next_kernel_variable = 0;
    let (transitions, _) = certified_statement_transitions(
        &state,
        &crate::surface::PureFactList::from(vec![fact.clone()]),
        &statement,
        &ExecutionEnvironment::new(),
        None,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
        "simple transition test",
        &mut next_opaque_call,
        &mut next_kernel_variable,
        StatementPrerequisitePolicy::Fast,
        None,
    )
    .expect("simple transition should execute");
    let [transition] = transitions.as_slice() else {
        panic!("expected one transition")
    };

    assert!(transition.pure_facts.contains(&fact));
    let StatementOutcome::Normal(post_state) = &transition.outcome else {
        panic!("expected a normal transition")
    };
    let transported = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::MemoryLoad(
                crate::kernel::ProgramPoint::at(
                    &(crate::kernel::intern_memory(post_state.memory().clone())),
                ),
                Box::new(first),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(MachineTerm::constant(7)),
        },
        true,
    );
    assert!(!transition.pure_facts.contains(&transported));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_01")]
fn failed_call_step_reports_its_unresolved_required_precondition() {
    let c_source = r#"
            int32 caller(int32 x, int32 y) {
                int32 result;
                result = either_positive(x, y);
                return result;
            }
        "#;
    let click_source = r#"
            verifying "caller.c";

            extern int32 either_positive(int32 x, int32 y) {
                requires x > 0 or y > 0;
                ensures result == 0;
            }

            int32 caller(int32 x, int32 y) {
                ensures result == 0;
            } by {
                step();
                step();
            }
        "#;

    let error = verify_c_sources(click_source, &[("caller.c", c_source)])
        .expect_err("the caller establishes neither arm of the call requirement");
    let requirement = error
        .unresolved_requirement()
        .expect("the refused call requirement should survive verification-error wrapping");
    assert_eq!(
        requirement.context.as_deref(),
        Some("precondition clause 1 of `either_positive`")
    );
    assert!(matches!(requirement.proposition, Proposition::Or(_, _)));
    let call_site = requirement
        .call_site
        .as_ref()
        .expect("call requirements retain their selected call site");
    assert_eq!(call_site.callee, "either_positive");
    assert_eq!(call_site.interface.as_ref(), "either_positive");
    assert_eq!(call_site.candidate_ordinal, 0);
    assert_eq!(call_site.requirement_ordinal, 0);
    assert_eq!(call_site.source_requirement_ordinal, Some(0));
    assert_eq!(
        call_site.source_arguments.as_slice(),
        [
            ProgramExpression::Variable(
                crate::kernel::LocalBindingId::new(
                    crate::kernel::LocalFunctionId::new(Some("caller.c".into()), "caller".into()),
                    true,
                    0,
                    Some("x".into())
                )
                .into()
            ),
            ProgramExpression::Variable(
                crate::kernel::LocalBindingId::new(
                    crate::kernel::LocalFunctionId::new(Some("caller.c".into()), "caller".into()),
                    true,
                    1,
                    Some("y".into())
                )
                .into()
            )
        ]
    );

    let wrapped = error
        .clone()
        .with_context("outer context")
        .with_prefix("branch: ");
    assert_eq!(wrapped.unresolved_requirement(), Some(requirement));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_01")]
fn ordinary_requirement_errors_have_no_call_site_metadata() {
    let obligation = ProofObligation::verification_condition(Proposition::Predicate {
        name: "ordinary_requirement".to_string(),
        arguments: Vec::new(),
    });
    let error = ClickError::new("ordinary requirement")
        .with_unresolved_requirement(&obligation)
        .with_proof_refusal(ProofRefusal::UnsuccessfulSearch);
    assert!(error.report().contains("error kind: unsuccessful search"));
    assert!(
        error.report().contains("goal: ordinary_requirement()"),
        "{}",
        error.report()
    );
    assert!(
        error
            .unresolved_requirement()
            .expect("structured ordinary requirement")
            .call_site
            .is_none()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_01")]
fn execute_step_records_a_state_checked_surface_expansion() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures to_integer(result) == to_integer(x + 1);
            } by {
                step();
                normalize();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("increment.c", c_source)])
    });
    let verified = verified.expect("the smart execution step should verify");
    assert_eq!(
        planning_transitions, 0,
        "the exact definedness premise should be selected without a mutable planning transition"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the linear smart step should have a surface expansion");

    assert_eq!(expanded[0], ProofTactic::Step);
    assert_eq!(expanded[1], ProofTactic::Normalize);
    assert_eq!(verified[0].expansion_blocker(), None);
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the recorded expansion should be a surface certificate");
    let source = verified[0]
        .expanded_proof_source()
        .expect("checked expansion should have canonical source");
    assert!(source.contains("step();"));
    assert!(source.contains("normalize();"));

    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
    let line = click_source[..execute_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = execute_offset
        - click_source[..execute_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let rewritten =
        expand_c_tactic_source_at(click_source, &[("increment.c", c_source)], line, column)
            .expect("the overflow-safe step should expand");
    assert!(rewritten.contains("x < 2147483647;"), "{rewritten}");
    verify_c_sources(&rewritten, &[("increment.c", c_source)])
        .expect("the emitted numeric prerequisite should check");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_01")]
fn no_premise_smart_step_searches_directly_on_proof() {
    let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                ensures result == 0;
            } by {
                step();
                known();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("zero.c", c_source)])
    });
    let verified = verified.expect("a no-premise smart step should verify on its Proof successor");
    assert_eq!(
        planning_transitions, 0,
        "the accepted no-premise candidate must not first execute a mutable planning transition"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked smart step should retain its expansion");
    assert_eq!(expanded[0], ProofTactic::Step);
    assert_eq!(expanded[1], ProofTactic::Known);

    let expanded_source = expand_c_claim_source(
        click_source,
        &[("zero.c", c_source)],
        "zero",
        ContractProofClaim::Grouped,
    )
    .expect("the direct smart step should expand into source");
    verify_c_sources(&expanded_source, &[("zero.c", c_source)])
        .expect("the retained no-premise step should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_02")]
fn scalar_root_facts_do_not_force_smart_step_planning() {
    let c_source = r#"
            int32 zero(int32 x) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero(int32 x) {
                requires x >= 0;
                ensures result == 0;
            } by {
                step();
                known();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("zero.c", c_source)])
    });
    let verified = verified.expect("the unrelated scalar fact should remain shared by Proof");
    assert_eq!(
        planning_transitions, 0,
        "an unrelated scalar root fact must not force mutable step planning"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked smart step should retain its expansion");
    assert_eq!(expanded[0], ProofTactic::Step);
    assert_eq!(expanded[1], ProofTactic::Known);

    let expanded_source = expand_c_claim_source(
        click_source,
        &[("zero.c", c_source)],
        "zero",
        ContractProofClaim::Grouped,
    )
    .expect("the checked smart step should expand");
    verify_c_sources(&expanded_source, &[("zero.c", c_source)])
        .expect("the retained step should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_02")]
fn fact_free_linear_smart_steps_search_directly_on_proof() {
    let c_source = r#"
            int32 set_one(int32 x) {
                x = 1;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "set_one.c";

            int32 set_one(int32 x) {
                ensures result == 1;
            } by {
                step();
                step();
                known();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("set_one.c", c_source)])
    });
    let verified = verified.expect("fact-free linear smart steps should verify through Proof");
    assert_eq!(
        planning_transitions, 0,
        "neither linear statement should execute on a mutable planning context"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked linear path should retain its expansion");
    assert!(matches!(
        expanded.as_slice(),
        [
            ProofTactic::Step,
            ProofTactic::Step,
            ProofTactic::Known,
            ProofTactic::Known,
            ProofTactic::Known,
            ProofTactic::Known
        ]
    ));

    let expanded_source = expand_c_claim_source(
        click_source,
        &[("set_one.c", c_source)],
        "set_one",
        ContractProofClaim::Grouped,
    )
    .expect("the direct linear smart steps should expand into source");
    verify_c_sources(&expanded_source, &[("set_one.c", c_source)])
        .expect("the retained linear steps should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_02")]
fn local_assignment_smart_step_selects_only_local_surface_dependencies() {
    let c_source = r#"
            int32 set_one(int32 x) {
                x = 1;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "set_one.c";

            int32 set_one(int32 x) {
                requires x >= 0;
                ensures result == 1;
            } by {
                step();
                step();
                known();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("set_one.c", c_source)])
    });
    let verified = verified.expect("the local assignment dependency should be selected by Proof");
    assert_eq!(
        planning_transitions, 0,
        "the smart local assignment must not execute on a mutable planning context"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked assignment should retain its expansion");
    // The smart step expands to a bare step; the explicit `step();`
    // is kept as written during the migration.
    assert!(
        matches!(
            expanded.as_slice(),
            [
                ProofTactic::Step,
                ProofTactic::Step,
                ProofTactic::Known,
                ProofTactic::Known,
                ProofTactic::Known,
                ProofTactic::Known
            ]
        ),
        "{expanded:#?}"
    );

    let expanded_source = expand_c_claim_source(
        click_source,
        &[("set_one.c", c_source)],
        "set_one",
        ContractProofClaim::Grouped,
    )
    .expect("the selected local dependency should expand into source");
    assert!(expanded_source.contains("x >= 0;"), "{expanded_source}");
    verify_c_sources(&expanded_source, &[("set_one.c", c_source)])
        .expect("the retained assignment dependency should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_02")]
fn execute_rest_return_certificate_omits_unused_ambient_facts() {
    let c_source = r#"
            int32 return_x(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "return_x.c";

            int32 return_x(int32 x) {
                requires x < 100;
                ensures result == x;
            } by {
                step_until(function.exit);
                solve();
            }
        "#;

    let verified = verify_c_sources(click_source, &[("return_x.c", c_source)])
        .expect("the return proof should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the return proof should have a surface expansion");
    assert_eq!(expanded[0], ProofTactic::Step);
    assert!(matches!(expanded[1], ProofTactic::Have(_)));
    assert_eq!(expanded[2], ProofTactic::Known);

    let execute_offset = click_source
        .find("step_until(function.exit)")
        .expect("proof should contain step_until");
    let position = expansion::position_at_offset(click_source, execute_offset);
    let rewritten = expand_c_tactic_source_at(
        click_source,
        &[("return_x.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the return execution should expand");
    assert!(rewritten.contains("    step();"), "{rewritten}");
    verify_c_sources(&rewritten, &[("return_x.c", c_source)])
        .expect("the minimal return certificate should check");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_03")]
fn linear_execute_retains_its_checked_execution_proof() {
    let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                ensures result == 0;
            } by {
                step_until(function.exit);
                known();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("zero.c", c_source)])
    });
    let verified = verified.expect("linear execute should verify through its checked Proof");
    assert_eq!(
        planning_transitions, 0,
        "linear execute must search on checked Proof descendants"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("linear execute should retain an expansion");
    assert_eq!(expanded[0], ProofTactic::Step);
    assert_eq!(expanded[1], ProofTactic::Known);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_03")]
fn linear_execute_until_retains_its_checked_execution_proof() {
    let c_source = r#"
            int32 zero() {
                int32 value = 0;
                return value;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                ensures result == 0;
            } by {
                step_until(region(2).entry);
                step_until(function.exit);
                known();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("zero.c", c_source)])
    });
    let verified = verified.expect("linear execute_until should verify through its checked Proof");
    assert_eq!(
        planning_transitions, 0,
        "linear execute_until must search on checked Proof descendants"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("linear execute_until should retain an expansion");
    assert_eq!(
        &expanded[expanded.len() - 3..],
        &[ProofTactic::Known, ProofTactic::Known, ProofTactic::Known]
    );
    let expanded = &expanded[..expanded.len() - 3];
    assert!(
        expanded[..expanded.len() - 1]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::Step))
    );
    assert_eq!(expanded.last(), Some(&ProofTactic::Known));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_03")]
fn execute_step_omits_materialization_only_transport() {
    let c_source = r#"
            int32 set_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_is_seven(p: int32[]) {
                p[0] == 7
            }

            int32 set_second_return_first(int32 p[2]) {
                requires first_is_seven(p);
                owns p[0..2];
            } by {
                unfold(first_is_seven(p));
                have p[0] == 7 by {
                    known();
                }
                step();
                step();
                solve();
            }
        "#;

    let (verified, planning_transitions) = collect_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("transport.c", c_source)])
    });
    let verified = verified.expect("automatic state transport should verify");
    assert!(
        planning_transitions.iter().all(|(claim, _, tactic)| claim
            != "set_second_return_first.contract"
            || tactic != "step"),
        "resource-sensitive smart steps must search only on checked Proof descendants: \
         {planning_transitions:#?}"
    );
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "atomic transport should have a surface expansion: {:?}",
            verified[0].expansion_blocker()
        )
    });

    assert!(
        !expanded
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::TransportUsing { .. })),
        "{expanded:#?}"
    );
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the materialization-free expansion should be a surface certificate");
    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
    let line = click_source[..execute_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = execute_offset
        - click_source[..execute_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded_source =
        expand_c_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the statement expansion should print as surface Click");
    assert!(!expanded_source.contains("transport("), "{expanded_source}");
    verify_c_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the statement expansion should check without representational transport");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_03")]
fn execute_step_omits_materialized_mixed_state_transport() {
    let c_source = r#"
            int32 replace_first(int32 p[2]) {
                p[0] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_less_than_second(p: int32[]) {
                p[0] < p[1]
            }

            int32 replace_first(int32 p[2]) {
                requires first_less_than_second(p);
                owns p[0..2];
            } by {
                unfold(first_less_than_second(p));
                step();
                step();
                solve();
            }
        "#;

    let verified = verify_c_sources(click_source, &[("transport.c", c_source)])
        .expect("mixed state transport should verify");
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "mixed state transport should have a surface expansion: {:?}",
            verified[0].expansion_blocker()
        )
    });

    assert!(
        !expanded
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::TransportUsing { .. })),
        "{expanded:#?}"
    );
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the mixed-state expansion should be a surface certificate");
    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
    let line = click_source[..execute_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = execute_offset
        - click_source[..execute_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded_source =
        expand_c_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the mixed-state statement should expand");
    verify_c_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the mixed-state expansion should check without representational transport");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_04")]
fn execute_step_omits_materialization_transport_across_statements() {
    let c_source = r#"
            int32 replace_first_then_touch_other(int32 p[2], int32 q[1]) {
                p[0] = 9;
                q[0] = 1;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_less_than_second(p: int32[]) {
                p[0] < p[1]
            }

            int32 replace_first_then_touch_other(int32 p[2], int32 q[1]) {
                requires first_less_than_second(p);
                requires separate(memory(p[0..2]), memory(q[0..1]));
                owns p[0..2];
                owns q[0..1];
            } by {
                unfold(first_less_than_second(p));
                step();
                step();
                step();
                solve();
            }
        "#;

    let verified = verify_c_sources(click_source, &[("transport.c", c_source)])
        .expect("multi-statement state transport should verify");
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "multi-statement transport should have a surface expansion: {:?}",
            verified[0].expansion_blocker()
        )
    });

    assert_eq!(
        expanded
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::TransportUsing { .. }))
            .count(),
        0,
        "{expanded:#?}"
    );
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the multi-statement expansion should be a surface certificate");
    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
    let line = click_source[..execute_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = execute_offset
        - click_source[..execute_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded_source =
        expand_c_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the first multi-statement step should expand");
    verify_c_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the multi-statement expansion should check without representational transport");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_04")]
fn execute_step_expands_call_assign_fact_from_internal_state() {
    let increment_c_source = r#"
            int32 set_seven(int32 p[1]) {
                p[0] = 7;
                return 7;
            }
        "#;
    let caller_c_source = r#"
            int32 call_set_seven(int32 p[1]) {
                int32 result;
                result = set_seven(p);
                return result;
            }
        "#;
    let click_source = r#"
            verifying "set_seven.c";
            verifying "call_set_seven.c";

            int32 set_seven(int32 p[1]) {
                owns p[0..1];
                ensures result == 7;
                ensures p[0] == 7;
            } by {
                step();
                step();
                solve();
            }

            int32 call_set_seven(int32 p[1]) {
                owns p[0..1];
                ensures result == 7;
                ensures p[0] == 7;
            } by {
                step();
                step();
                solve();
            }
        "#;

    let caller_offset = click_source
        .find("int32 call_set_seven")
        .expect("caller should be present");
    let execute_offset = caller_offset
        + click_source[caller_offset..]
            .find("step()")
            .expect("caller should execute its call");
    let line = click_source[..execute_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = execute_offset
        - click_source[..execute_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c_tactic_source_at(
        click_source,
        &[
            ("set_seven.c", increment_c_source),
            ("call_set_seven.c", caller_c_source),
        ],
        line,
        column,
    )
    .expect("call-assign facts should normalize to the source statement exit");
    assert!(expanded.contains("step();"), "{expanded}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_04")]
fn synthesizes_loaded_pointer_equality_as_pointer_comparison() {
    let owner = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(41)), 4),
    };
    let data = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(42)), 4),
    };
    let read = Address::loaded_value(&crate::kernel::intern_memory(SymbolicMemory::new()), &owner);
    let proposition = Proposition::condition_is(
        ConditionTerm::pointer_equal(
            crate::kernel::Pointer::new(read, ProgramType::Int32Pointer),
            crate::kernel::Pointer::new(data.clone(), ProgramType::Int32Pointer),
        ),
        true,
    );
    let parameters = [
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "owner".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "data".to_string(),
            None,
        ),
    ];
    let arguments = [
        ProgramExpression::Value(ProgramValue::pointer(owner)),
        ProgramExpression::Value(ProgramValue::pointer(data)),
    ];

    let surface = super::proof::synthesize_surface_proposition(
        &proposition,
        ParameterBinding::new(&parameters, &arguments),
        &ExecutionState::new(),
    )
    .expect("pointer-offset equality should have a surface form");

    // No field or declaration names the loaded cell and a load carries no
    // pointee type, so it spells at Click's untyped `Pointer`
    // (`design/loads.md`, "Raising"), never at a guessed `int32 *`.
    assert!(matches!(
        surface,
        ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
                value_type: ProgramType::Pointer,
                ..
            }),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Variable(name)),
        } if name == ("data").into()
    ));
}

/// A pointer parameter the function has reassigned names its new value; the
/// value it was passed is `old(p)`. Spelling the passed value as `p` wrote
/// `p == p` for a fact relating the two, which lowers to `true`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_04")]
fn synthesizes_a_reassigned_pointer_parameter_at_entry() {
    let passed = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(43)), 4),
    };
    let current = Address::symbolic(Variable(44));
    let proposition = Proposition::condition_is(
        ConditionTerm::pointer_equal(
            crate::kernel::Pointer::new(passed.clone(), ProgramType::Int32Pointer),
            crate::kernel::Pointer::new(current.clone(), ProgramType::Int32Pointer),
        ),
        true,
    );
    let parameters = [crate::languages::interface::ImportedParameter::new(
        InterfaceType::Int32Pointer,
        "p".to_string(),
        None,
    )];
    let arguments = [ProgramExpression::Value(ProgramValue::pointer(
        passed.clone(),
    ))];
    let entry = ExecutionState::new().with_local("p", ProgramValue::pointer(passed));
    let post = ExecutionState::new().with_local("p", ProgramValue::pointer(current));

    let surface = super::proof::synthesize_surface_proposition_at_entry_and_post(
        &proposition,
        ParameterBinding::new(&parameters, &arguments),
        &entry,
        &post,
    )
    .expect("the entry and current values of `p` both have names");

    assert_eq!(
        crate::surface::printing::source_click_proposition(&surface),
        "old(p) == p"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_05")]
fn synthesizes_dynamically_indexed_pointer_offset_equality() {
    let owner_offset = AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(41)), 4);
    let data_offset = AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(42)), 4);
    let index = MachineTerm::Variable(Variable(43));
    let proposition = Proposition::condition_is(
        ConditionTerm::AddressOffsetEqual(
            Box::new(AddressOffset::Add(
                Box::new(data_offset.clone()),
                Box::new(AddressOffset::scaled_int32_node(index.clone(), 4)),
            )),
            Box::new(AddressOffset::Add(
                Box::new(owner_offset.clone()),
                Box::new(AddressOffset::Constant(4)),
            )),
        ),
        true,
    );
    let parameters = [
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "owner".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "data".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "index".to_string(),
            None,
        ),
    ];
    let arguments = [
        ProgramExpression::Value(ProgramValue::pointer(Address {
            base: "arg-memory".into(),
            offset: owner_offset,
        })),
        ProgramExpression::Value(ProgramValue::pointer(Address {
            base: "arg-memory".into(),
            offset: data_offset,
        })),
        ProgramExpression::Value(ProgramValue::Int32(index)),
    ];

    let surface = super::proof::synthesize_surface_proposition(
        &proposition,
        ParameterBinding::new(&parameters, &arguments),
        &ExecutionState::new(),
    )
    .expect("dynamically indexed pointer equality should have a surface form");

    assert!(matches!(
        surface,
        ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Add(left, right)),
            operator: ComparisonOperator::Equal,
            ..
        } if matches!(left.as_ref(), ProgramExpression::Variable(name) if name.is_named("data"))
            && matches!(right.as_ref(), ProgramExpression::Variable(name) if name.is_named("index"))
    ));
}

/// A bare `step()` whose call precondition no fact states exactly
/// (`memcmp`'s per-byte `defined` requirement, from the caller's viewed
/// range) proves it by the implicit `solve` and records no hidden derivation.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_05")]
fn bare_step_proves_an_open_obligation_by_implicit_solve() {
    let c_source = r#"
            int32 compare_self(uint8 bytes[]) {
                return memcmp(bytes, bytes, 2);
            }
        "#;
    let click_source = r#"
            verifying "compare.c";

            int32 compare_self(uint8 bytes[]) {
                views bytes[0..2];
                ensures 1 == 1 by { step(); step(); solve(); }
            }
        "#;
    let (verified, planning_transitions) = collect_planning_statement_transitions(|| {
        verify_c_sources(click_source, &[("compare.c", c_source)])
    });
    verified.expect("the catalog memcmp call should verify");
    assert_eq!(planning_transitions, vec![]);
    crate::surface::proof::without_implicit_solve(|| {
        verify_c_sources(click_source, &[("compare.c", c_source)])
    })
    .expect_err("with the implicit `solve` off, the open obligation is refused");
}

#[test]
fn explicit_preservation_keeps_a_tagged_pointer_after_a_join() {
    // Both arms store the pointer decoded from the tag, as in rbtree
    // insertion. Preserve that joined observation across the tag write.
    let c_source = r#"struct node { unsigned long tag; struct node *left; struct node *right; };
void change(struct node *g, struct node *source, struct node *t) {
    struct node *p = (struct node *)(source->tag & ~3UL);
    if (t) { g->right = p; t->tag = 0; }
    else { g->right = p; }
    p->tag = 1;
}
"#;
    let click_source = r#"verifying "join.c";
spec enum Model { Empty, Nonempty }
resource child(p: struct node*) {
    field model: Model;
    match model {
        Model::Empty => { fact p == 0; },
        Model::Nonempty => { fact p != 0; owns p->tag; },
    }
}
void change(struct node *g, struct node *source, struct node *t) {
    owns g->right;
    owns source->tag;
    owns ((source->tag & ~3) as (struct node *))->tag;
    owns c: child(t);
    ensures c.model == old(c.model);
    ensures g->right == old((source->tag & ~3) as (struct node *));
} by {
    step(); step();
    match c.model ensuring { owns c: child(t); fact c.model == old(c.model); fact g->right == p; } {
        Model::Empty => {
            unfold(c); step(); step();
            have g->right == p by { solve(); }
            let c = fold(child(t), { model: Model::Empty });
            have c.model == old(c.model) by { solve(); }
        },
        Model::Nonempty => {
            unfold(c); step(); step(); step();
            have g->right == p by { solve(); }
            let c = fold(child(t), { model: Model::Nonempty });
            have c.model == old(c.model) by { solve(); }
        },
    }
    mark before_tag;
    have at(before_tag, g->right == p) by { known(); }
    have separate(memory(g->right), memory(p->tag)) by { known(); }
    step();
    have separate(statement(2).footprint, memory(g->right)) by {
        normalize() using { separate(memory(g->right), memory(p->tag)); };
    }
    have g->right == at(before_tag, g->right) by {
        preserve(memory(g->right), statement(2));
    }
    have g->right == p by {
        rewrite(g->right, at(before_tag, g->right));
        known();
    }
    step(); solve();
}
"#;
    verify_c_sources(click_source, &[("join.c", c_source)])
        .expect("the joined pointer value survives the disjoint tag write");
    let expanded = expand_c_claim_source(
        click_source,
        &[("join.c", c_source)],
        "change",
        ContractProofClaim::Grouped,
    )
    .expect("the tagged-pointer proof should expand");
    assert!(!expanded.contains("transport("), "{expanded}");
    crate::surface::proof::without_implicit_solve(|| {
        verify_c_sources(&expanded, &[("join.c", c_source)])
    })
    .expect("the expanded proof should check independently");

    let false_source = click_source.replace(
        "at(before_tag, g->right == p)",
        "at(before_tag, g->right != p)",
    );
    let error = verify_c_sources(&false_source, &[("join.c", c_source)])
        .expect_err("an available target must not bypass a false source");
    assert!(
        error.message().contains("could not close the current goal"),
        "{}",
        error.message()
    );

    let absent_premise = click_source.replace(
        "normalize() using { separate(memory(g->right), memory(p->tag)); };",
        "normalize() using { false; };",
    );
    let error = verify_c_sources(&absent_premise, &[("join.c", c_source)])
        .expect_err("an available target must not bypass an unavailable premise");
    assert!(
        error
            .message()
            .contains("premise 0 is not exactly available"),
        "{}",
        error.message()
    );

    let overwritten_c = c_source.replace("    p->tag = 1;", "    g->right = 0;\n    p->tag = 1;");
    let overwritten_proof = click_source.replace(
        "    step();\n    have separate(statement(2)",
        "    step(); step();\n    have separate(statement(2)",
    );
    let error = verify_c_sources(&overwritten_proof, &[("join.c", &overwritten_c)])
        .expect_err("separation must refuse the store that overwrites the pointer");
    assert!(
        error.message().contains("did not normalize to true"),
        "{}",
        error.message()
    );
}

#[path = "../../../scaling_tests/surface/tests/tactic_tests/statement_steps.rs"]
mod scaling_tests;

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_05")]
fn prepared_call_cannot_use_its_postcondition_to_prove_its_precondition() {
    let c = "int32 caller(int32 a) { return callee(a); }";
    for step in [
        "step();",
        "step() by known();",
        "step() { requires positive(a) == 1 by known(); }",
    ] {
        let source = format!(
            r#"
verifying "call.c";
function positive(x: int32) -> int32 {{ if x > 0 {{ 1 }} else {{ 0 }} }}
extern int32 callee(int32 x) {{
    requires positive(x) == 1;
    ensures positive(x) == 1;
    ensures result == x;
}}
int32 caller(int32 a) {{
    requires a < 0;
    ensures result == a;
}} by {{ {step} step(); solve(); }}
"#
        );
        verify_c_sources(&source, &[("call.c", c)])
            .expect_err("a conditional successor must not supply its own prerequisite");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by statement_steps_batch_05")]
fn prepared_call_refuses_an_unproved_omitted_requirement() {
    let source = r#"
verifying "call.c";
function positive(x: int32) -> int32 { if x > 0 { 1 } else { 0 } }
extern int32 callee(int32 x, int32 y) {
    requires positive(x) == 1;
    requires positive(y) == 1;
    ensures positive(y) == 1;
    ensures result == x;
}
int32 caller(int32 a, int32 b) {
    requires a > 0;
    requires b < 0;
    ensures result == a;
} by {
    step() {
        requires positive(a) == 1 by {
            unfold(positive(a)); normalize() using { a > 0; };
        }
    }
    step(); solve();
}
"#;
    let c = "int32 caller(int32 a, int32 b) { return callee(a, b); }";
    for implicit in [true, false] {
        let check = || verify_c_sources(source, &[("call.c", c)]);
        let result = if implicit {
            check()
        } else {
            crate::surface::without_implicit_solve(check)
        };
        result.expect_err("every omitted slot must be discharged before publication");
    }
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "statement_steps.rs",
    marker: "statement_steps_batch_",
    statement_steps_batch_00: [
        proof_step_supports_explicit_fact_transport,
        explicit_fact_transport_can_certify_a_derived_source,
        smart_step_starts_each_source_tactic_with_an_empty_step_delta,
        simple_statement_transition_does_not_transport_facts_automatically,
    ],
    statement_steps_batch_01: [
        failed_call_step_reports_its_unresolved_required_precondition,
        ordinary_requirement_errors_have_no_call_site_metadata,
        execute_step_records_a_state_checked_surface_expansion,
        no_premise_smart_step_searches_directly_on_proof,
    ],
    statement_steps_batch_02: [
        scalar_root_facts_do_not_force_smart_step_planning,
        fact_free_linear_smart_steps_search_directly_on_proof,
        local_assignment_smart_step_selects_only_local_surface_dependencies,
        execute_rest_return_certificate_omits_unused_ambient_facts,
    ],
    statement_steps_batch_03: [
        linear_execute_retains_its_checked_execution_proof,
        linear_execute_until_retains_its_checked_execution_proof,
        execute_step_omits_materialization_only_transport,
        execute_step_omits_materialized_mixed_state_transport,
    ],
    statement_steps_batch_04: [
        execute_step_omits_materialization_transport_across_statements,
        execute_step_expands_call_assign_fact_from_internal_state,
        synthesizes_loaded_pointer_equality_as_pointer_comparison,
        synthesizes_a_reassigned_pointer_parameter_at_entry,
    ],
    statement_steps_batch_05: [
        synthesizes_dynamically_indexed_pointer_offset_equality,
        bare_step_proves_an_open_obligation_by_implicit_solve,
        prepared_call_cannot_use_its_postcondition_to_prove_its_precondition,
        prepared_call_refuses_an_unproved_omitted_requirement,
    ],
}
