use super::*;

#[test]
fn simple_step_supports_explicit_fact_transport() {
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
                consumes p[0..2];
                mutable p[1..2];
                produces p[0..2];
                ensures result == 7;
            } by {
                unfold(first_is_seven);
                step();
                transport(old(p[0]) == 7, p[0] == 7) using {
                    old(p[0]) == 7;
                }
                step();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("explicit fact transport should verify");

    let missing_source = click_source.replace(
        "transport(old(p[0]) == 7, p[0] == 7) using {
                    old(p[0]) == 7;
                }",
        "transport(old(p[0]) == 7, p[0] == 7) using {}",
    );
    let error = verify_c0_sources(&missing_source, &[("transport.c", c_source)])
        .expect_err("explicit transport must not borrow its logical source from ambient facts");
    assert!(
        error
            .message()
            .contains("requires a source derivable from its explicit facts"),
        "{}",
        error.message()
    );
}

#[test]
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
                consumes p[0..3];
                mutable p[2..3];
                produces p[0..3];
                ensures result >= 0;
            } by {
                unfold(ordered);
                step();
                transport(0 <= old(p[1]), 0 <= p[1]);
                step();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("transport should certify a source derived from exact snapshot facts");
}

#[test]
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
                memory(owner[0..4]),
                memory(owner->data[0..owner->len])
            );
        }

        verifying "clone_cursor.c";

        int32 clone_cursor(struct cursor* target, struct cursor* source) {
            requires separate(memory(target[0..4]), memory(source[0..4]));
            requires separate(
                memory(target[0..4]),
                memory(source->data[0..source->len])
            );
            consumes target[0..4];
            views cursor(source);
            mutable target[0..4];
            ensures result == source->pos;
        } by {
            observe(cursor(source));
            step();
            step();
            step();
            step();
            frame();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("clone_cursor.c", c_source)])
        .expect("clone field stores should verify");
}

#[test]
fn simple_statement_transition_does_not_transport_facts_automatically() {
    let base_memory = CMemory::new();
    let first = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let first_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(base_memory.clone()),
        Box::new(first.clone()),
    );
    let before_memory = base_memory
        .clone()
        .store(first.clone(), int32(first_value.clone()))
        .store(
            second.clone(),
            int32(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(base_memory.clone()),
                Box::new(second.clone()),
            )),
        );
    let state = CState::new()
        .with_memory(before_memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new(
                first.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(2),
            )),
        ));
    let fact = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(first_value),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );
    let statement = CStatement::TypedStore {
        pointer: CExpression::Value(CValue::Pointer(second)),
        value: CExpression::Value(int32(9)),
        value_type: CType::Int32,
    };
    let mut next_opaque_call = 0;
    let mut next_verification_variable = 0;
    let (transitions, _) = certified_statement_transitions(
        &state,
        std::slice::from_ref(&fact),
        &statement,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        "simple transition test",
        &mut next_opaque_call,
        &mut next_verification_variable,
        StatementPrerequisitePolicy::Explicit,
        StatementFactTransportPolicy::None,
    )
    .expect("simple transition should execute");
    let [transition] = transitions.as_slice() else {
        panic!("expected one transition")
    };

    assert!(transition.pure_facts.contains(&fact));
    let CStatementOutcome::Normal(post_state) = &transition.outcome else {
        panic!("expected a normal transition")
    };
    let transported = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(post_state.memory().clone()),
                Box::new(first),
            )),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );
    assert!(!transition.pure_facts.contains(&transported));
}

#[test]
fn simple_step_does_not_contextually_prove_execution_prerequisites() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result > x;
            } by {
                step() using {
                }
                simp();
            }
        "#;

    let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect_err("simple tactic must preserve the overflow prerequisite");
    assert!(
        error.message().contains("signed overflow"),
        "{}",
        error.message()
    );
}

#[test]
fn step_using_limits_execution_to_explicit_pure_premises() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result == x + 1;
            } by {
                step() using {
                    x < 2147483647;
                }
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("an explicit premise should justify one contextual execution transition");
}

#[test]
fn execute_step_records_a_point_checked_surface_expansion() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result == x + 1;
            } by {
                step();
                normalize();
            }
        "#;

    let ((verified, events), planning_transitions) = count_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("increment.c", c_source)])
        })
    });
    let verified = verified.expect("the smart execution step should verify");
    assert_eq!(
        planning_transitions, 0,
        "the exact definedness premise should be selected without a mutable planning transition"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment.contract" && name == "surface certificate replay"
        )),
        "a linear smart step must retain its checked Proof instead of ordinarily replaying it: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the linear smart step should have a surface expansion");

    assert!(matches!(expanded[0], ProofTactic::StepUsing(_)));
    let ProofTactic::StepUsing(premises) = &expanded[0] else {
        unreachable!("the first expanded tactic was checked above")
    };
    assert_eq!(premises.len(), 1);
    assert_eq!(expanded[1], ProofTactic::Normalize);
    assert_eq!(verified[0].expansion_blocker(), None);
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the recorded expansion should be a surface certificate");
    let source = verified[0]
        .expanded_proof_source()
        .expect("checked expansion should have canonical source");
    assert!(source.contains("step() using"));
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
        expand_c0_tactic_source_at(click_source, &[("increment.c", c_source)], line, column)
            .expect("the overflow-safe step should expand");
    assert!(rewritten.contains("x < 2147483647;"), "{rewritten}");
    verify_c0_sources(&rewritten, &[("increment.c", c_source)])
        .expect("the emitted numeric prerequisite should replay");
}

#[test]
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
                normalize();
            }
        "#;

    let ((verified, events), planning_transitions) = count_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &[("zero.c", c_source)]))
    });
    let verified = verified.expect("a no-premise smart step should verify on its Proof successor");
    assert_eq!(
        planning_transitions, 0,
        "the accepted no-premise candidate must not first execute a mutable planning transition"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "zero.contract" && name == "surface certificate replay"
        )),
        "the direct Proof successor must not pass through ordinary construction replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked smart step should retain its expansion");
    assert_eq!(expanded[0], ProofTactic::StepUsing(Vec::new()));
    assert_eq!(expanded[1], ProofTactic::Normalize);

    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("zero.c", c_source)],
        "zero",
        CProofClaim::Grouped,
    )
    .expect("the direct smart step should expand into source");
    verify_c0_sources(&expanded_source, &[("zero.c", c_source)])
        .expect("the retained no-premise step should independently reverify");
}

#[test]
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
                normalize();
            }
        "#;

    let ((verified, events), planning_transitions) = count_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("set_one.c", c_source)])
        })
    });
    let verified = verified.expect("fact-free linear smart steps should verify through Proof");
    assert_eq!(
        planning_transitions, 0,
        "neither linear statement should execute on a mutable planning context"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "set_one.contract" && name == "surface certificate replay"
        )),
        "the retained Proof path must not pass through ordinary construction replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked linear path should retain its expansion");
    assert!(matches!(
        expanded.as_slice(),
        [ProofTactic::StepUsing(first), ProofTactic::StepUsing(second), ProofTactic::Normalize]
            if first.is_empty() && second.is_empty()
    ));

    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("set_one.c", c_source)],
        "set_one",
        CProofClaim::Grouped,
    )
    .expect("the direct linear smart steps should expand into source");
    verify_c0_sources(&expanded_source, &[("set_one.c", c_source)])
        .expect("the retained linear steps should independently reverify");
}

#[test]
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
                step() using {}
                normalize();
            }
        "#;

    let ((verified, events), planning_transitions) = count_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("set_one.c", c_source)])
        })
    });
    let verified = verified.expect("the local assignment dependency should be selected by Proof");
    assert_eq!(
        planning_transitions, 0,
        "the smart local assignment must not execute on a mutable planning context"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "set_one.contract" && name == "surface certificate replay"
        )),
        "the retained Proof path must not pass through ordinary construction replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked assignment should retain its expansion");
    assert!(matches!(
        expanded.as_slice(),
        [ProofTactic::StepUsing(first), ProofTactic::StepUsing(second), ProofTactic::Normalize]
            if first.len() == 1 && second.is_empty()
    ));

    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("set_one.c", c_source)],
        "set_one",
        CProofClaim::Grouped,
    )
    .expect("the selected local dependency should expand into source");
    assert!(expanded_source.contains("x >= 0;"), "{expanded_source}");
    verify_c0_sources(&expanded_source, &[("set_one.c", c_source)])
        .expect("the retained assignment dependency should independently reverify");
}

#[test]
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
                execute();
                simp();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("return_x.c", c_source)])
        .expect("the return proof should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the return proof should have a surface expansion");
    assert_eq!(expanded[0], ProofTactic::StepUsing(Vec::new()));
    assert!(matches!(expanded[1], ProofTactic::Have(_)));
    assert_eq!(expanded[2], ProofTactic::Assumption);

    let execute_offset = click_source
        .find("execute()")
        .expect("proof should contain execute_rest");
    let position = expansion::position_at_offset(click_source, execute_offset);
    let rewritten = expand_c0_tactic_source_at(
        click_source,
        &[("return_x.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the return execution should expand");
    assert!(rewritten.contains("    step() using {"), "{rewritten}");
    verify_c0_sources(&rewritten, &[("return_x.c", c_source)])
        .expect("the minimal return certificate should replay");
}

#[test]
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
                execute();
                normalize();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("zero.c", c_source)])
    });
    let verified = verified.expect("linear execute should verify through its checked Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "zero.contract" && name == "surface certificate replay"
        )),
        "linear execute must not ordinarily replay its retained certificate: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("linear execute should retain an expansion");
    assert_eq!(expanded[0], ProofTactic::StepUsing(Vec::new()));
    assert_eq!(expanded[1], ProofTactic::Normalize);
}

#[test]
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
                execute_until(statement(2));
                execute();
                normalize();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("zero.c", c_source)])
    });
    let verified = verified.expect("linear execute_until should verify through its checked Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "zero.contract" && name == "surface certificate replay"
        )),
        "linear execute_until must not ordinarily replay its retained certificate: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("linear execute_until should retain an expansion");
    assert!(
        expanded[..expanded.len() - 1]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::StepUsing(_)))
    );
    assert_eq!(expanded.last(), Some(&ProofTactic::Normalize));
}

#[test]
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
                consumes p[0..2];
                mutable p[1..2] by {
                    unfold(first_is_seven);
                    have p[0] == 7 by {
                        assumption();
                    }
                    step();
                    step();
                    frame();
                }
                produces p[0..2];
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("automatic snapshot transport should verify");
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
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the statement expansion should print as surface Click");
    assert!(!expanded_source.contains("transport("), "{expanded_source}");
    verify_c0_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the statement expansion should replay without representational transport");
}

#[test]
fn execute_step_omits_materialized_mixed_snapshot_transport() {
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
                consumes p[0..2];
                mutable p[0..1] by {
                    unfold(first_less_than_second);
                    step();
                    step();
                    frame();
                }
                produces p[0..2];
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("mixed snapshot transport should verify");
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "mixed snapshot transport should have a surface expansion: {:?}",
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
        .expect("the mixed-snapshot expansion should be a surface certificate");
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
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the mixed-snapshot statement should expand");
    verify_c0_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the mixed-snapshot expansion should replay without representational transport");
}

#[test]
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
                consumes p[0..2];
                consumes q[0..1];
                mutable p[0..1], q[0..1] by {
                    unfold(first_less_than_second);
                    step();
                    step();
                    step();
                    frame();
                }
                produces p[0..2];
                produces q[0..1];
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("multi-statement snapshot transport should verify");
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
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the first multi-statement step should expand");
    verify_c0_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the multi-statement expansion should replay without representational transport");
}

#[test]
fn execute_step_expands_call_assign_fact_from_internal_snapshot() {
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
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == 7;
                ensures p[0] == 7;
            } by {
                step();
                step();
                frame();
                simp();
            }

            int32 call_set_seven(int32 p[1]) {
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == 7;
                ensures p[0] == 7;
            } by {
                step();
                step();
                frame();
                simp();
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

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[
            ("set_seven.c", increment_c_source),
            ("call_set_seven.c", caller_c_source),
        ],
        line,
        column,
    )
    .expect("call-assign facts should normalize to the source statement exit");
    assert!(expanded.contains("step() using {"), "{expanded}");
}

#[test]
fn synthesizes_pointer_offset_equality_as_pointer_comparison() {
    let owner_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(41))),
        byte_width: 4,
    };
    let data_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(42))),
        byte_width: 4,
    };
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: owner_offset,
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: data_offset.clone(),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(owner.clone()),
                )),
                byte_width: 4,
            }),
            Box::new(data_offset),
        ),
        true,
    );
    let parameters = [
        syntax::C0Parameter::new(C0Type::Int32Pointer, "owner".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32Pointer, "data".to_string(), None),
    ];
    let arguments = [
        CExpression::Value(CValue::Pointer(owner)),
        CExpression::Value(CValue::Pointer(data)),
    ];

    let surface = super::proof::synthesize_surface_proposition(
        &proposition,
        &parameters,
        &arguments,
        &CState::new(),
    )
    .expect("pointer-offset equality should have a Click spelling");

    assert!(matches!(
        surface,
        ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::TypedLoad {
                value_type: CType::Int32Pointer,
                ..
            }),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable(name)),
        } if name == "data"
    ));
}

#[test]
fn synthesizes_dynamically_indexed_pointer_offset_equality() {
    let owner_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(41))),
        byte_width: 4,
    };
    let data_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(42))),
        byte_width: 4,
    };
    let index = Bitvector32Term::Variable(Variable(43));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(
            Box::new(PointerOffsetTerm::Add(
                Box::new(data_offset.clone()),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index.clone()),
                    byte_width: 4,
                }),
            )),
            Box::new(PointerOffsetTerm::Add(
                Box::new(owner_offset.clone()),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
        ),
        true,
    );
    let parameters = [
        syntax::C0Parameter::new(C0Type::Int32Pointer, "owner".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32Pointer, "data".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32, "index".to_string(), None),
    ];
    let arguments = [
        CExpression::Value(CValue::Pointer(Pointer {
            block: "arg-memory".into(),
            offset: owner_offset,
        })),
        CExpression::Value(CValue::Pointer(Pointer {
            block: "arg-memory".into(),
            offset: data_offset,
        })),
        CExpression::Value(CValue::Int32(index)),
    ];

    let surface = super::proof::synthesize_surface_proposition(
        &proposition,
        &parameters,
        &arguments,
        &CState::new(),
    )
    .expect("dynamically indexed pointer equality should have a Click spelling");

    assert!(matches!(
        surface,
        ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Add(left, right)),
            operator: ComparisonOperator::Equal,
            ..
        } if matches!(left.as_ref(), CExpression::Variable(name) if name == "data")
            && matches!(right.as_ref(), CExpression::Variable(name) if name == "index")
    ));
}
