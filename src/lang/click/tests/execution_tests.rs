use super::*;

#[test]
fn verifies_loadable_segment_proposition_for_indexed_read() {
    let c_source = r#"
            int32 read_index(int32 p[], int32 index, int32 n) {
                return p[index];
            }
        "#;
    let click_source = r#"
            verifying "read_index.c";

            int32 read_index(int32 p[], int32 index, int32 n) {
                requires 0 <= index;
                requires index < n;
                requires loadable(p[0..n]);
                views p[0..n];

                ensures returns_loaded_value: result == p[index] by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("read_index.c", c_source)])
        .expect("loadable segment should prove indexed read loadability");

    assert_eq!(verified.len(), 1);
}

#[test]
fn verifies_symbolic_increment_with_numeric_requirement() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures increments: result == x + 1 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("increment sidecar should verify");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].specification.requires().len(), 1);
}

#[test]
fn bounded_assignment_preserves_successor_definedness() {
    let c_source = r#"
            int32 add_twice(int32 x) {
                int32 first;
                first = x + 1;
                return first + 1;
            }
        "#;
    let click_source = r#"
            verifying "add_twice.c";

            int32 add_twice(int32 x) {
                requires x >= 0;
                requires x <= 2147483645;
                ensures result == (x + 1) + 1;
            } by {
                execute();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("add_twice.c", c_source)])
        .expect("the bound on x should prove both additions defined");
}

#[test]
fn symbolic_increment_without_numeric_requirement_fails() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                ensures increments: result == x + 1 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect_err("increment without overflow requirement should fail");

    assert!(
        error
            .message()
            .contains("undefined behavior: signed overflow"),
        "{}",
        error.message()
    );
}

#[test]
fn uninitialized_scalar_read_fails_verification() {
    let c_source = r#"
            int32 read_uninitialized() {
                int32 x;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "read_uninitialized.c";

            int32 read_uninitialized() {
                ensures result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_uninitialized.c", c_source)])
        .expect_err("an uninitialized scalar read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
fn uninitialized_local_array_read_fails_verification() {
    let c_source = r#"
            int32 read_uninitialized_array() {
                int32 data[1];
                return data[0];
            }
        "#;
    let click_source = r#"
            verifying "read_uninitialized_array.c";

            int32 read_uninitialized_array() {
                ensures result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_uninitialized_array.c", c_source)])
        .expect_err("an uninitialized local array read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
fn pointer_argument_keeps_its_null_execution_path() {
    let c_source = r#"
            int32 pointer_is_null(int32* p) {
                if (p == 0) {
                    return 1;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "pointer_is_null.c";

            int32 pointer_is_null(int32* p) {
                ensures result == 0 by auto;
            }
        "#;

    verify_c0_sources(click_source, &[("pointer_is_null.c", c_source)])
        .expect_err("an unconstrained pointer parameter may be null");
}

#[test]
fn step_and_execute_step_advance_one_concrete_loop_transition() {
    let c_source = r#"
            int32 count_two() {
                int32 i;
                i = 0;
                while (i < 2) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_two.c";

            int32 count_two() {
                ensures returns_two: result == 2 by {
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_two.c", c_source)])
        .expect("small tactics should traverse concrete loop heads and iterations");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
}

#[test]
fn bounded_execute_resumes_and_explores_symbolic_branches() {
    let c_source = r#"
            int32 choose_after_init(int32 x) {
                int32 y;
                y = 0;
                if (x > 0) {
                    y = 1;
                } else {
                    y = 2;
                }
                return y;
            }
        "#;
    let click_source = r#"
            verifying "choose_after_init.c";

            int32 choose_after_init(int32 x) {
                ensures result == 1 or result == 2 by {
                    step();
                    step();
                    execute();
                    normalize();
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("choose_after_init.c", c_source)])
        .expect("bounded execution should resume and prove every symbolic branch");

    assert_eq!(verified.len(), 2);
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.proof_kind() == ProofKind::TacticScript)
    );
    for theorem in &verified {
        let expanded = theorem.expanded_proof_tactics().unwrap_or_else(|| {
            panic!(
                "bounded branch execution should expand: {:?}",
                theorem.expansion_blocker()
            )
        });
        let proof_if = expanded
            .iter()
            .find_map(|tactic| match tactic {
                ProofTactic::If(proof_if) => Some(proof_if),
                _ => None,
            })
            .expect("bounded branch execution should retain its surface branch");
        assert_eq!(proof_if.then_tactics.last(), Some(&ProofTactic::Normalize));
        assert_eq!(proof_if.else_tactics.last(), Some(&ProofTactic::Normalize));
        ProofCertificate::from_proof_tactics(&expanded)
            .expect("bounded branch expansion should be a surface certificate");
    }
}

#[test]
fn verifies_fill3_c0_source_with_sidecar_specification() {
    let verified = verify_c0_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
        .expect("fill3 sidecar should verify");

    assert_eq!(verified.len(), 1);
    let verified = &verified[0];
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: scale_int32_offset(
            Bitvector32Term::Variable(Variable(POINTER_ARGUMENT_VARIABLE_BASE)),
            4,
        ),
    };
    let first = base.clone();
    let second = offset_pointer_by_int32_elements(base.clone(), Bitvector32Term::Constant(1));
    let third = offset_pointer_by_int32_elements(base.clone(), Bitvector32Term::Constant(2));
    let local_i = Pointer {
        block: "local:i".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let initial_memory = memory_with_symbolic_loadable_cells(
        CMemory::new(),
        &std::collections::BTreeMap::from([(
            "p".to_string(),
            ConcreteMemoryRangeSeed {
                base: base.clone(),
                bytes: 12,
                element_width: 4,
            },
        )]),
    );
    let initial_resources =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(3),
        )));
    let final_memory = initial_memory
        .clone()
        .with_block("local:i", 4)
        .store(first, int32(0))
        .store(second, int32(1))
        .store(third, int32(2))
        .store(local_i, int32(3));

    assert_eq!(
        verified.specification.state(),
        &CState::new()
            .with_memory(initial_memory)
            .with_resource_context(initial_resources.clone())
    );
    assert_eq!(verified.specification.arguments(), &[c_pointer_value(base)]);
    assert_eq!(
        verified.specification.outcome(),
        &CFunctionOutcome::Return {
            value: int32(2),
            state: CState::new()
                .with_memory(final_memory)
                .with_resource_context(initial_resources),
        }
    );
    assert_eq!(
        implication_body(verified.theorem.proposition()),
        &Proposition::CFunctionPartiallySatisfiesSpecification {
            function: syntax::parse_function(FILL3_C)
                .expect("fill3 should parse")
                .to_kernel_function()
                .with_resource_summary(
                    vec![CResourceSpec::Write(CMemorySegment::new(
                        CExpression::Variable("p".to_string()),
                        CExpression::Value(int32(0)),
                        CExpression::Value(int32(3)),
                    ))],
                    Vec::new(),
                )
                .with_contract(
                    vec![SpecProposition::MemoryLoadable {
                        memory: SpecMemory::Current,
                        base: SpecExpression::CExpression(CExpression::Variable("p".to_string(),)),
                        start: SpecExpression::Value(int32(0)),
                        end: SpecExpression::Value(int32(3)),
                        element_width: 4,
                    }],
                    vec![SpecProposition::Comparison {
                        left: SpecExpression::CExpression(CExpression::Variable(
                            "result".to_string(),
                        )),
                        operator: CComparisonOperator::Equal,
                        right: SpecExpression::Value(int32(2)),
                    }],
                    vec![CMemorySegment::new(
                        CExpression::Variable("p".to_string()),
                        CExpression::Value(int32(0)),
                        CExpression::Value(int32(3)),
                    )],
                    vec![CFunctionContractClaim::ensure_proposition(0, 0)],
                    true,
                ),
            specification: verified.specification.clone(),
        }
    );
}

#[test]
fn bounded_auto_loop_expands_without_a_detached_summary() {
    let sources = [("fill3.c", FILL3_C)];
    let position = c0_tactic_source_position(FILL3_CLICK, &sources, "fill3.returns_second", 0)
        .expect("the default auto proof should have a source position");
    let expanded =
        expand_c0_tactic_source_at(FILL3_CLICK, &sources, position.line, position.column)
            .expect("bounded loop execution should have a surface certificate");

    assert!(!expanded.contains("summarize("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the bounded loop certificate should freshly replay");
}

#[test]
fn signature_mismatch_reports_direct_error() {
    let source = FILL3_CLICK.replace("int32* p", "int32 q");
    let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
        .expect_err("wrong signature should fail");

    assert!(
        error.message().contains("signature mismatch"),
        "{}",
        error.message()
    );
}

#[test]
fn struct_name_signature_mismatch_reports_direct_error() {
    let c_source = r#"
        struct actual {
            int32 value;
        };

        struct expected {
            int32 value;
        };

        int32 get_value(struct actual* p) {
            return p->value;
        }
    "#;
    let click_source = r#"
        verifying "get_value.c";

        int32 get_value(struct expected* p) {
            views p->value;
            ensures result == old(p->value) by auto;
        }
    "#;

    let error = verify_c0_sources(click_source, &[("get_value.c", c_source)])
        .expect_err("wrong struct name should fail");

    assert!(
        error.message().contains(
            "signature mismatch for `get_value` parameter 1 in `get_value.c`: .click has struct expected* p, C has struct actual* p"
        ),
        "{}",
        error.message()
    );
}

#[test]
fn observed_cursor_facts_produce_replayable_surface_certificates() {
    let c_source = r#"
        struct input_cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 input_cursor_peek(struct input_cursor* owner) {
            return owner->data[owner->pos];
        }
    "#;
    let take_c_source = r#"
        struct input_cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 input_cursor_take(struct input_cursor* owner) {
            int32 value;
            value = owner->data[owner->pos];
            owner->pos = owner->pos + 1;
            return value;
        }
    "#;
    let click_source = r#"
        resource readable_input(data: int32*, length: int32) {
            views data[0..length];
            fact 0 <= length;
        }

        resource input_cursor(owner: struct input_cursor*) {
            owns owner->pos;
            owns owner->len;
            owns owner->data;
            views readable_input(owner->data, owner->len);
            fact 0 <= owner->pos;
            fact owner->pos <= owner->len;
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->len])
            );
        }

        verifying "input_cursor_peek.c";
        verifying "input_cursor_take.c";

        int32 input_cursor_peek(struct input_cursor* owner) {
            requires owner->pos < owner->len;
            views input_cursor(owner);
            immutable;
            ensures result == owner->data[owner->pos];
        } by {
            observe(input_cursor(owner));
            observe(readable_input(owner->data, owner->len));
            execute();
            frame();
            simp();
        }

        int32 input_cursor_take(struct input_cursor* owner) {
            requires owner->pos < owner->len;
            owns input_cursor(owner);
            mutable owner->pos;
            ensures result == old(owner->data[owner->pos]);
            ensures owner->pos == old(owner->pos) + 1;
            ensures owner->len == old(owner->len);
            ensures owner->data == old(owner->data);
        } by {
            unfold(input_cursor(owner));
            observe(readable_input(owner->data, owner->len));
            execute();
            have 0 <= owner->pos by simp;
            have owner->pos <= owner->len by simp;
            have separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->len])
            ) by {
                simp();
            }
            fold(input_cursor(owner));
            frame();
            simp();
        }

    "#;

    let sources = [
        ("input_cursor_peek.c", c_source),
        ("input_cursor_take.c", take_c_source),
    ];
    let final_simp = click_source
        .rfind("simp();")
        .expect("final simp should exist");
    let position = expansion::position_at_offset(click_source, final_simp);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped simp should emit a non-circular surface certificate");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped simp surface certificate should replay from fresh source");
}

#[test]
fn explicit_store_step_with_unfolded_resource_facts_verifies() {
    let c_source = r#"
        struct owned_string {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 owned_string_set(
            struct owned_string* owner,
            int32 index,
            int32 value
        ) {
            owner->data[index] = value;
            return value;
        }
    "#;
    let click_source = r#"
        predicate terminated_at(data: int32[], length: int32) {
            data[length] == 0
        }

        resource owned_string(owner: struct owned_string*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len < owner->cap;
            fact terminated_at(owner->data, owner->len);
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            );
        }

        verifying "owned_string_set.c";

        int32 owned_string_set(
            struct owned_string* owner,
            int32 index,
            int32 value
        ) {
            requires 0 <= index;
            requires index < owner->len;
            owns owned_string(owner);
            ensures result == value;
            ensures owner->data[index] == value;
        } by {
            unfold(owned_string(owner));
            unfold(terminated_at);
            step();
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at);
                simp();
            }
            have owner->data[owner->len] == 0 by simp;
            have 0 <= owner->len by simp;
            have owner->len < owner->cap by simp;
            have separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            ) by {
                simp();
            }
            fold(owned_string(owner));
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("owned_string_set.c", c_source)])
    });
    verified.expect("explicit store certificate should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "owned_string_set.contract"
                    && name == "smart tactic compatibility replay (tactic 9, source 9)"
        )),
        "the leading Have and resource-backed step must remain on Proof: {events:#?}"
    );

    let smart_step = click_source
        .rfind("step();")
        .expect("the resource-backed return step should be present");
    let position = expansion::position_at_offset(click_source, smart_step);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("owned_string_set.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained Have and statement step should expand");
    assert!(expanded.contains("have "), "{expanded}");
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c0_sources(&expanded, &[("owned_string_set.c", c_source)])
        .expect("the rewritten resource-backed step should verify normally");
}

#[test]
fn expanded_read_step_keeps_named_range_separation_premises() {
    let c_source = r#"
        struct owned_string {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 owned_string_pop(struct owned_string* owner) {
            int32 index;
            int32 value;
            index = owner->len - 1;
            value = owner->data[index];
            owner->data[index] = 0;
            owner->len = index;
            return value;
        }
    "#;
    let click_source = r#"
        predicate terminated_at(data: int32[], length: int32) {
            data[length] == 0
        }

        resource owned_string(owner: struct owned_string*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len < owner->cap;
            fact terminated_at(owner->data, owner->len);
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            );
        }

        verifying "owned_string_pop.c";

        int32 owned_string_pop(struct owned_string* owner) {
            requires 1 <= owner->len;
            owns owned_string(owner);
            mutable owner[0..1], (owner->data + (owner->len - 1))[0..1];
            ensures result == old(owner->data[owner->len - 1]);
            ensures owner->len == old(owner->len) - 1;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
            ensures owner->data[owner->len] == 0;
        } by {
            unfold(owned_string(owner));
            have 0 <= owner->len - 1 by simp;
            have owner->len - 1 < owner->len by simp;
            execute();
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at);
                simp();
            }
            have 0 <= owner->len by simp;
            have owner->len < owner->cap by simp;
            have separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            ) by {
                simp();
            }
            fold(owned_string(owner));
            frame();
            simp();
        }
    "#;
    let execute_offset = click_source
        .find("execute()")
        .expect("proof should contain execute_rest");
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
    let (expanded, events) = crate::instrumentation::collect(|| {
        expand_c0_tactic_source_at(
            click_source,
            &[("owned_string_pop.c", c_source)],
            line,
            column,
        )
    });
    let expanded = expanded.expect("the read step's generated surface certificate should replay");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "owned_string_pop.contract"
                    && name == "smart tactic compatibility replay (tactic 3, source 3)"
        )),
        "resource-backed execute entered compatibility replay: {events:#?}"
    );

    let strict_limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(30),
        smart: std::time::Duration::from_millis(100),
        control: std::time::Duration::from_secs(30),
    };
    crate::instrumentation::with_tactic_limits(strict_limits, || {
        verify_c0_sources(&expanded, &[("owned_string_pop.c", c_source)])
    })
    .expect("the expanded certificate should contain no deferred smart tactic");

    let generous_limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(30),
        smart: std::time::Duration::from_secs(30),
        control: std::time::Duration::from_secs(30),
    };
    crate::instrumentation::with_tactic_limits(generous_limits, || {
        verify_c0_sources(&expanded, &[("owned_string_pop.c", c_source)])
    })
    .expect("the expanded read certificate should verify as a complete proof");
}

#[test]
fn decrement_contract_replays_nonnegative_and_equality_certificates() {
    let c_source = r#"
        int32 decrement(int32 value, int32 count) {
            return value - 1;
        }
    "#;
    let click_source = r#"
        verifying "decrement.c";

        int32 decrement(int32 value, int32 count) {
            requires 0 < value;
            requires value == count;
            ensures result == value - 1;
        } by {
            have 0 <= value - 1 by simp;
            have value - 1 < value by simp;
            have value - 1 == count - 1 by simp;
            execute();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("decrement.c", c_source)])
        .expect("decrement arithmetic should search and replay consistently");
}
