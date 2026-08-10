use super::*;

#[test]
fn click_addition_cancels_a_negated_pointer_base() {
    let base = Bitvector32Term::Variable(Variable(90));
    let index = Bitvector32Term::Variable(Variable(91));
    let negative_base = Bitvector32Term::Subtract(
        Box::new(Bitvector32Term::Constant(0)),
        Box::new(base.clone()),
    );

    assert_eq!(
        super::lowering::bitvector32_add(
            negative_base,
            Bitvector32Term::Add(Box::new(base), Box::new(index.clone())),
        ),
        index
    );
}

#[test]
fn resource_neutral_callee_preserves_callers_allocation_resource() {
    let push_c = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 push(struct vector* owner, int32 value) {
            int32 index;
            int32* data;
            index = owner->len;
            data = owner->data;
            data[index] = value;
            owner->len = index + 1;
            return owner->len;
        }
    "#;
    let caller_c = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 caller(struct vector* owner, int32 value) {
            int32 pushed;
            pushed = push(owner, value);
            return pushed;
        }
    "#;
    let click_source = r#"
        resource storage(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact loadable(owner->data[0..owner->len]);
            fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        }

        resource allocated(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            contains allocation(owner->data, owner->cap * 4);
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact 1 <= owner->cap;
            fact loadable(owner->data[0..owner->len]);
            fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        }

        verifying "push.c";
        verifying "caller.c";

        int32 push(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            owns storage(owner);
            mutable owner->len, owner->data[owner->len..owner->len + 1];
            ensures result == old(owner->len) + 1;
            ensures owner->len == old(owner->len) + 1;
            ensures 1 <= owner->len;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
        } by {
            unfold(storage(owner));
            execute();
            fold(storage(owner));
            frame();
            simp();
        }

        int32 caller(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            consumes allocated(owner);
            mutable owner->len, owner->data[owner->len..owner->len + 1];
            produces allocated(owner);
            ensures result == old(owner->len) + 1;
            ensures result == old(owner->len) + 1 or result == 0;
            ensures owner->len == old(owner->len) + 1;
        } by {
            unfold(allocated(owner));
            fold(storage(owner));
            execute_until(statement(2));
            unfold(storage(owner));
            have 1 <= owner->cap by simp;
            fold(allocated(owner));
            execute();
            frame();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("push.c", push_c), ("caller.c", caller_c)])
        .expect("a storage-only callee should preserve its caller's allocation authority");
}

#[test]
fn exact_struct_field_offsets_remain_resolvable_after_deadline() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100000))),
            byte_width: 4,
        },
    };
    let field = base.offset_by_bytes(4);

    let index = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        super::checking::pointer_element_index_from_base(&field, &base, &Assumptions::new())
    });

    assert_eq!(index, Some(Bitvector32Term::Constant(1)));
}

#[test]
fn verifier_diagnostics_are_bounded_deterministically_at_utf8_boundaries() {
    use std::cell::Cell;

    struct CountingDebug<'a>(&'a Cell<usize>);

    impl fmt::Debug for CountingDebug<'_> {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            for _ in 0..10_000 {
                self.0.set(self.0.get() + 1);
                formatter.write_str("資源")?;
            }
            Ok(())
        }
    }

    let primary_cause = "owned_vector.grow path 2: ghost resource mismatch\n";
    let enormous = format!(
        "{primary_cause}{}",
        "資源".repeat(DEFAULT_DIAGNOSTIC_BYTE_LIMIT)
    );
    let first = super::diagnostics::bound_error_message_for_mode(enormous.clone(), false);
    let second = super::diagnostics::bound_error_message_for_mode(enormous.clone(), false);

    assert_eq!(first, second);
    assert!(first.starts_with(primary_cause));
    assert!(first.len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
    assert!(first.contains("diagnostic truncated"));
    assert_eq!(
        super::diagnostics::bound_error_message_for_mode(enormous.clone(), true),
        enormous
    );

    let writes = Cell::new(0);
    let debug = super::diagnostics::bounded_debug_for_mode(&CountingDebug(&writes), false);
    assert!(
        writes.get() < 10_000,
        "bounded formatting must stop the producer"
    );
    assert!(debug.len() <= 2 * 1024);
    assert!(debug.contains("diagnostic truncated"));
}

#[test]
fn missing_contract_load_diagnostic_omits_raw_memory_snapshots() {
    let error = super::checking::evaluate_contract_memory_load_from_memory(
        &CMemory::new(),
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100000))),
                byte_width: 4,
            },
        },
        CType::Int32,
        &Assumptions::new(),
    )
    .expect_err("an unowned external load should require loadability");

    assert!(error.contains("missing pure fact: loadable"), "{error}");
    assert!(error.contains("could not be read as Int32"), "{error}");
    assert!(!error.contains("CMemory"), "{error}");
    assert!(!error.contains("Pointer {"), "{error}");
    assert!(error.len() < 1_000, "{error}");
}

#[test]
fn certificate_reconstruction_diagnostics_summarize_internal_snapshots() {
    let memory = CMemory::new().with_block("hidden-snapshot", 4);
    let fact = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(Pointer {
                    block: "hidden-snapshot".into(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
            )),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let failures = (0..20)
        .map(|_| {
            (
                fact.clone(),
                ClickError::new(
                    "comparison fact has no replayable Surface Click spelling at this proof point",
                ),
            )
        })
        .collect::<Vec<_>>();

    let rendered = super::diagnostics::describe_unexpressed_pure_facts(&failures, &[], &[]);

    assert!(rendered.contains("int32 equality is true"), "{rendered}");
    assert!(
        rendered.contains("no replayable Surface Click spelling"),
        "{rendered}"
    );
    assert!(rendered.contains("8 more omitted"), "{rendered}");
    assert!(!rendered.contains("CMemory"), "{rendered}");
    assert!(!rendered.contains("hidden-snapshot"), "{rendered}");
}

#[test]
fn condition_certificate_search_reports_its_budget_without_dumping_snapshots() {
    let memory = CMemory::new().with_block("wide-hidden-snapshot", 256);
    let memory = crate::kernel::intern_c_memory(memory);
    let facts = (0u32..64)
        .map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::MemoryLoad(
                        memory.clone(),
                        Box::new(Pointer {
                            block: "wide-hidden-snapshot".into(),
                            offset: PointerOffsetTerm::Constant(i64::from(index) * 4),
                        }),
                    )),
                    Box::new(Bitvector32Term::Constant(index)),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Variable(Variable(2))),
        ),
        true,
    );
    let limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(1),
        smart: std::time::Duration::ZERO,
        control: std::time::Duration::from_secs(1),
    };
    let tactic = crate::instrumentation::TacticEvent {
        claim: "wide-condition.contract".to_string(),
        tactic_index: 0,
        tactic_name: "execute_until".to_string(),
        class: "smart".to_string(),
        statement_index: 0,
        source_index: 0,
    };

    let error = crate::instrumentation::with_tactic_limits(limits, || {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticStarted(
            tactic.clone(),
        ));
        let result = super::proof::search_condition_derivation(&goal, &facts)
            .expect_err("a zero smart budget should stop condition-certificate search");
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFailed(
            tactic,
        ));
        result
    });

    assert!(
        error
            .message()
            .contains("condition-certificate premise search exceeded"),
        "{error:?}"
    );
    assert!(
        error.message().contains("int32 equality is true"),
        "{error:?}"
    );
    assert!(
        error.message().contains("ambient condition facts: 64"),
        "{error:?}"
    );
    assert!(error.message().contains("exact premises"), "{error:?}");
    assert!(!error.message().contains("CMemory"), "{error:?}");
    assert!(
        !error.message().contains("wide-hidden-snapshot"),
        "{error:?}"
    );
}

#[test]
fn condition_certificate_search_is_not_sensitive_to_a_fact_prefix() {
    let mut facts = (0u32..64)
        .map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(Variable(100 + u64::from(index)))),
                    Box::new(Bitvector32Term::Constant(index)),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let left = Bitvector32Term::Variable(Variable(1));
    let middle = Bitvector32Term::Variable(Variable(2));
    let right = Bitvector32Term::Variable(Variable(3));
    facts.push(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(middle.clone())),
        true,
    ));
    facts.push(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(middle), Box::new(right.clone())),
        true,
    ));
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );

    let derivation = super::proof::search_condition_derivation(&goal, &facts)
        .expect("condition search should remain within the verification budget")
        .expect("the two relevant facts should derive the goal even after 64 irrelevant facts");

    assert_eq!(derivation.context_premises().len(), 2);
    assert!(
        derivation.replay(&assumptions_from_propositions(&facts)),
        "the selected certificate premises must replay"
    );
}

#[test]
fn verifier_diagnostics_bound_fact_items_and_show_resource_deltas() {
    let facts = (0..20)
        .map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Constant(index)),
                    Box::new(Bitvector32Term::Constant(index)),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let rendered = super::diagnostics::describe_pure_facts(&facts);
    assert!(rendered.contains("8 more omitted"), "{rendered}");

    let desired_resource = CResourceFact::own_composite(
        "owned_vector".to_string(),
        vec![CValue::Pointer(Pointer::null())],
    );
    let certified_resource = CResourceFact::own_composite(
        "allocation".to_string(),
        vec![CValue::Pointer(Pointer::null())],
    );
    let desired = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(desired_resource)),
    };
    let certified = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(certified_resource)),
    };
    let delta = super::diagnostics::describe_function_outcome_delta(&desired, &certified, &[], &[]);
    assert!(delta.contains("missing certified resources"), "{delta}");
    assert!(delta.contains("owned_vector"), "{delta}");
    assert!(delta.contains("extra certified resources"), "{delta}");
    assert!(delta.contains("allocation"), "{delta}");
    assert!(!delta.contains("CFunctionOutcome"), "{delta}");
}

#[test]
fn simp_uses_assumed_compound_proposition() {
    let proposition = Proposition::Or(
        Box::new(Proposition::Predicate {
            name: "left".to_string(),
            arguments: Vec::new(),
        }),
        Box::new(Proposition::Predicate {
            name: "right".to_string(),
            arguments: Vec::new(),
        }),
    );
    let assumptions = Assumptions::new().assume_proposition(proposition.clone());

    assert_eq!(
        simp_proposition(&proposition, &assumptions),
        SimpProposition::True
    );
}
