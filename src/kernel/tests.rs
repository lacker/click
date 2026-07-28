use super::prelude::*;

fn memory_range(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CMemoryRange {
    CMemoryRange::new(base, start.into(), end.into())
}

fn read_element(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::view_memory(memory_range(base, start, end))
}

fn write_element(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::own_memory(memory_range(base, start, end))
}

fn read_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(read_element(base, start, end))
}

fn write_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(write_element(base, start, end))
}

fn assert_replayable_derivation(assumptions: &Assumptions, proposition: &Proposition) {
    let derivation = assumptions
        .derive_proposition(proposition)
        .expect("expected an explicit proposition derivation");
    assert_eq!(derivation.conclusion(), proposition);
    assert!(
        derivation.replay(assumptions),
        "explicit proposition derivation must replay"
    );
}

#[test]
fn strict_reverse_order_derives_a_false_comparison() {
    let left = Bitvector32Term::Variable(Variable(200));
    let right = Bitvector32Term::Variable(Variable(201));
    let reverse = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(right.clone(), left.clone()),
        true,
    );
    let target = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), false);
    let assumptions = Assumptions::new().assume_proposition(reverse.clone());
    let derivation = assumptions
        .derive_proposition(&target)
        .expect("a strict reverse order should prove the comparison false");
    assert_eq!(derivation.context_premises(), vec![reverse]);
    assert!(derivation.replay(&assumptions));
    assert!(
        assumptions
            .clone()
            .defer_non_exact_loadability_obligations()
            .derive_proposition(&target)
            .is_some(),
        "proof construction remains available when symbolic execution defers search"
    );
}

#[test]
fn condition_fact_matching_ignores_unrelated_local_memory() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_000)), 4),
    };
    let owner_field = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::add(owner.offset.clone(), PointerOffsetTerm::Constant(4)),
    };
    let ignored_local = Pointer {
        block: "local:ignored".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let empty_memory = CMemory::new();
    let old_memory = empty_memory.clone().store(
        owner.clone(),
        int32(Bitvector32Term::MemoryLoad(
            Box::new(empty_memory),
            Box::new(owner),
        )),
    );
    let before_local = CMemory::new()
        .with_block("call-havoc:8000000", 0)
        .with_block("local:ignored", 4);
    let after_local = before_local
        .clone()
        .with_block("local:ignored", 4)
        .store(ignored_local, int32(Bitvector32Term::Variable(Variable(1))));
    let old_load = Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(owner_field.clone()));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before_local), Box::new(owner_field.clone())),
            old_load.clone(),
        ),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after_local), Box::new(owner_field)),
            old_load,
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(fact);

    assert_replayable_derivation(&assumptions, &target);
}

#[test]
fn equality_chains_across_observationally_equivalent_memory_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_000)), 4),
    };
    let observed = CMemory::local_pointer("observed");
    let before_materialized = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0)
        .with_block(observed.block.clone(), 4)
        .store(observed, int32(Bitvector32Term::Variable(Variable(10))));
    let before_sparse = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0);
    let after = before_sparse.clone().with_block("call-havoc:3", 0);
    let before_materialized_load =
        Bitvector32Term::MemoryLoad(Box::new(before_materialized), Box::new(owner.clone()));
    let before_sparse_load =
        Bitvector32Term::MemoryLoad(Box::new(before_sparse), Box::new(owner.clone()));
    let after_load = Bitvector32Term::MemoryLoad(Box::new(after), Box::new(owner));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(before_materialized_load, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(after_load.clone(), before_sparse_load),
            true,
        );
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(after_load, Bitvector32Term::Constant(1)),
        true,
    );

    assert_replayable_derivation(&assumptions, &target);
}

#[test]
fn proposition_derivation_proves_implication_from_false_antecedent() {
    let condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(1)),
        Bitvector32Term::Constant(0),
    );
    let antecedent = Proposition::ConditionIs(condition.clone(), false);
    let conclusion = Proposition::Implies(
        Box::new(antecedent),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(2)),
                Bitvector32Term::Variable(Variable(3)),
            ),
            true,
        )),
    );
    let assumptions = Assumptions::new().assume_condition(condition, true);

    let derivation = assumptions
        .derive_simp_proposition(&conclusion)
        .expect("a false antecedent should prove an implication");
    assert!(derivation.replay(&assumptions));
}

#[test]
fn bitwise_xor_normalizes_swap_identities() {
    let x = Bitvector32Term::Variable(Variable(1));
    let y = Bitvector32Term::Variable(Variable(2));
    let x_xor_y = Bitvector32Term::bitwise_xor(x.clone(), y.clone());
    let recovered_x = Bitvector32Term::bitwise_xor(y.clone(), x_xor_y.clone());
    let recovered_y = Bitvector32Term::bitwise_xor(x_xor_y, x.clone());

    assert_eq!(recovered_x, x);
    assert_eq!(recovered_y, y);
}

#[test]
fn join_state_forgets_changed_scalars_and_memory() {
    let stable_x = int32(Bitvector32Term::Variable(Variable(7)));
    let pointer = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state_zero = CState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(0))
        .with_memory(
            CMemory::new()
                .with_block("heap", 4)
                .store(pointer.clone(), int32(0)),
        )
        .with_resource_context(write_context(pointer.clone(), 0, 1));
    let state_one = CState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(1))
        .with_memory(
            CMemory::new()
                .with_block("heap", 4)
                .store(pointer, int32(1)),
        );
    let stable = BTreeMap::from([("x".to_string(), stable_x.clone())]);

    let abstract_zero =
        abstract_c_state_for_join(&state_zero, &stable, 10_000).expect("join abstraction");
    let abstract_one =
        abstract_c_state_for_join(&state_one, &stable, 10_000).expect("join abstraction");

    assert_eq!(abstract_zero, abstract_one);
    assert_eq!(abstract_zero.locals().get("x"), Some(&stable_x));
    assert_ne!(abstract_zero.locals().get("y"), Some(&int32(0)));
    assert!(abstract_zero.resources().is_empty());
}

#[test]
fn join_state_abstracts_changed_pointer_locals() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let abstract_left = abstract_c_state_for_join(
        &CState::new().with_local("selected", CValue::Pointer(left)),
        &BTreeMap::new(),
        20_000,
    )
    .expect("pointer join abstraction");
    let abstract_right = abstract_c_state_for_join(
        &CState::new().with_local("selected", CValue::Pointer(right)),
        &BTreeMap::new(),
        20_000,
    )
    .expect("pointer join abstraction");

    assert_eq!(abstract_left, abstract_right);
    let Some(CValue::Pointer(selected)) = abstract_left.locals().get("selected") else {
        panic!("selected should remain a pointer local");
    };
    assert!(selected.has_symbolic_block());
}

#[test]
fn symbolic_pointer_blocks_do_not_imply_non_aliasing() {
    let symbolic = Pointer::symbolic(Variable(21_000));
    let concrete = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert!(!pointers_proven_distinct(
        &symbolic,
        &concrete,
        &Assumptions::new()
    ));
    assert_eq!(
        Assumptions::new().decide(&ConditionTerm::pointer_equal(symbolic, concrete)),
        None
    );
}

#[test]
fn concrete_pointer_block_names_cannot_create_symbolic_identity() {
    let misleading_name = Pointer {
        block: "symbolic-pointer:21000".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let heap = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert!(!misleading_name.has_symbolic_block());
    assert!(misleading_name.blocks_proven_distinct(&heap));
}

#[test]
fn resource_family_cores_are_view_facts() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert_eq!(
        read_element(base.clone(), 0, 1).core(),
        Some(read_element(base.clone(), 0, 1))
    );
    assert_eq!(
        write_element(base.clone(), 0, 1).core(),
        Some(read_element(base, 0, 1))
    );
    assert_eq!(
        CResourceFact::own_token("token".to_string(), vec![int32(0)]).core(),
        Some(CResourceFact::view_token(
            "token".to_string(),
            vec![int32(0)]
        ))
    );
    assert_eq!(
        CResourceFact::own_composite("box".to_string(), vec![int32(1)]).core(),
        Some(CResourceFact::view_composite(
            "box".to_string(),
            vec![int32(1)]
        ))
    );
}

#[test]
fn exact_resource_families_reject_duplicate_owned_facts() {
    for fact in [
        CResourceFact::own_token("token".to_string(), vec![int32(0)]),
        CResourceFact::own_composite("box".to_string(), vec![int32(1)]),
    ] {
        let error = ResourceContext::new()
            .try_compose_with_facts([fact.clone(), fact.clone()], &Assumptions::new())
            .expect_err("duplicate exact owned resources must be invalid");
        assert_eq!(
            error,
            ResourceContextValidityError::DuplicateOwnedResourceFact(fact)
        );
    }
}

#[test]
fn exact_resource_views_are_preserved_when_satisfied() {
    for (owned, viewed) in [
        (
            CResourceFact::own_token("token".to_string(), vec![int32(0)]),
            CResourceFact::view_token("token".to_string(), vec![int32(0)]),
        ),
        (
            CResourceFact::own_composite("box".to_string(), vec![int32(1)]),
            CResourceFact::view_composite("box".to_string(), vec![int32(1)]),
        ),
    ] {
        let context = ResourceContext::new().unchecked_with_fact(owned.clone());
        let after_view = context
            .without_fact(&viewed, &Assumptions::new())
            .expect("owned exact resource should satisfy its view");
        assert_eq!(after_view.facts(), &[owned]);
    }
}

#[test]
fn batch_resource_consumption_splits_without_repeated_normalization() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 0, 3)));
    let required = [
        CResourceFact::own_memory(memory_range(base.clone(), 0, 1)),
        CResourceFact::own_memory(memory_range(base, 1, 3)),
    ];

    let remaining = context
        .without_facts(&required, &Assumptions::new())
        .expect("both subranges should be consumable");

    assert!(remaining.is_empty());
}

#[test]
fn batch_resource_consumption_normalizes_when_a_requirement_needs_a_merge() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 0, 1)))
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 1, 2)));
    let required = [CResourceFact::own_memory(memory_range(base, 0, 2))];

    let remaining = context
        .without_facts(&required, &Assumptions::new())
        .expect("adjacent ranges should merge before consumption");

    assert!(remaining.is_empty());
}

#[test]
fn resource_context_observes_write_separation() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = memory_range(base.clone(), 0, 1);
    let right = memory_range(base.clone(), 1, 2);
    let facts = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(left.clone()))
        .unchecked_with_fact(CResourceFact::own_memory(right.clone()))
        .observable_facts(&Assumptions::new())
        .expect("adjacent writes should be a valid resource context");

    assert_eq!(
        facts,
        vec![Proposition::CResourceSeparate {
            left: CResource::Memory(left),
            right: CResource::Memory(right),
        }]
    );
}

#[test]
fn resource_context_observes_same_and_cross_family_separation() {
    let memory = CResource::Memory(memory_range(
        Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let token = CResource::Token {
        name: "left".to_string(),
        arguments: vec![],
    };
    let other_token = CResource::Token {
        name: "right".to_string(),
        arguments: vec![],
    };
    let facts = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::Own(memory.clone()))
        .unchecked_with_fact(CResourceFact::Own(token.clone()))
        .unchecked_with_fact(CResourceFact::Own(other_token.clone()))
        .observable_facts(&Assumptions::new())
        .expect("distinct owned resources should compose validly");

    assert!(facts.contains(&Proposition::CResourceSeparate {
        left: token.clone(),
        right: other_token,
    }));
    assert!(facts.contains(&Proposition::CResourceSeparate {
        left: memory,
        right: token,
    }));
}

#[test]
fn resource_separation_proves_memory_disjointness() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = memory_range(base.clone(), 0, 1);
    let right = memory_range(base.clone(), 1, 2);
    let assumptions = Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(left),
        right: CResource::Memory(right),
    });

    assert!(assumptions.proves(&Proposition::CMemoryDisjoint {
        left_base: base.clone(),
        left_start: Bitvector32Term::Constant(0),
        left_end: Bitvector32Term::Constant(1),
        right_base: base,
        right_start: Bitvector32Term::Constant(1),
        right_end: Bitvector32Term::Constant(2),
    }));
}

#[test]
fn resource_separation_covers_larger_memory_range() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left_first = CResource::Memory(memory_range(base.clone(), 0, 1));
    let left_second = CResource::Memory(memory_range(base.clone(), 1, 2));
    let left_combined = CResource::Memory(memory_range(base.clone(), 0, 2));
    let right = CResource::Memory(memory_range(base, 10, 11));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: left_first,
            right: right.clone(),
        })
        .assume_proposition(Proposition::CResourceSeparate {
            left: left_second,
            right: right.clone(),
        });

    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: left_combined,
        right,
    }));
}

#[test]
fn resource_separation_transports_across_equal_memory_ranges() {
    let target = Pointer::symbolic(Variable(20_100));
    let original_data = Pointer::symbolic(Variable(20_101));
    let equal_data = Pointer::symbolic(Variable(20_102));
    let original_length = Bitvector32Term::Variable(Variable(20_103));
    let equal_length = Bitvector32Term::Variable(Variable(20_104));
    let target_resource = CResource::Memory(memory_range(target, 0, 4));
    let original_resource = CResource::Memory(memory_range(
        original_data.clone(),
        0,
        original_length.clone(),
    ));
    let equal_resource =
        CResource::Memory(memory_range(equal_data.clone(), 0, equal_length.clone()));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: target_resource.clone(),
            right: original_resource,
        })
        .assume_condition(
            ConditionTerm::pointer_equal(original_data, equal_data),
            true,
        )
        .assume_condition(ConditionTerm::equal(original_length, equal_length), true);

    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: target_resource,
        right: equal_resource,
    }));
}

#[test]
fn resource_contains_projects_separation_to_children() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let parent = CResource::Token {
        name: "parent".to_string(),
        arguments: vec![],
    };
    let child = CResource::Memory(memory_range(base.clone(), 0, 1));
    let other = CResource::Memory(memory_range(base.clone(), 1, 2));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: parent.clone(),
            right: other.clone(),
        })
        .assume_proposition(Proposition::CResourceContains {
            parent,
            child: child.clone(),
        });

    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: child,
        right: other,
    }));
}

#[test]
fn checked_resource_composition_rejects_invalid_state_before_normalizing() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let error = ResourceContext::new()
        .try_compose_with_facts(
            [
                write_element(base.clone(), 0, 1),
                write_element(base.clone(), 0, 1),
            ],
            &Assumptions::new(),
        )
        .expect_err("duplicate writes must be rejected before normalization");

    assert_eq!(
        error,
        ResourceContextValidityError::OverlappingWriteResources {
            left: memory_range(base.clone(), 0, 1),
            right: memory_range(base, 0, 1),
        }
    );
}

#[test]
fn concrete_max_executes_without_list_encoding() {
    let state = c_max_state(int32(0), int32(1));
    let theorem =
        prove_c_statement_execution(state.clone(), c_max_body()).expect("max should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement: c_max_body(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );
}

#[test]
fn concrete_max_function_call_preserves_caller_locals() {
    let state = CState::new().with_local("caller", int32(99));
    let function = c_max_function();
    let arguments = vec![c_int32_literal(0), c_int32_literal(1)];
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    )
    .expect("max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: CFunctionOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );
}

#[test]
fn symbolic_max_function_call_reports_branch_facts() {
    let a = Variable(14);
    let b = Variable(15);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = CState::new();
    let function = c_max_function();
    let arguments = vec![
        CExpression::Value(int32(a_bits.clone())),
        CExpression::Value(int32(b_bits.clone())),
    ];
    let execution = prove_symbolic_c_function_execution_paths(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    );

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: CFunctionOutcome::Return {
                    value: int32(b_bits),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition.clone(), false)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, false)),
            Box::new(Proposition::CFunctionExecutes {
                state: state.clone(),
                function,
                arguments,
                outcome: CFunctionOutcome::Return {
                    value: int32(a_bits),
                    state,
                },
            }),
        )
    );
}

#[test]
fn function_call_threads_memory_but_discards_callee_locals() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_local("caller", int32(42))
        .with_resource_context(resources.clone());
    let function = c_function(
        CType::Int32,
        "store_and_load",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_load(c_variable("p"))),
        ),
    );
    let arguments = vec![c_pointer_value(pointer.clone())];
    let final_state = CState::new()
        .with_local("caller", int32(42))
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    )
    .expect("store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: CFunctionOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn function_call_does_not_inherit_undeclared_resources() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources);
    let helper = c_function(
        CType::Int32,
        "store_and_load",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_load(c_variable("p"))),
        ),
    );
    let caller = c_function(
        CType::Int32,
        "caller",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_call_assign("result", "store_and_load", vec![c_variable("p")]),
    );
    let arguments = vec![c_pointer_value(pointer.clone())];
    let theorem = prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        arguments.clone(),
        Assumptions::new(),
        CExecutionEnvironment::new().with_function(helper),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("call should report missing callee permission");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments,
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource: write_element(pointer, 0, 1),
            }),
        }
    );
}

#[test]
fn concrete_function_specification_is_native_theorem() {
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![c_int32_literal(0), c_int32_literal(1)],
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        Assumptions::new(),
    )
    .expect("concrete max specification should prove");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionSatisfiesSpecification {
            function,
            specification
        }
    );
}

#[test]
fn symbolic_function_specification_uses_requirements_as_execution_pure_facts() {
    let a = Variable(16);
    let b = Variable(17);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![
            CExpression::Value(int32(a_bits)),
            CExpression::Value(int32(b_bits)),
        ],
        vec![Proposition::ConditionIs(condition.clone(), true)],
        CFunctionOutcome::Return {
            value: int32(Bitvector32Term::Variable(b)),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        Assumptions::new(),
    )
    .expect("symbolic branch specification should prove under condition");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, true)),
            Box::new(Proposition::CFunctionSatisfiesSpecification {
                function,
                specification
            }),
        )
    );
}

#[test]
fn symbolic_max_branch_specifications_include_bounds() {
    let a = Variable(60);
    let b = Variable(61);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let function = c_max_function();
    let arguments = vec![
        CExpression::Value(int32(a_bits.clone())),
        CExpression::Value(int32(b_bits.clone())),
    ];
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());

    let right_specification = c_function_specification(
        CState::new(),
        arguments.clone(),
        vec![Proposition::ConditionIs(condition.clone(), true)],
        CFunctionOutcome::Return {
            value: int32(b_bits.clone()),
            state: CState::new(),
        },
    );
    prove_c_function_satisfies_specification_and_propositions(
        function.clone(),
        right_specification,
        Assumptions::new(),
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(b_bits.clone(), a_bits.clone()),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(b_bits.clone(), b_bits.clone()),
                true,
            ),
        ],
    )
    .expect("under a < b, max returns b and b is >= both inputs");

    let left_specification = c_function_specification(
        CState::new(),
        arguments,
        vec![Proposition::ConditionIs(condition, false)],
        CFunctionOutcome::Return {
            value: int32(a_bits.clone()),
            state: CState::new(),
        },
    );
    prove_c_function_satisfies_specification_and_propositions(
        function,
        left_specification,
        Assumptions::new(),
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(a_bits.clone(), a_bits.clone()),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_greater_equal(a_bits, b_bits), true),
        ],
    )
    .expect("under not (a < b), max returns a and a is >= both inputs");
}

#[test]
fn symbolic_clamp_branch_specifications_include_bounds_under_ordered_limits() {
    let x = Variable(62);
    let lo = Variable(63);
    let hi = Variable(64);
    let x_bits = Bitvector32Term::Variable(x);
    let lo_bits = Bitvector32Term::Variable(lo);
    let hi_bits = Bitvector32Term::Variable(hi);
    let ordered_limits = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lo_bits.clone(), hi_bits.clone()),
        true,
    );
    let below_lo = ConditionTerm::signed_less_than(x_bits.clone(), lo_bits.clone());
    let above_hi = ConditionTerm::signed_greater_than(x_bits.clone(), hi_bits.clone());
    let function = c_function(
        CType::Int32,
        "clamp",
        vec![
            c_parameter("x", CType::Int32),
            c_parameter("lo", CType::Int32),
            c_parameter("hi", CType::Int32),
        ],
        c_if(
            c_less_than(c_variable("x"), c_variable("lo")),
            c_return(c_variable("lo")),
            c_if(
                c_greater_than(c_variable("x"), c_variable("hi")),
                c_return(c_variable("hi")),
                c_return(c_variable("x")),
            ),
        ),
    );
    let arguments = vec![
        CExpression::Value(int32(x_bits.clone())),
        CExpression::Value(int32(lo_bits.clone())),
        CExpression::Value(int32(hi_bits.clone())),
    ];

    for (requires, result, message) in [
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), true),
            ],
            lo_bits.clone(),
            "x below lo returns lo within bounds",
        ),
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), false),
                Proposition::ConditionIs(above_hi.clone(), true),
            ],
            hi_bits.clone(),
            "x above hi returns hi within bounds",
        ),
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), false),
                Proposition::ConditionIs(above_hi.clone(), false),
            ],
            x_bits.clone(),
            "x already in range returns x within bounds",
        ),
    ] {
        let specification = c_function_specification(
            CState::new(),
            arguments.clone(),
            requires,
            CFunctionOutcome::Return {
                value: int32(result.clone()),
                state: CState::new(),
            },
        );
        prove_c_function_satisfies_specification_and_propositions(
            function.clone(),
            specification,
            Assumptions::new(),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(result.clone(), lo_bits.clone()),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(result, hi_bits.clone()),
                    true,
                ),
            ],
        )
        .expect(message);
    }
}

#[test]
fn incomplete_symbolic_function_specification_does_not_prove() {
    let a = Variable(18);
    let b = Variable(19);
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![
            CExpression::Value(int32(Bitvector32Term::Variable(a))),
            CExpression::Value(int32(Bitvector32Term::Variable(b))),
        ],
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(Bitvector32Term::Variable(b)),
            state: CState::new(),
        },
    );

    assert!(
        prove_c_function_satisfies_specification(function, specification, Assumptions::new())
            .is_none()
    );
}

#[test]
fn call_assign_uses_function_environment() {
    let increment = c_function(
        CType::Int32,
        "increment",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_add(c_variable("x"), c_int32_literal(1))),
    );
    let environment = CExecutionEnvironment::new().with_function(increment);
    let state = CState::new();
    let statement = c_seq(
        c_call_assign("result", "increment", vec![c_int32_literal(41)]),
        c_return(c_variable("result")),
    );
    let final_state = CState::new().with_local("result", int32(42));
    let theorem = prove_symbolic_c_execution_with_environment(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("known function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(42),
                state: final_state,
            },
        }
    );
}

#[test]
fn loop_semantics_explicitly_select_verification_or_verified_rules() {
    let state = CState::new().with_local("i", int32(0));
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
    );
    let assumptions = Assumptions::new();
    let (certified, loop_rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            assumptions.clone(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
    let loop_rule = loop_rule.expect("loop verification should produce a rule");

    let missing = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(missing.paths().is_empty());

    let mut ignored_rule = loop_rule.clone();
    ignored_rule.paths.clear();
    let verified_directly = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new().with_verified_loop_rules([ignored_rule]),
        CExecutionSemantics::EXECUTE_BODIES,
    );
    assert!(!verified_directly.paths().is_empty());

    let reused = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions
            .clone()
            .assume_condition(ConditionTerm::Constant(true), true),
        CExecutionEnvironment::new().with_verified_loop_rules([loop_rule.clone()]),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(reused.paths().len(), certified.paths().len());

    let mismatched = prove_symbolic_c_statement_verification_paths_with_environment(
        state.with_local("unrelated", int32(0)),
        statement,
        assumptions,
        CExecutionEnvironment::new().with_verified_loop_rules([loop_rule]),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(mismatched.paths().is_empty());
}

#[test]
fn loop_exit_rule_with_proven_preservation_does_not_reverify_the_body() {
    let state = CState::new().with_local("i", int32(0));
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_int32_literal(u32::MAX)),
    );
    let assumptions = Assumptions::new();
    let automatic = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    );
    assert!(
        automatic
            .paths()
            .iter()
            .flat_map(SymbolicCExecutionPath::obligations)
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );

    let (after_proof, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        false,
        true,
    );
    assert!(loop_rule.is_some());
    assert!(after_proof.paths().iter().all(|path| {
        path.obligations()
            .iter()
            .all(|obligation| obligation.context() != Some("loop preservation"))
    }));
}

#[test]
fn loop_exit_with_unproven_preservation_does_not_produce_rule() {
    let state = CState::new().with_local("i", int32(u32::MAX));
    let statement = c_while_with_invariant_checks(
        c_int32_literal(1),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_int32_literal(u32::MAX)),
    );
    let (execution, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases(
        state,
        statement,
        Assumptions::new(),
        CExecutionEnvironment::new(),
        true,
        false,
    );

    assert!(loop_rule.is_none());
    let obligations = execution
        .paths()
        .iter()
        .flat_map(SymbolicCExecutionPath::obligations)
        .collect::<Vec<_>>();
    assert!(
        obligations
            .iter()
            .all(|obligation| obligation.context() != Some("loop entry"))
    );
    assert!(
        obligations
            .iter()
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );
}

#[test]
fn unknown_call_assign_is_runtime_error() {
    let state = CState::new();
    let statement = c_call_assign("result", "missing", Vec::new());
    let theorem = prove_symbolic_c_execution_with_environment(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("unknown function should produce a single runtime-error path");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                "missing".to_string(),
            )),
        }
    );
}

#[test]
fn while_loop_executes_concrete_countdown() {
    let state = CState::new().with_local("x", int32(3));
    let loop_statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        Vec::new(),
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let statement = c_seq(loop_statement, c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(0));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete countdown loop should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: final_state,
            },
        }
    );
}

#[test]
fn loop_budget_exhaustion_is_executor_failure_not_c_runtime_error() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_while(
        c_int32_literal(1),
        Vec::new(),
        c_assign("x", c_variable("x")),
    );
    let budget = ExecutionBudget::new().with_loop_unrolls(2);
    let execution = prove_symbolic_c_execution_paths_with_budget(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        budget.clone(),
    );

    assert_eq!(execution.limit(), Some(ExecutionLimit::LoopUnrolls));
    assert_eq!(execution.paths(), &[] as &[SymbolicCExecutionPath]);
    assert!(
        prove_symbolic_c_execution_with_budget(state, statement, Assumptions::new(), budget,)
            .is_none()
    );
}

#[test]
fn executor_budgets_cap_steps_calls_and_paths() {
    let state = CState::new();
    let statement = c_return(c_int32_literal(1));

    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            ExecutionBudget::new().with_statement_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::StatementSteps)
    );
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement,
            Assumptions::new(),
            ExecutionBudget::new().with_expression_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::ExpressionSteps)
    );

    let function = c_function(
        CType::Int32,
        "id",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    );
    assert_eq!(
        prove_symbolic_c_function_execution_paths_with_budget(
            CState::new(),
            function,
            vec![c_int32_literal(1)],
            Assumptions::new(),
            ExecutionBudget::new().with_function_calls(0),
        )
        .limit(),
        Some(ExecutionLimit::FunctionCalls)
    );

    let a = Variable(75);
    let b = Variable(76);
    let branchy_statement = c_return(c_less_than(
        CExpression::Value(int32(Bitvector32Term::Variable(a))),
        CExpression::Value(int32(Bitvector32Term::Variable(b))),
    ));
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state,
            branchy_statement,
            Assumptions::new(),
            ExecutionBudget::new().with_paths(3),
        )
        .limit(),
        Some(ExecutionLimit::Paths)
    );
}

#[test]
fn while_invariant_is_proof_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invariant = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let state = CState::new().with_local("x", int32(0));
    let statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        vec![invariant.clone()],
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("false loop should execute under invariant obligation");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(invariant),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(state),
            }),
        )
    );
}

#[test]
fn builtin_obligation_solver_proves_trivial_props() {
    let assumptions = Assumptions::new();
    let memory = CMemory::new().with_block("block", 8);
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };

    assert!(assumptions.proves(&Proposition::Equal(
        Term::Bitvector32(Bitvector32Term::Constant(7)),
        Term::Bitvector32(Bitvector32Term::Constant(7)),
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::Constant(true),
        true
    )));
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
}

#[test]
fn deferred_obligations_keep_contextual_memory_proofs_explicit() {
    let memory = CMemory::new();
    let base = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: Bitvector32Term::Constant(8),
    };
    let element = Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new().assume_proposition(range);

    let mut ordinary = Vec::new();
    assert!(add_proof_obligation(&mut ordinary, &assumptions, element.clone()).is_some());
    assert!(
        ordinary.is_empty(),
        "ordinary execution may solve the range"
    );

    let mut deferred = Vec::new();
    let deferred_assumptions = assumptions.defer_non_exact_loadability_obligations();
    assert!(add_proof_obligation(&mut deferred, &deferred_assumptions, element.clone()).is_some());
    assert_eq!(deferred.len(), 1);
    assert_eq!(deferred[0].proposition(), &element);
}

#[test]
fn memory_derivation_records_the_selected_range_candidate() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: Pointer {
            block: "unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::Constant(64),
    };
    let selected = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(8),
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(unrelated)
        .assume_proposition(selected.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&target)
        .expect("the selected range should establish the element access");

    assert!(derivation.replay(&assumptions));
    assert_eq!(derivation.context_premises(), vec![selected]);
}

#[test]
fn loadable_symbolic_subrange_proves_an_indexed_cell() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let split = Bitvector32Term::Variable(Variable(87));
    let index = Bitvector32Term::Variable(Variable(88));
    let len = Bitvector32Term::Variable(Variable(89));
    let range = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(split.clone()),
        bytes: Bitvector32Term::multiply(
            Bitvector32Term::subtract(len.clone(), split.clone()),
            Bitvector32Term::Constant(4),
        ),
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(index.clone()),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(range)
        .assume_condition(ConditionTerm::signed_less_equal(split, index.clone()), true)
        .assume_condition(ConditionTerm::signed_less_than(index, len), true);

    assert!(
        assumptions.derive_atomic_proposition(&target).is_some(),
        "split <= index < len should select a cell from [split..len]"
    );
}

#[test]
fn proposition_derivation_replay_requires_its_context() {
    let x = Bitvector32Term::Variable(Variable(86));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x, Bitvector32Term::Constant(0)),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(proposition.clone());
    let derivation = assumptions
        .derive_simp_proposition(&proposition)
        .expect("exact fact should produce a derivation");

    assert!(derivation.replay(&assumptions));
    assert!(!derivation.replay(&Assumptions::new()));
    assert_eq!(derivation.context_premises(), vec![proposition]);
}

#[test]
fn implication_derivation_context_excludes_its_local_antecedent() {
    let antecedent = Proposition::Predicate {
        name: "local_hypothesis".to_string(),
        arguments: Vec::new(),
    };
    let goal = Proposition::Implies(Box::new(antecedent.clone()), Box::new(antecedent));
    let assumptions = Assumptions::new();
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("an implication may use its own antecedent");

    assert!(derivation.replay(&assumptions));
    assert!(
        derivation.context_premises().is_empty(),
        "binder-local assumptions are not ambient certificate premises"
    );
}

#[test]
fn finite_context_split_derivation_records_its_range_premises() {
    let variable = Variable(87);
    let value = Bitvector32Term::Variable(variable);
    let lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(3), value.clone()),
        true,
    );
    let upper = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(value, Bitvector32Term::Constant(3)),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone());
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the singleton finite range should establish equality");

    assert!(derivation.replay(&assumptions));
    assert!(!derivation.replay(&Assumptions::new()));
    let context = derivation.context_premises();
    assert!(context.contains(&lower));
    assert!(context.contains(&upper));
}

#[test]
fn successor_order_derivation_needs_only_an_upper_bound() {
    let index = Bitvector32Term::Variable(Variable(88));
    let upper = Bitvector32Term::Variable(Variable(89));
    let upper_bound =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(index.clone(), upper), true);
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::add(index.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let unrelated_order = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Variable(Variable(90)),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_proposition(unrelated_order)
        .assume_proposition(upper_bound.clone())
        .assume_proposition(Proposition::Predicate {
            name: "unrelated".to_string(),
            arguments: Vec::new(),
        });
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("an int32 value below another int32 value cannot overflow when incremented");

    assert!(derivation.replay(&assumptions));
    assert_eq!(derivation.context_premises(), vec![upper_bound]);
}

#[test]
fn assumptions_split_small_finite_context_variable() {
    let j = Bitvector32Term::Variable(Variable(87));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let proposition = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j, Bitvector32Term::Constant(1)),
            true,
        )),
    );

    assert!(assumptions.proves(&proposition));
    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn finite_context_derivation_replays_under_a_narrower_range() {
    let j = Bitvector32Term::Variable(Variable(88));
    let broad = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let proposition = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(1)),
            true,
        )),
    );
    let derivation = broad
        .derive_proposition(&proposition)
        .expect("the broad two-value range should produce a finite proof");
    let narrow = broad.assume_condition(
        ConditionTerm::signed_less_than(j, Bitvector32Term::Constant(1)),
        true,
    );

    assert!(
        derivation.replay(&narrow),
        "a proof covering a finite range remains valid when later facts narrow that range"
    );
}

#[test]
fn proposition_derivation_composes_case_split_conjuncts() {
    let j = Bitvector32Term::Variable(Variable(187));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let finite_choice = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j, Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(187)),
                Bitvector32Term::Constant(1),
            ),
            true,
        )),
    );
    let proposition = Proposition::And(Box::new(finite_choice.clone()), Box::new(finite_choice));

    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn finite_forall_order_fact_participates_in_transitive_order_path() {
    let memory = CMemory::new();
    let indexed_load = |index| {
        Bitvector32Term::MemoryLoad(
            Box::new(memory.clone()),
            Box::new(Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(index, 4),
            }),
        )
    };
    let k = Variable(88);
    let k_bits = Bitvector32Term::Variable(k);
    let load_k = indexed_load(k_bits.clone());
    let load_0 = indexed_load(Bitvector32Term::Constant(0));
    let load_1 = indexed_load(Bitvector32Term::Constant(1));
    let load_2 = indexed_load(Bitvector32Term::Constant(2));
    let finite_order_fact = Proposition::ForAll {
        var: k,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(k_bits, Bitvector32Term::Constant(1)),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(load_k, load_1.clone()),
                true,
            )),
        )),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(finite_order_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(load_1, load_2.clone()),
            true,
        );

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(load_0, load_2),
        true,
    )));
}

#[test]
fn conditional_forall_instantiates_at_same_named_variable_in_order_path() {
    let k = Variable(188);
    let k_bits = Bitvector32Term::Variable(k);
    let j = Bitvector32Term::Variable(Variable(189));
    let value_at_k = Bitvector32Term::MemoryLoad(
        Box::new(CMemory::new()),
        Box::new(Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(k_bits.clone(), 4),
        }),
    );
    let pivot = Bitvector32Term::Variable(Variable(191));
    let successor = Bitvector32Term::Variable(Variable(192));
    let induction_hypothesis = Proposition::ForAll {
        var: k,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), j.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(value_at_k.clone(), pivot.clone()),
                true,
            )),
        )),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(induction_hypothesis)
        .assume_condition(
            ConditionTerm::signed_less_than(
                k_bits.clone(),
                Bitvector32Term::add(j.clone(), Bitvector32Term::Constant(1)),
            ),
            true,
        )
        .assume_condition(ConditionTerm::equal(k_bits, j.clone()), false)
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j, Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(pivot, successor.clone()),
            true,
        );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value_at_k, successor),
        true,
    );

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("quantified order instance should produce a simplifier derivation");
    assert_eq!(derivation.conclusion(), &goal);
    assert!(derivation.replay(&assumptions));
}

#[test]
fn assumptions_prove_by_bounded_disjunction_cases() {
    let x = Bitvector32Term::Variable(Variable(89));
    let x_is_zero = Proposition::ConditionIs(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let x_is_one = Proposition::ConditionIs(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(Proposition::Or(
        Box::new(x_is_zero.clone()),
        Box::new(x_is_one.clone()),
    ));

    let proposition = Proposition::Or(Box::new(x_is_one), Box::new(x_is_zero));
    assert!(assumptions.proves(&proposition));
    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn known_memory_block_bounds_prove_symbolic_element_access() {
    let index = Variable(91);
    let index_bits = Bitvector32Term::Variable(index);
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index_bits.clone(), Bitvector32Term::Constant(3)),
            true,
        );
    let memory = CMemory::new().with_block("local:a", 12);
    let pointer = CMemory::local_pointer("a").offset_by_int32_elements(index_bits);

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
}

#[test]
fn symbolic_int32_range_directly_proves_constant_element_loadable() {
    let memory = CMemory::new();
    let base = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let length = Bitvector32Term::Variable(Variable(89));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
        });

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn assumptions_prove_forall_int32_array_range_body() {
    let index = Variable(90);
    let index_bits = Bitvector32Term::Variable(index);
    let memory = CMemory::new().with_block("block", 12);
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let indexed_pointer = base.offset_by_int32_elements(index_bits.clone());
    let in_segment = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(index_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(index_bits, Bitvector32Term::Constant(3)),
            true,
        )),
    );
    let loadable_index = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: indexed_pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryLoadable {
        memory,
        base,
        bytes: Bitvector32Term::Constant(12),
    });

    assert!(assumptions.proves(&forall_int32(
        index,
        Proposition::Implies(Box::new(in_segment), Box::new(loadable_index)),
    )));
}

#[test]
fn loadability_transports_to_snapshot_with_symbolic_index_bounds() {
    let index = Bitvector32Term::Variable(Variable(190));
    let cursor = Bitvector32Term::Variable(Variable(191));
    let range_memory = CMemory::new();
    let snapshot_memory = CMemory::new().with_block("local:j", 4);
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: range_memory,
            base: base.clone(),
            bytes: Bitvector32Term::Constant(12),
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), cursor.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(cursor.clone(), Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(cursor, Bitvector32Term::Constant(2)),
            false,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::Constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: snapshot_memory,
        base: base.offset_by_int32_elements(index),
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn assumptions_prove_finite_forall_int32_by_instantiation() {
    let i = Variable(92);
    let j = Variable(93);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let antecedent = Proposition::And(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(j_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
        )),
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(i_bits.clone(), j_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(3)),
                true,
            )),
        )),
    );
    let consequent = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        )),
    );

    assert!(Assumptions::new().proves(&forall_int32(
        i,
        forall_int32(
            j,
            Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
        ),
    )));
}

#[test]
fn assumptions_use_finite_forall_fact_to_prove_condition() {
    let k = Variable(94);
    let base_left = Bitvector32Term::Variable(Variable(95));
    let base_right = Bitvector32Term::Variable(Variable(96));
    let k_bits = Bitvector32Term::Variable(k);
    let antecedent = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
            true,
        )),
    );
    let consequent = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(base_left.clone()), Box::new(k_bits.clone())),
            Bitvector32Term::Add(Box::new(base_right.clone()), Box::new(k_bits)),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(forall_int32(
        k,
        Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
    ));

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(base_left), Box::new(Bitvector32Term::Constant(1))),
            Bitvector32Term::Add(Box::new(base_right), Box::new(Bitvector32Term::Constant(1))),
        ),
        true,
    )));
}

#[test]
fn order_solver_uses_negated_less_than_transitively() {
    let a = Bitvector32Term::Variable(Variable(94));
    let b = Bitvector32Term::Variable(Variable(95));
    let c = Bitvector32Term::Variable(Variable(96));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_than(b.clone(), a.clone()), false)
        .assume_condition(ConditionTerm::signed_less_than(c.clone(), b), false);

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(a, c),
        true,
    )));
}

#[test]
fn assumptions_do_not_prove_implication_by_treating_unknown_antecedent_as_false() {
    let x = Bitvector32Term::Variable(Variable(91));
    let antecedent = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let consequent =
        Proposition::ConditionIs(ConditionTerm::equal(x, Bitvector32Term::Constant(0)), true);

    assert!(!Assumptions::new().proves(&Proposition::Implies(
        Box::new(antecedent),
        Box::new(consequent),
    )));
}

#[test]
fn builtin_obligation_solver_discharges_concrete_invariant() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 4);
    let invariant = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let state = CState::new().with_local("x", int32(0)).with_memory(memory);
    let statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        vec![invariant],
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete invariant should be solved");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Normal(state),
        }
    );
}

#[test]
fn countdown_loop_body_preserves_nonnegative_invariant_symbolically() {
    let x = Variable(66);
    let x_bits = Bitvector32Term::Variable(x);
    let state = CState::new().with_local("x", int32(x_bits.clone()));
    let statement = c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1)));
    let invariant =
        ConditionTerm::signed_greater_equal(x_bits.clone(), Bitvector32Term::Constant(0));
    let condition =
        ConditionTerm::signed_greater_than(x_bits.clone(), Bitvector32Term::Constant(0));
    let post_invariant = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Subtract(
                Box::new(x_bits.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(invariant.clone(), true)
        .assume_condition(condition.clone(), true);
    let theorem = prove_c_statement_executes_and_propositions(
        state.clone(),
        statement.clone(),
        assumptions,
        vec![post_invariant.clone()],
    )
    .expect("x > 0 should prove x - 1 executes and remains nonnegative");

    assert_eq!(
        theorem.proposition().peel_implications(),
        &proposition_and(
            Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(CState::new().with_local(
                    "x",
                    int32(Bitvector32Term::Subtract(
                        Box::new(x_bits),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                ),),
            },
            post_invariant,
        )
    );
}

#[test]
fn symbolic_max_lt_branch_is_native_theorem() {
    let a = Variable(10);
    let b = Variable(11);
    let theorem = prove_c_max_lt_returns_right(a, b).expect("lt branch should prove");
    let condition = ConditionTerm::Bitvector32SignedLessThan(
        Box::new(Bitvector32Term::Variable(a)),
        Box::new(Bitvector32Term::Variable(b)),
    );
    let state = c_max_state(
        int32(Bitvector32Term::Variable(a)),
        int32(Bitvector32Term::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(condition, true)),
                    Box::new(Proposition::CStatementExecutes {
                        state: state.clone(),
                        statement: c_max_body(),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(b)),
                            state,
                        },
                    }),
                ),
            ),
        )
    );
}

#[test]
fn symbolic_max_not_lt_branch_is_native_theorem() {
    let a = Variable(12);
    let b = Variable(13);
    let theorem = prove_c_max_not_lt_returns_left(a, b).expect("false branch should prove");
    let condition = ConditionTerm::Bitvector32SignedLessThan(
        Box::new(Bitvector32Term::Variable(a)),
        Box::new(Bitvector32Term::Variable(b)),
    );
    let state = c_max_state(
        int32(Bitvector32Term::Variable(a)),
        int32(Bitvector32Term::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(condition, false)),
                    Box::new(Proposition::CStatementExecutes {
                        state: state.clone(),
                        statement: c_max_body(),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(a)),
                            state,
                        },
                    }),
                ),
            ),
        )
    );
}

#[test]
fn signed_add_overflow_is_native_undefined_behavior() {
    let state = CState::new();
    let theorem = prove_c_expression_evaluation(
        state.clone(),
        c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
    )
    .expect("concrete add should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn condition_evaluation_certifies_c_truthiness_directly() {
    let state = CState::new();
    let condition = c_less_than(c_int32_literal(1), c_int32_literal(2));
    let evaluation =
        prove_symbolic_c_condition_evaluation(state.clone(), condition.clone(), Assumptions::new());

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state,
            condition,
            outcome: CConditionOutcome::Value(true),
        }
    );
}

#[test]
fn symbolic_condition_evaluation_exposes_both_truthiness_paths() {
    let x = Variable(90);
    let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(x)));
    let condition = c_greater_equal(c_variable("x"), c_int32_literal(0));
    let evaluation = prove_symbolic_c_condition_evaluation(state, condition, Assumptions::new());

    let outcomes = evaluation
        .paths()
        .iter()
        .map(
            |path| match path.theorem().proposition().peel_implications() {
                Proposition::CConditionEvaluates { outcome, .. } => outcome.clone(),
                proposition => panic!("unexpected condition theorem {proposition:?}"),
            },
        )
        .collect::<BTreeSet<_>>();
    assert_eq!(
        outcomes,
        BTreeSet::from([
            CConditionOutcome::Value(false),
            CConditionOutcome::Value(true),
        ])
    );
}

#[test]
fn int32_subtraction_is_native() {
    let state = CState::new();
    let statement = c_return(c_subtract(c_int32_literal(7), c_int32_literal(2)));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete subtraction should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state,
            },
        }
    );
}

#[test]
fn nonnegative_ordered_subtraction_does_not_overflow() {
    let position = Bitvector32Term::Variable(Variable(24));
    let length = Bitvector32Term::Variable(Variable(25));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(position.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(length.clone(), position.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(length, position)),
        Some(false)
    );
}

#[test]
fn signed_subtract_overflow_is_native_undefined_behavior() {
    let state = CState::new();
    let theorem = prove_c_expression_evaluation(
        state.clone(),
        c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
    )
    .expect("concrete subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn int32_comparisons_return_c_int32_zero_or_one() {
    let state = CState::new();
    let examples = [
        (
            c_less_equal(c_int32_literal(2), c_int32_literal(2)),
            int32(1),
        ),
        (
            c_greater_than(c_int32_literal(3), c_int32_literal(2)),
            int32(1),
        ),
        (
            c_greater_equal(c_int32_literal(2), c_int32_literal(3)),
            int32(0),
        ),
        (c_equal(c_int32_literal(4), c_int32_literal(4)), int32(1)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("comparison should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn pointer_equality_returns_c_int32_zero_or_one() {
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let other = Pointer {
        block: "other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(p))
        .with_local("same", CValue::Pointer(same))
        .with_local("next", CValue::Pointer(next))
        .with_local("other", CValue::Pointer(other));
    let examples = [
        (c_equal(c_variable("p"), c_variable("same")), int32(1)),
        (c_equal(c_variable("p"), c_variable("next")), int32(0)),
        (c_equal(c_variable("p"), c_variable("other")), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("pointer equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn spec_pointer_equality_lowers_to_a_pure_fact() {
    let left = Pointer::symbolic(Variable(22_100));
    let right = Pointer::symbolic(Variable(22_101));
    let equality = ConditionTerm::pointer_equal(left.clone(), right.clone());

    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left.clone()),
            CComparisonOperator::Equal,
            &CValue::Pointer(right.clone()),
        ),
        Some(Proposition::ConditionIs(equality.clone(), true)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left.clone()),
            CComparisonOperator::NotEqual,
            &CValue::Pointer(right),
        ),
        Some(Proposition::ConditionIs(equality, false)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left),
            CComparisonOperator::LessThan,
            &CValue::Int32(Bitvector32Term::Constant(0)),
        ),
        None,
    );
}

#[test]
fn symbolic_pointer_truthiness_keeps_null_and_nonnull_paths() {
    let paths = c_truthiness_paths(
        CValue::Pointer(Pointer::symbolic(Variable(22_000))),
        Vec::new(),
        Vec::new(),
        &Assumptions::new(),
    );

    assert_eq!(paths.len(), 2);
    assert!(paths.iter().any(|path| path.is_true));
    assert!(paths.iter().any(|path| !path.is_true));
}

#[test]
fn pointer_equality_accepts_int32_zero_as_null_pointer_constant() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("nullp", CValue::Pointer(null))
        .with_local("p", CValue::Pointer(nonnull));
    let examples = [
        (c_equal(c_variable("nullp"), c_int32_literal(0)), int32(1)),
        (c_equal(c_int32_literal(0), c_variable("nullp")), int32(1)),
        (c_equal(c_variable("p"), c_int32_literal(0)), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("null equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    let invalid = c_equal(c_variable("p"), c_int32_literal(1));
    let theorem = prove_c_expression_evaluation(state.clone(), invalid.clone())
        .expect("invalid pointer equality should evaluate");
    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: invalid,
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        }
    );
}

#[test]
fn not_equal_and_not_return_c_int32_zero_or_one() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("nullp", CValue::Pointer(null))
        .with_local("p", CValue::Pointer(p))
        .with_local("same", CValue::Pointer(same))
        .with_local("next", CValue::Pointer(next));
    let examples = [
        (
            c_not_equal(c_int32_literal(4), c_int32_literal(5)),
            int32(1),
        ),
        (c_not_equal(c_variable("p"), c_variable("same")), int32(0)),
        (c_not_equal(c_variable("p"), c_variable("next")), int32(1)),
        (
            c_not_equal(c_variable("nullp"), c_int32_literal(0)),
            int32(0),
        ),
        (c_not(c_int32_literal(0)), int32(1)),
        (c_not(c_int32_literal(7)), int32(0)),
        (c_not(c_variable("nullp")), int32(1)),
        (c_not(c_variable("p")), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("logical expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn logical_and_or_short_circuit_right_operand() {
    let invalid_pointer = Pointer {
        block: "missing".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invalid_load = c_load(c_pointer_value(invalid_pointer));
    let state = CState::new().with_resource_context(read_context(
        Pointer {
            block: "missing".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let examples = [
        (c_and(c_int32_literal(0), invalid_load.clone()), int32(0)),
        (c_or(c_int32_literal(1), invalid_load.clone()), int32(1)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("short-circuit expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    assert!(
        prove_c_expression_evaluation(
            state.clone(),
            c_and(c_int32_literal(1), invalid_load.clone()),
        )
        .is_none()
    );
    assert!(prove_c_expression_evaluation(state, c_or(c_int32_literal(0), invalid_load)).is_none());
}

#[test]
fn symbolic_pointer_equality_reports_branch_facts() {
    let offset = Variable(80);
    let left = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Variable(offset),
    };
    let condition = ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone());
    let state = CState::new()
        .with_local("p", CValue::Pointer(left))
        .with_local("q", CValue::Pointer(right));
    let statement = c_if(
        c_equal(c_variable("p"), c_variable("q")),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement: statement.clone(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state: state.clone(),
            },
        }
    );
    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition, false)]
    );
    assert_eq!(
        execution.paths()[1]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state,
            },
        }
    );
}

#[test]
fn if_uses_c_int32_truthiness() {
    let state = CState::new();
    let statement = c_if(
        c_int32_literal(7),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("nonzero int32 condition should take then branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );

    let state = CState::new();
    let statement = c_if(
        c_int32_literal(0),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("zero int32 condition should take else branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state,
            },
        }
    );
}

#[test]
fn assignment_and_sequence_update_native_state() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_seq(c_assign("x", c_int32_literal(2)), c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(2));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn store_then_load_threads_native_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources.clone());
    let statement = c_seq(
        c_store(c_pointer_value(pointer.clone()), c_int32_literal(9)),
        c_return(c_load(c_pointer_value(pointer.clone()))),
    );
    let final_state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("store then load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn read_element_permits_symbolic_external_load_from_incomplete_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(pointer.clone()))
        .with_resource_context(read_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(Bitvector32Term::MemoryLoad(
                    Box::new(CMemory::new()),
                    Box::new(pointer),
                )),
                state,
            },
        }
    );
}

#[test]
fn block_backed_store_then_load_needs_no_memory_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 16);
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let statement = c_seq(
        c_store(c_pointer_value(pointer.clone()), c_int32_literal(9)),
        c_return(c_load(c_pointer_value(pointer.clone()))),
    );
    let final_state = CState::new()
        .with_memory(memory.store(pointer, int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("in-range block store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn block_backed_missing_load_returns_symbolic_value_without_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new().with_block("block", 16);
    let state = CState::new()
        .with_local("p", CValue::Pointer(pointer.clone()))
        .with_memory(memory.clone())
        .with_resource_context(read_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("in-range missing load should produce symbolic value");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(Bitvector32Term::MemoryLoad(
                    Box::new(memory),
                    Box::new(pointer)
                )),
                state,
            },
        }
    );
}

#[test]
fn pointer_addition_scales_int32_offsets_for_loads() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), int32(23));
    let resources = read_context(base.clone(), 1, 2);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("pointer arithmetic load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(23),
                state: CState::new()
                    .with_local(
                        "p",
                        CValue::Pointer(Pointer {
                            block: "block".into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                    )
                    .with_memory(
                        CMemory::new()
                            .with_block("block", 16)
                            .store(second, int32(23),),
                    )
                    .with_resource_context(resources),
            },
        }
    );
}

#[test]
fn read_element_permits_pointer_addition_load_beyond_memory_block() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let derived = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new().with_block("block", 4);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_memory(memory.clone())
        .with_resource_context(read_context(base, 1, 2));
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(Bitvector32Term::MemoryLoad(
                    Box::new(memory),
                    Box::new(derived),
                )),
                state,
            },
        }
    );
}

#[test]
fn fixed_bound_store_loop_touches_only_valid_pointer_range() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 12);
    let resources = write_context(base.clone(), 0, 3);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_local("i", int32(0))
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let loop_statement = c_while(
        c_less_than(c_variable("i"), c_int32_literal(3)),
        Vec::new(),
        c_seq(
            c_store(c_add(c_variable("p"), c_variable("i")), c_variable("i")),
            c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
        ),
    );
    let statement = c_seq(loop_statement, c_return(c_variable("i")));
    let final_memory = memory
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            int32(0),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(4),
            },
            int32(1),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(8),
            },
            int32(2),
        );
    let final_state = CState::new()
        .with_local(
            "p",
            CValue::Pointer(Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
        .with_local("i", int32(3))
        .with_memory(final_memory)
        .with_resource_context(resources);
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(3),
                state: final_state,
            },
        }
    );
}

#[test]
fn symbolic_loadable_discharges_pointer_access_obligation() {
    let i = Variable(67);
    let n = Variable(68);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let memory = CMemory::new();
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_local("i", int32(i_bits.clone()))
        .with_memory(memory.clone())
        .with_resource_context(write_context(base.clone(), 0, n_bits.clone()));
    let statement = c_store(c_add(c_variable("p"), c_variable("i")), c_int32_literal(7));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::Multiply(
                Box::new(n_bits.clone()),
                Box::new(Bitvector32Term::Constant(4)),
            ),
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits),
            true,
        );
    let execution = prove_symbolic_c_execution_paths(state, statement, assumptions);

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
}

#[test]
fn interval_arithmetic_proves_increment_bounds_and_no_overflow() {
    let i = Variable(69);
    let n = Variable(70);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new().with_local("i", int32(i_bits.clone()));
    let statement = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits.clone()),
            true,
        );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(i_bits.clone(), incremented.clone()),
        true,
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(i_bits.clone(), incremented.clone()),
        true,
    )));
    let theorem = prove_c_statement_executes_and_propositions(
        state,
        statement,
        assumptions,
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    incremented.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_less_equal(incremented, n_bits), true),
        ],
    )
    .expect("interval facts should prove i + 1 bounds and no signed overflow");

    assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
}

#[test]
fn signed_order_solver_knows_int32_universal_bounds() {
    let x = Bitvector32Term::Variable(Variable(71));
    let int_min = Bitvector32Term::Constant(i32::MIN as u32);
    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
    let assumptions = Assumptions::new();

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            x.clone(),
            int_max.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_than(x.clone(), int_max)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            x.clone(),
            int_min.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(x, int_min)),
        Some(false)
    );
}

#[test]
fn interval_arithmetic_uses_lower_bound_for_incremented_values() {
    let i = Variable(73);
    let i_bits = Bitvector32Term::Variable(i);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    // A lower bound alone is not enough: `i + 1` wraps at INT_MAX, so
    // `i >= 1` does not entail `i + 1 >= 1` (false at i = INT_MAX).
    let lower_only = Assumptions::new().assume_condition(
        ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    assert!(!lower_only.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
        true,
    )));

    // Knowing `i < INT_MAX` rules out signed overflow of `i + 1`, so the
    // lower bound carries to the incremented value.
    let assumptions = lower_only.assume_condition(
        ConditionTerm::signed_less_than(i_bits, Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
        true,
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(incremented, Bitvector32Term::Constant(0)),
        true,
    )));
}

#[test]
fn additive_upper_bound_covers_incremented_pointer_access() {
    let j = Variable(74);
    let j_bits = Bitvector32Term::Variable(j);
    let incremented = Bitvector32Term::add(j_bits.clone(), Bitvector32Term::Constant(1));
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_int32_elements(incremented.clone());
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(2)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            incremented,
            Bitvector32Term::Constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.pointer_access_in_range(
        &pointer,
        4,
        &base,
        &Bitvector32Term::Constant(0),
        &Bitvector32Term::Constant(3),
    ));
}

#[test]
fn relative_dependent_range_is_covered_by_owned_range() {
    let owner = Bitvector32Term::Variable(Variable(75));
    let backing = Bitvector32Term::Variable(Variable(76));
    let index = Bitvector32Term::Variable(Variable(77));
    let length = Bitvector32Term::Variable(Variable(78));
    let capacity = Bitvector32Term::Variable(Variable(79));
    let base = Pointer {
        block: "owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let backing_start = Bitvector32Term::subtract(backing.clone(), owner.clone());
    let indexed_start =
        Bitvector32Term::subtract(Bitvector32Term::add(backing, index.clone()), owner);
    let available = CResourceFact::own_memory(CMemoryRange::new(
        base.clone(),
        backing_start.clone(),
        Bitvector32Term::add(backing_start, capacity.clone()),
    ));
    let required = CResourceFact::own_memory(CMemoryRange::new(
        base,
        indexed_start.clone(),
        Bitvector32Term::add(indexed_start, Bitvector32Term::Constant(1)),
    ));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(length, capacity), true);
    let resources = ResourceContext::new().unchecked_with_fact(available);

    assert!(resources.satisfies_fact(&required, &assumptions));
    assert!(resources.without_fact(&required, &assumptions).is_some());
}

#[test]
fn negative_equality_fact_decides_equality_false() {
    let x = Bitvector32Term::Variable(Variable(79));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
        false,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(Bitvector32Term::Constant(0), x,)),
        Some(false)
    );
}

#[test]
fn equality_facts_are_transitive() {
    let i = Bitvector32Term::Variable(Variable(84));
    let k = Bitvector32Term::Variable(Variable(85));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(k.clone(), i.clone()), true)
        .assume_condition(ConditionTerm::equal(i, Bitvector32Term::Constant(1)), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(1))),
        Some(true)
    );
}

#[test]
fn equality_transports_signed_order_facts_in_both_directions() {
    let selected = Bitvector32Term::Variable(Variable(86));
    let key = Bitvector32Term::Variable(Variable(87));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(selected.clone(), key.clone()), true)
        .assume_condition(
            ConditionTerm::signed_greater_equal(key.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(10), selected.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            selected,
            Bitvector32Term::Constant(0),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(10),
            key,
        )),
        Some(true)
    );
}

#[test]
fn simp_combines_equality_with_discrete_integer_bounds() {
    let length = Bitvector32Term::Variable(Variable(87_100));
    let owner_length = Bitvector32Term::Variable(Variable(87_101));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::equal(owner_length.clone(), length), true);

    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            owner_length,
        )),
        Some(true)
    );
}

#[test]
fn simp_evaluates_equality_arithmetic_chains() {
    let old_split = Bitvector32Term::Variable(Variable(87_102));
    let split = Bitvector32Term::Variable(Variable(87_103));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(old_split.clone(), Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(
                split.clone(),
                Bitvector32Term::add(old_split, Bitvector32Term::Constant(1)),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            split,
        )),
        Some(true)
    );
}

#[test]
fn equality_transport_reaches_chains_and_arithmetic_terms() {
    let x = Bitvector32Term::Variable(Variable(88));
    let y = Bitvector32Term::Variable(Variable(89));
    let z = Bitvector32Term::Variable(Variable(90));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(x.clone(), y), true)
        .assume_condition(ConditionTerm::equal(z.clone(), x), true)
        .assume_condition(
            ConditionTerm::signed_less_than(
                Bitvector32Term::add(z, Bitvector32Term::Constant(1)),
                Bitvector32Term::Constant(8),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(89)),
                Bitvector32Term::Constant(1),
            ),
            Bitvector32Term::Constant(8),
        )),
        Some(true)
    );
}

#[test]
fn excluded_small_integer_range_is_inconsistent() {
    let k = Bitvector32Term::Variable(Variable(80));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(3)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(0)),
            false,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(1)),
            false,
        )
        .assume_condition(ConditionTerm::equal(k, Bitvector32Term::Constant(2)), false);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn singleton_integer_range_forces_equality() {
    let k = Bitvector32Term::Variable(Variable(86));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(1)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(0))),
        Some(true)
    );
}

#[test]
fn safe_positive_subtraction_is_below_its_base() {
    let x = Bitvector32Term::Variable(Variable(87));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::subtract(x.clone(), Bitvector32Term::Constant(1)),
            x,
        )),
        Some(true)
    );
}

#[test]
fn mutable_frame_proves_unwritten_load_equal_across_stack_locals() {
    let i = Variable(74);
    let i_bits = Bitvector32Term::Variable(i);
    let old_memory = CMemory::new();
    let loop_entry_memory = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(1));
    let loop_exit_memory = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(i_bits.clone()));
    let first_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: loop_entry_memory,
            after: loop_exit_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(loop_exit_memory), Box::new(first_cell.clone()),),
            Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(first_cell)),
        ),
        true,
    )));
}

#[test]
fn mutable_frame_transports_load_across_certified_effect_chain() {
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first_write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let second_write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let before = CMemory::new();
    let middle = before.clone().store(first_write.clone(), int32(1));
    let after = middle.clone().store(second_write.clone(), int32(2));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: middle.clone(),
            pointers: vec![first_write],
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: middle,
            after: after.clone(),
            pointers: vec![second_write],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after), Box::new(preserved.clone())),
            Bitvector32Term::MemoryLoad(Box::new(before), Box::new(preserved)),
        ),
        true,
    )));
}

#[test]
fn unrelated_external_cell_store_preserves_memory_load_with_stack_temporary() {
    let old_memory = CMemory::new();
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let stack_memory = CMemory::new()
        .with_block("local:tmp", 4)
        .store(CMemory::local_pointer("tmp"), int32(0));
    let current_memory = stack_memory.clone().store(
        p0.clone(),
        int32(Bitvector32Term::MemoryLoad(
            Box::new(stack_memory),
            Box::new(p0),
        )),
    );

    assert!(Assumptions::new().proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(current_memory), Box::new(p1.clone())),
            Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(p1)),
        ),
        true,
    )));
}

#[test]
fn exact_changed_cell_frame_precedes_abstract_effect_search() {
    let queried = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_000)), 4),
    };
    let materialized = Pointer {
        block: queried.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_001)), 4),
    };
    let before = CMemory::new().with_block("call-havoc:0", 0);
    let after = before.clone().store(materialized.clone(), int32(7));
    let assumptions = Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(queried.clone(), 0, 1)),
        right: CResource::Memory(memory_range(materialized, 0, 1)),
    });

    assert!(c_memory_load_is_unchanged(
        &before,
        &after,
        &queried,
        &assumptions,
    ));
}

#[test]
fn exact_separation_resolves_contained_symbolic_ranges_without_general_search() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_000)), 4),
    };
    let data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_001)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(41_002));
    let owner_range = memory_range(owner.clone(), 0, 4);
    let data_range = memory_range(data.clone(), 0, length.clone());
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range.clone()),
            right: CResource::Memory(data_range.clone()),
        })
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        ));
    let owner_field = memory_range(owner.offset_by_int32_elements(2.into()), 0, 1);
    let data_cell = memory_range(data.clone(), 0, 1);

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &owner_field,
            &data_cell,
        )
    );

    let memory = CMemory::new().with_block("call-havoc:0", 0);
    let data_field = owner.offset_by_int32_elements(2.into());
    let loaded_data_offset = PointerOffsetTerm::scale_int32(
        Bitvector32Term::MemoryLoad(Box::new(memory), Box::new(data_field)),
        4,
    );
    let loaded_data = Pointer {
        block: data.block.clone(),
        offset: loaded_data_offset.clone(),
    };
    let assumptions = assumptions
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(loaded_data_offset, data.offset.clone()),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), length),
            true,
        ));
    let owner_len_field = memory_range(owner.offset_by_int32_elements(1.into()), 0, 1);
    let second_data_cell = memory_range(loaded_data, 1, 2);
    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &owner_len_field,
            &second_data_cell,
        )
    );
}

#[test]
fn direct_resource_match_uses_exact_field_load_equalities() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("call-havoc:0", 0);
    let loaded_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                Box::new(memory.clone()),
                Box::new(owner.offset_by_int32_elements(2.into())),
            ),
            4,
        ),
    };
    let loaded_length = Bitvector32Term::MemoryLoad(
        Box::new(memory),
        Box::new(owner.offset_by_int32_elements(1.into())),
    );
    let named_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_100)), 4),
    };
    let named_length = Bitvector32Term::Variable(Variable(41_101));
    let loaded = CResource::Memory(memory_range(loaded_data.clone(), 0, loaded_length.clone()));
    let named = CResource::Memory(memory_range(named_data.clone(), 0, named_length.clone()));

    assert!(!c_resources_directly_match(
        &loaded,
        &named,
        &Assumptions::new()
    ));

    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(loaded_data.offset, named_data.offset),
            true,
        )
        .assume_condition(ConditionTerm::equal(loaded_length, named_length), true);
    assert!(c_resources_directly_match(&loaded, &named, &assumptions));
}

#[test]
fn equivalent_memory_load_order_facts_can_be_inconsistent() {
    let old_memory = CMemory::new();
    let stack_memory = CMemory::new()
        .with_block("local:tmp", 4)
        .store(CMemory::local_pointer("tmp"), int32(0));
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let old_p0 = Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(p0.clone()));
    let stack_p0 = Bitvector32Term::MemoryLoad(Box::new(stack_memory), Box::new(p0));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(old_p0.clone(), stack_p0.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(stack_p0, old_p0), true);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn equivalent_condition_facts_with_different_truth_values_are_inconsistent() {
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory_a = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(0));
    let memory_b = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(1));
    let left_a = Bitvector32Term::MemoryLoad(Box::new(memory_a.clone()), Box::new(p0.clone()));
    let right_a = Bitvector32Term::MemoryLoad(Box::new(memory_a), Box::new(p1.clone()));
    let left_b = Bitvector32Term::MemoryLoad(Box::new(memory_b.clone()), Box::new(p0));
    let right_b = Bitvector32Term::MemoryLoad(Box::new(memory_b), Box::new(p1));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_than(left_a, right_a), true)
        .assume_condition(ConditionTerm::signed_less_than(left_b, right_b), false);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn disjoint_range_proves_mutable_frame_cell_distinct() {
    let i = Variable(81);
    let j = Variable(82);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let before_memory = CMemory::new();
    let after_memory = CMemory::new();
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let read_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(j_bits.clone()),
            byte_width: 4,
        },
    };
    let i_plus_one = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let j_plus_one = Bitvector32Term::Add(
        Box::new(j_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), i_plus_one.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits.clone(), j_plus_one.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: base.clone(),
            left_start: i_bits.clone(),
            left_end: i_plus_one,
            right_base: base,
            right_start: j_bits.clone(),
            right_end: j_plus_one,
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after_memory), Box::new(read_cell.clone())),
            Bitvector32Term::MemoryLoad(Box::new(before_memory), Box::new(read_cell)),
        ),
        true,
    )));
}

#[test]
fn disjoint_ranges_frame_metadata_across_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(83)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(84)), 4),
    };
    let index = Bitvector32Term::Variable(Variable(85));
    let capacity = Bitvector32Term::Variable(Variable(86));
    let metadata_cell = owner.clone();
    let written_cell = data.offset_by_int32_elements(index.clone());
    let before_memory = CMemory::new();
    let after_memory = before_memory.clone().store(written_cell.clone(), int32(7));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: owner,
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(4),
            right_base: data,
            right_start: Bitvector32Term::Constant(0),
            right_end: capacity,
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after_memory), Box::new(metadata_cell.clone()),),
            Bitvector32Term::MemoryLoad(Box::new(before_memory), Box::new(metadata_cell)),
        ),
        true,
    )));
}

#[test]
fn equivalent_field_derived_bases_frame_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(87)), 4),
    };
    let owner_data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let base_memory = CMemory::new();
    let execution_memory = base_memory
        .clone()
        .with_block("local:data", 8)
        .store(CMemory::local_pointer("data"), int32(0));
    let resource_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                Box::new(base_memory.clone()),
                Box::new(owner_data_cell.clone()),
            ),
            4,
        ),
    };
    let execution_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                Box::new(execution_memory.clone()),
                Box::new(owner_data_cell),
            ),
            4,
        ),
    };
    let index = Bitvector32Term::Variable(Variable(88));
    let capacity = Bitvector32Term::Variable(Variable(89));
    let metadata_cell = owner.clone();
    let written_cell = execution_data.offset_by_int32_elements(index.clone());
    let after_memory = execution_memory
        .clone()
        .store(written_cell.clone(), int32(7));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                resource_data,
                Bitvector32Term::Constant(0),
                capacity,
            )),
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: execution_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after_memory), Box::new(metadata_cell.clone()),),
            Bitvector32Term::MemoryLoad(Box::new(execution_memory), Box::new(metadata_cell)),
        ),
        true,
    )));
}

#[test]
fn direct_transport_composes_framed_loads_inside_an_indexed_address() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95)), 4),
    };
    let owner_len_cell = owner.clone();
    let owner_data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let data_value =
        Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(owner_data_cell));
    let length = Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(owner_len_cell));
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_value, 4),
    };
    let index = Bitvector32Term::Variable(Variable(96));
    let capacity = Bitvector32Term::Variable(Variable(97));
    let written_cell = data.offset_by_int32_elements(index.clone());
    let terminator_cell = data.offset_by_int32_elements(length.clone());
    let after = before.clone().store(written_cell.clone(), int32(7));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(terminator_cell)),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_than(index, length), true)
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                data,
                Bitvector32Term::Constant(0),
                capacity,
            )),
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before,
            after: after.clone(),
            pointers: vec![written_cell],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("the address loads and then the indexed cell should transport");
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    assert_ne!(target.as_ref(), &fact);
    assert_eq!(c_condition_fact_memories(target), vec![after]);
}

#[test]
fn explicit_separation_contains_one_element_under_a_positive_length() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(98)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(99)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(100));
    let owner_range = CMemoryRange::new(
        owner,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(6),
    );
    let data_range = CMemoryRange::new(data, Bitvector32Term::Constant(0), length.clone());
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), length),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range.clone()),
            right: CResource::Memory(data_range.clone()),
        });

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &CMemoryRange::new(
                data_range.base().clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ),
            &CMemoryRange::new(
                owner_range.base().clone(),
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(2),
            ),
        )
    );
}

#[test]
fn direct_separation_contains_zero_under_a_constant_lower_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(104)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(105)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(106));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                data.clone(),
                Bitvector32Term::Constant(0),
                length,
            )),
        });

    assert!(assumptions.ranges_directly_disjoint_from_pointer(
        &[CMemoryRange::new(
            owner,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
        &data,
    ));
}

#[test]
fn constant_field_offset_is_disjoint_from_earlier_constant_range() {
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(101)), 4),
    };
    let first_field = CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let third_field = base.offset_by_int32_elements(Bitvector32Term::Constant(2));

    assert!(Assumptions::new().ranges_proven_disjoint_from_pointer(&[first_field], &third_field));
}

#[test]
fn bounded_separation_uses_order_fact_across_equivalent_snapshots() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(102)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(103)), 4),
    };
    let len_cell = owner.clone();
    let cap_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let plain = CMemory::new();
    let cached = CMemory::new().store(
        Pointer {
            block: "local:cache".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(0),
    );
    let query_len =
        Bitvector32Term::MemoryLoad(Box::new(plain.clone()), Box::new(len_cell.clone()));
    let query_cap = Bitvector32Term::MemoryLoad(Box::new(plain), Box::new(cap_cell.clone()));
    let fact_len = Bitvector32Term::MemoryLoad(Box::new(cached.clone()), Box::new(len_cell));
    let fact_cap = Bitvector32Term::MemoryLoad(Box::new(cached), Box::new(cap_cell));
    let owner_range = CMemoryRange::new(
        owner.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    );
    let owned_data_range = CMemoryRange::new(data.clone(), Bitvector32Term::Constant(0), query_cap);
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_equal(fact_len, fact_cap), true)
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range),
            right: CResource::Memory(owned_data_range),
        });

    assert!(assumptions.ranges_proven_disjoint_from_pointer(
        &[CMemoryRange::new(
            data,
            Bitvector32Term::Constant(0),
            query_len,
        )],
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
    ));
}

#[test]
fn covering_disjoint_fact_handles_shifted_mutable_range() {
    let n = Variable(83);
    let k = Variable(84);
    let n_bits = Bitvector32Term::Variable(n);
    let k_bits = Bitvector32Term::Variable(k);
    let before_memory = CMemory::new();
    let after_memory = CMemory::new();
    let dst_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(85)), 4),
    };
    let src_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(86)), 4),
    };
    let src_cell = src_base.offset_by_int32_elements(k_bits.clone());
    let shifted_dst = dst_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k_bits, n_bits.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: dst_base,
            left_start: Bitvector32Term::Constant(0),
            left_end: n_bits.clone(),
            right_base: src_base,
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before: before_memory.clone(),
            after: after_memory.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                shifted_dst,
                Bitvector32Term::Constant(0),
                Bitvector32Term::subtract(n_bits, Bitvector32Term::Constant(1)),
            )],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after_memory), Box::new(src_cell.clone())),
            Bitvector32Term::MemoryLoad(Box::new(before_memory), Box::new(src_cell)),
        ),
        true,
    )));
}

#[test]
fn atomic_condition_fact_transport_uses_certified_effect_summary() {
    let before = CMemory::new()
        .with_block("stable", 4)
        .with_block("mutated", 4);
    let after = before.clone().with_block("call-havoc:0", 0);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mutated = Pointer {
        block: "mutated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(stable.clone())),
            Bitvector32Term::Constant(7),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            mutated,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the framed load should transport");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(Box::new(after), Box::new(stable)),
                    Bitvector32Term::Constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn memory_load_equality_does_not_ignore_loop_havoc_identity() {
    let before = CMemory::new();
    let after = before.clone().with_block("havoc:0", 0);
    let pointer = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(after), Box::new(pointer.clone())),
            Bitvector32Term::MemoryLoad(Box::new(before), Box::new(pointer)),
        ),
        true,
    );

    assert!(
        !Assumptions::new().proves(&equality),
        "a havoced snapshot requires explicit frame evidence"
    );
}

#[test]
fn atomic_condition_fact_transport_ignores_distinct_materialized_cell() {
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("call-havoc:0", 0);
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let materialized = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let after = before
        .clone()
        .store(materialized, CValue::Int32(Bitvector32Term::Constant(9)));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(preserved.clone())),
            Bitvector32Term::Constant(7),
        ),
        true,
    );

    let theorem = prove_c_condition_fact_transport(&fact, &after, &Assumptions::new())
        .expect("a distinct materialized cell must not change the framed load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(Box::new(after), Box::new(preserved)),
                    Bitvector32Term::Constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn atomic_condition_fact_transport_preserves_pointer_offset_equality() {
    let before = CMemory::new()
        .with_block("stable", 4)
        .with_block("mutated", 4);
    let after = before.clone().with_block("call-havoc:0", 0);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mutated = Pointer {
        block: "mutated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let expected = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(345)), 4);
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(stable.clone())),
                4,
            ),
            expected.clone(),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            mutated,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the framed pointer-valued field should transport");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(
                        Bitvector32Term::MemoryLoad(Box::new(after), Box::new(stable)),
                        4,
                    ),
                    expected,
                ),
                true,
            )),
        )
    );
}

#[test]
fn equality_fact_matching_transports_both_pointer_offset_endpoints() {
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let local = Pointer {
        block: "local:value".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("local:value", 4);
    let after = before
        .clone()
        .store(local, CValue::Int32(Bitvector32Term::Constant(7)));
    let load_offset = |memory: &CMemory, pointer: &Pointer| {
        PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(Box::new(memory.clone()), Box::new(pointer.clone())),
            4,
        )
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            load_offset(&before, &left),
            load_offset(&before, &right),
        ),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            load_offset(&after, &left),
            load_offset(&after, &right),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(fact);

    assert!(assumptions.proves(&target));
}

#[test]
fn memory_load_equality_combines_equal_pointer_base_and_zero_index() {
    let memory = CMemory::new().with_block("arg-memory", 64);
    let owner = Bitvector32Term::Variable(Variable(90));
    let data = Bitvector32Term::Variable(Variable(91));
    let owner_offset = PointerOffsetTerm::scale_int32(owner, 4);
    let data_field = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(owner_offset.clone(), PointerOffsetTerm::Constant(8)),
    };
    let pos_field = Pointer {
        block: "arg-memory".into(),
        offset: owner_offset,
    };
    let data_load = Bitvector32Term::MemoryLoad(Box::new(memory.clone()), Box::new(data_field));
    let pos_load = Bitvector32Term::MemoryLoad(Box::new(memory.clone()), Box::new(pos_field));
    let indexed = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_load.clone(), 4),
            PointerOffsetTerm::scale_int32(pos_load.clone(), 4),
        ),
    };
    let direct = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data.clone(), 4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::scale_int32(data_load, 4),
                PointerOffsetTerm::scale_int32(data, 4),
            ),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(pos_load, Bitvector32Term::Constant(0)),
            true,
        ));
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(memory.clone()), Box::new(indexed)),
            Bitvector32Term::MemoryLoad(Box::new(memory), Box::new(direct)),
        ),
        true,
    );

    assert!(assumptions.proves(&target));
}

#[test]
fn pointer_offset_equality_combines_equal_base_and_zero_index() {
    let base = Bitvector32Term::Variable(Variable(90));
    let target = Bitvector32Term::Variable(Variable(91));
    let index = Bitvector32Term::Variable(Variable(92));
    let base_offset = PointerOffsetTerm::scale_int32(base, 4);
    let target_offset = PointerOffsetTerm::scale_int32(target, 4);
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(base_offset.clone(), target_offset.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::add(base_offset, PointerOffsetTerm::scale_int32(index, 4),),
            target_offset,
        )),
        Some(true),
    );
}

#[test]
fn atomic_condition_fact_transport_uses_exact_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(left.clone())),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                left.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                right.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                right,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the exact separate range should frame the left load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(Box::new(after), Box::new(left)),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )),
        )
    );
}

#[test]
fn direct_condition_transport_uses_relative_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let data_index_from_owner = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Variable(Variable(92)),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(data.clone())),
            Bitvector32Term::Variable(Variable(94)),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner.clone(), Bitvector32Term::Constant(2)),
            ),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner, Bitvector32Term::Constant(2)),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("relative exact separation should directly frame the data load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(Box::new(after), Box::new(data)),
                    Bitvector32Term::Variable(Variable(94)),
                ),
                true,
            )),
        )
    );
}

#[test]
fn direct_condition_transport_uses_indexed_relative_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let data_one = data.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let data_index_from_owner = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Variable(Variable(92)),
    );
    let length = Bitvector32Term::Variable(Variable(95));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(data_one.clone())),
            Bitvector32Term::Variable(Variable(94)),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner, length),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("an indexed pointer in a relative separate range should be directly framed");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(Box::new(after), Box::new(data_one)),
                    Bitvector32Term::Variable(Variable(94)),
                ),
                true,
            )),
        )
    );
}

#[test]
fn condition_fact_transport_preserves_arithmetic_structure() {
    let before = CMemory::new().with_block("stable", 4);
    let after = before.clone().with_block("local:value", 4);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::add(
                Bitvector32Term::MemoryLoad(Box::new(before), Box::new(stable.clone())),
                Bitvector32Term::Constant(1),
            ),
            Bitvector32Term::Constant(8),
        ),
        true,
    );

    let theorem = prove_c_condition_fact_transport(&fact, &after, &Assumptions::new())
        .expect("arithmetic around a framed load should transport structurally");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::add(
                        Bitvector32Term::MemoryLoad(Box::new(after), Box::new(stable)),
                        Bitvector32Term::Constant(1),
                    ),
                    Bitvector32Term::Constant(8),
                ),
                true,
            )),
        )
    );
}

#[test]
fn adjacent_disjoint_fact_ranges_cover_larger_disjoint_goal() {
    let n_bits = Bitvector32Term::Variable(Variable(87));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p_plus_one = p_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(88)), 4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: p_base.clone(),
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(1),
            right_base: q_base.clone(),
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        })
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: p_plus_one,
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(2),
            right_base: q_base.clone(),
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        });

    assert!(assumptions.proves(&Proposition::CMemoryDisjoint {
        left_base: p_base,
        left_start: Bitvector32Term::Constant(0),
        left_end: Bitvector32Term::Constant(2),
        right_base: q_base,
        right_start: Bitvector32Term::Constant(0),
        right_end: n_bits,
    }));
}

#[test]
fn symbolic_disjoint_fact_proves_itself() {
    let n_bits = Bitvector32Term::Variable(Variable(89));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let fact = Proposition::CMemoryDisjoint {
        left_base: p_base,
        left_start: Bitvector32Term::Constant(0),
        left_end: n_bits.clone(),
        right_base: q_base,
        right_start: Bitvector32Term::Constant(0),
        right_end: n_bits,
    };
    let assumptions = Assumptions::new().assume_proposition(fact.clone());

    assert!(assumptions.proves(&fact));
}

#[test]
fn while_invariant_rule_proves_symbolic_loop_exit_fact() {
    let i = Variable(71);
    let n = Variable(72);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new()
        .with_local("i", int32(i_bits.clone()))
        .with_local("n", int32(n_bits.clone()));
    let condition = c_less_than(c_variable("i"), c_variable("n"));
    let body = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
    let invariant = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i_bits.clone(), n_bits.clone()),
            true,
        ),
    ];
    let assumptions = invariant
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                n_bits.clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            ),
            true,
        );
    let theorem = prove_c_while_invariant_rule(
        state,
        condition,
        invariant,
        body,
        assumptions,
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    incremented.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(incremented, n_bits.clone()),
                true,
            ),
        ],
        Proposition::ConditionIs(ConditionTerm::equal(i_bits, n_bits), true),
    )
    .expect("invariant rule should prove preservation and i == n on loop exit");

    assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
}

#[test]
fn same_block_frame_uses_symbolic_offset_inequality() {
    let i = Variable(73);
    let j = Variable(74);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let stored_pointer = base.offset_by_int32_elements(i_bits);
    let loaded_pointer = base.offset_by_int32_elements(j_bits);
    let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::pointer_offset_equal(
            stored_pointer.offset.clone(),
            loaded_pointer.offset.clone(),
        ),
        false,
    );
    let theorem = prove_memory_load_after_store_distinct_under_assumptions(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
        assumptions,
    )
    .expect("i != j should prove store p[i] preserves load p[j]");

    assert_eq!(
        theorem.proposition().peel_implications(),
        &Proposition::CMemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: CExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn same_symbolic_base_constant_offsets_are_distinct() {
    let base = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4);
    let first = Pointer {
        block: "arg-memory".into(),
        offset: base.clone(),
    };
    let second = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(base, PointerOffsetTerm::Constant(4)),
    };

    assert!(pointers_proven_distinct(
        &first,
        &second,
        &Assumptions::new()
    ));
}

#[test]
fn additive_equality_cancellation_feeds_range_contradictions() {
    let base = Bitvector32Term::Variable(Variable(91));
    let index = Bitvector32Term::Variable(Variable(92));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(Bitvector32Term::add(base.clone(), index.clone()), base),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(index, Bitvector32Term::Constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

#[test]
fn equality_facts_close_signed_order_contradiction_cycles() {
    let left = Bitvector32Term::Variable(Variable(193));
    let right = Bitvector32Term::Variable(Variable(194));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(left.clone(), right.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_than(left, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(right, Bitvector32Term::Constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

#[test]
fn equality_to_constant_feeds_signed_order_decisions() {
    let value = Bitvector32Term::Variable(Variable(93));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            value.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            value,
            Bitvector32Term::Constant(1),
        )),
        Some(true)
    );
}

#[test]
fn range_fold_simplifies_empty_and_one_step_ranges() {
    let accumulator = Variable(93);
    let item = Variable(94);
    let x = Bitvector32Term::Variable(Variable(95));
    let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), x.clone());

    assert_eq!(
        Bitvector32Term::range_fold(
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(7),
            accumulator,
            item,
            body.clone(),
        ),
        Bitvector32Term::Constant(7)
    );

    assert_eq!(
        Bitvector32Term::range_fold(
            Bitvector32Term::Variable(Variable(96)),
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(96)),
                Bitvector32Term::Constant(1)
            ),
            Bitvector32Term::Constant(7),
            accumulator,
            item,
            body,
        ),
        Bitvector32Term::add(Bitvector32Term::Constant(7), x)
    );
}

#[test]
fn count_shaped_range_fold_split_is_proven_equal() {
    let lo = Bitvector32Term::Variable(Variable(97));
    let mid = Bitvector32Term::Variable(Variable(98));
    let hi = Bitvector32Term::Variable(Variable(99));
    let x = Bitvector32Term::Variable(Variable(100));
    let accumulator = Variable(101);
    let item = Variable(102);
    let contribution = Bitvector32Term::if_then_else(
        ConditionTerm::equal(Bitvector32Term::Variable(item), x),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(0),
    );
    let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), contribution);
    let count = |start: Bitvector32Term, end: Bitvector32Term| {
        Bitvector32Term::range_fold(
            start,
            end,
            Bitvector32Term::Constant(0),
            accumulator,
            item,
            body.clone(),
        )
    };
    let whole = count(lo.clone(), hi.clone());
    let split = Bitvector32Term::add(
        count(lo.clone(), mid.clone()),
        count(mid.clone(), hi.clone()),
    );

    // The split identity fold(lo,hi) = fold(lo,mid) + fold(mid,hi) only
    // holds for lo <= mid <= hi. Without that ordering it is unsound
    // (half-open ranges make an out-of-order mid over- or under-count),
    // so the rule must not fire on unconstrained bounds.
    assert!(!Assumptions::new().proves(&Proposition::ConditionIs(
        ConditionTerm::equal(whole.clone(), split.clone()),
        true,
    )));

    let ordered = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_equal(lo, mid.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(mid, hi), true);
    assert!(ordered.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(whole, split),
        true,
    )));
}

#[test]
fn symbolic_store_invalidates_only_possible_aliasing_cells() {
    let i = Variable(81);
    let i_bits = Bitvector32Term::Variable(i);
    let concrete_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let symbolic_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let memory = CMemory::new()
        .with_block("array", 12)
        .store(concrete_cell.clone(), int32(42));

    let aliased = memory
        .without_possible_aliasing_cells(&symbolic_cell, &Assumptions::new())
        .store(symbolic_cell.clone(), int32(7));
    assert_eq!(aliased.known_value(&concrete_cell), None);

    let distinct_assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
        false,
    );
    let distinct = memory
        .without_possible_aliasing_cells(&symbolic_cell, &distinct_assumptions)
        .store(symbolic_cell, int32(7));
    assert_eq!(distinct.known_value(&concrete_cell), Some(int32(42)));
}

#[test]
fn memory_resolution_alias_check_uses_explicit_separation() {
    let left_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let right_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let assumptions = Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(left_base.clone(), 0, 4)),
        right: CResource::Memory(memory_range(right_base.clone(), 0, 4)),
    });

    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));

    let right_start = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(91)),
        Bitvector32Term::Variable(Variable(90)),
    );
    let normalized_assumptions =
        Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(left_base.clone(), 0, 4)),
            right: CResource::Memory(memory_range(
                left_base.clone(),
                right_start.clone(),
                Bitvector32Term::add(right_start, Bitvector32Term::Constant(4)),
            )),
        });
    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &normalized_assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_uses_exact_transitive_range_bounds() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let index = Bitvector32Term::Variable(Variable(94));
    let length = Bitvector32Term::Variable(Variable(95));
    let capacity = Bitvector32Term::Variable(Variable(96));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
            right: CResource::Memory(memory_range(data.clone(), 0, capacity.clone())),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &data.offset_by_int32_elements(index),
        &assumptions,
    ));

    let incremented = Bitvector32Term::add(
        Bitvector32Term::Variable(Variable(94)),
        Bitvector32Term::Constant(1),
    );
    let incremented_assumptions = assumptions
        .assume_condition(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::Variable(Variable(94)),
                Bitvector32Term::Constant(1),
            ),
            false,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(
                incremented.clone(),
                Bitvector32Term::Variable(Variable(96)),
            ),
            true,
        );
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &data.offset_by_int32_elements(incremented),
        &incremented_assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_transports_unchanged_field_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let len_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before =
        Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(data_cell.clone()));
    let data_after = Bitvector32Term::MemoryLoad(Box::new(after), Box::new(data_cell));
    let zero_index = Bitvector32Term::MemoryLoad(Box::new(before), Box::new(owner.clone()));
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_before, 4),
            PointerOffsetTerm::scale_int32(zero_index.clone(), 4),
        ),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_after, 4),
    };
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(zero_index, Bitvector32Term::Constant(0)),
        true,
    );

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &left,
        &right,
        &assumptions,
    ));
}

#[test]
fn memory_resolution_separation_transports_unchanged_range_base_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let len_cell = owner.clone();
    let data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before =
        Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(data_cell.clone()));
    let data_after = Bitvector32Term::MemoryLoad(Box::new(after), Box::new(data_cell));
    let index = Bitvector32Term::subtract(
        Bitvector32Term::MemoryLoad(Box::new(before), Box::new(owner.clone())),
        Bitvector32Term::Constant(1),
    );
    let data_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_before, 4),
    };
    let indexed_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_after.clone(), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
            right: CResource::Memory(memory_range(data_base.clone(), 0, 10)),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, Bitvector32Term::Constant(10)),
            true,
        );

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner,
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &data_base,
        &Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(data_after, 4),
        },
        &assumptions,
    ));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &indexed_data,
        &assumptions,
    ));
}

#[test]
fn incremented_materialized_index_transports_its_nonnegative_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(931)), 4),
    };
    let local_index = Pointer {
        block: "local:index".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new();
    let old_len = Bitvector32Term::MemoryLoad(Box::new(before.clone()), Box::new(owner.clone()));
    let materialized = before
        .with_block("local:index", 4)
        .store(local_index.clone(), int32(old_len.clone()));
    let materialized_index =
        Bitvector32Term::MemoryLoad(Box::new(materialized), Box::new(local_index));
    let incremented = Bitvector32Term::add(materialized_index, Bitvector32Term::Constant(1));
    let upper = Bitvector32Term::Variable(Variable(932));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), old_len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(old_len, upper), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            incremented.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            incremented,
        )),
        Some(true)
    );
}

#[test]
fn assumptions_resolve_materialized_symbolic_memory_load_aliases() {
    let k = Variable(75);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        Box::new(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });

    for (index, pointer) in src_pointers.into_iter().enumerate() {
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset.clone(),
                    pointer.offset.clone(),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(k),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(pointer)),
                Bitvector32Term::MemoryLoad(
                    Box::new(materialized_memory.clone()),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )));
    }
}

#[test]
fn assumptions_prove_wrapped_materialized_load_branch_obligation() {
    let k = Variable(76);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits.clone()),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        Box::new(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    Box::new(base_memory),
                    Box::new(src_pointers[1].clone()),
                ),
                Bitvector32Term::MemoryLoad(
                    Box::new(materialized_memory),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                symbolic_src.offset.clone(),
                src_pointers[0].offset.clone(),
            ),
            false,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(k_bits.clone(), Bitvector32Term::Constant(0)),
                false,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(
                        symbolic_src.offset,
                        src_pointers[1].offset.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::equal(k_bits, Bitvector32Term::Constant(1)),
                        true,
                    )),
                    Box::new(Proposition::ForAll {
                        var: k,
                        sort: Sort::CInt32,
                        body: Box::new(body),
                    }),
                )),
            )),
        )),
    );

    assert!(Assumptions::new().proves(&proposition));
}

#[test]
fn assumptions_prove_copied_prefix_new_cell_obligation() {
    let i = Variable(82);
    let k = Variable(83);
    let i_bits = Bitvector32Term::Variable(i);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits.clone()),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        Box::new(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    k_bits.clone(),
                    Bitvector32Term::Add(
                        Box::new(i_bits.clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                ),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    Box::new(base_memory),
                    Box::new(src_pointers[1].clone()),
                ),
                Bitvector32Term::MemoryLoad(
                    Box::new(materialized_memory),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(1)),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset,
                    PointerOffsetTerm::Int32Scaled {
                        value: Box::new(i_bits.clone()),
                        byte_width: 4,
                    },
                ),
                true,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(k_bits, i_bits),
                    true,
                )),
                Box::new(Proposition::ForAll {
                    var: k,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                }),
            )),
        )),
    );

    assert!(Assumptions::new().proves(&proposition));
}

#[test]
fn local_declaration_allocates_stack_object_for_address_of() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new();
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(5)),
            c_return(c_load(c_addr_of("x"))),
        ),
    );
    let final_state = CState::new().with_local("x", int32(5)).with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, int32(5)),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("local declaration/address-of should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn symbolic_execution_stops_without_needed_overflow_fact() {
    let left = Variable(20);
    let right = Variable(21);
    let state = CState::new()
        .with_local("left", int32(Bitvector32Term::Variable(left)))
        .with_local("right", int32(Bitvector32Term::Variable(right)));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));

    assert!(prove_symbolic_c_execution(state, statement, Assumptions::new()).is_none());
}

#[test]
fn symbolic_execution_reports_branch_facts() {
    let a = Variable(24);
    let b = Variable(25);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(int32(a_bits), int32(b_bits));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), c_max_body(), Assumptions::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Variable(b)),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition.clone(), false)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Variable(a)),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_execution_reports_overflow_facts() {
    let left = Variable(26);
    let right = Variable(27);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(overflow.clone(), false)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(overflow.clone(), false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(left_bits),
                        Box::new(right_bits)
                    )),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(overflow.clone(), true)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(overflow, true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            }),
        )
    );
}

#[test]
fn symbolic_execution_uses_no_overflow_fact() {
    let left = Variable(22);
    let right = Variable(23);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let no_overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let assumptions = Assumptions::new().assume_condition(no_overflow.clone(), false);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
        .expect("no-overflow fact should let symbolic add execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(no_overflow, false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(left_bits),
                        Box::new(right_bits)
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_increment_uses_int_max_bound_to_rule_out_overflow() {
    let x = Variable(65);
    let x_bits = Bitvector32Term::Variable(x);
    let state = CState::new().with_local("x", int32(x_bits.clone()));
    let statement = c_return(c_add(c_variable("x"), c_int32_literal(1)));
    let x_lt_int_max =
        ConditionTerm::signed_less_than(x_bits.clone(), Bitvector32Term::Constant(i32::MAX as u32));
    let assumptions = Assumptions::new().assume_condition(x_lt_int_max.clone(), true);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
        .expect("x < INT_MAX should prove x + 1 does not overflow");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(x_lt_int_max, true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(x_bits),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_increment_uses_any_strict_upper_bound_to_rule_out_overflow() {
    let x_bits = Bitvector32Term::Variable(Variable(651));
    let upper_bits = Bitvector32Term::Variable(Variable(652));
    let assumption = ConditionTerm::signed_less_than(x_bits.clone(), upper_bits);
    let assumptions = Assumptions::new().assume_condition(assumption, true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            x_bits,
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
}

#[test]
fn pointer_store_through_local_address_updates_named_lvalue() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_store(c_addr_of("x"), c_int32_literal(5)),
            c_return(c_variable("x")),
        ),
    );
    let final_state = CState::new().with_local("x", int32(5)).with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, int32(5)),
    );
    let theorem = prove_symbolic_c_execution(CState::new(), statement.clone(), Assumptions::new())
        .expect("pointer store through local address should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: CState::new(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn memory_load_store_are_native_theorems() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = int32(7);
    let theorem =
        prove_memory_load_after_store_same(CMemory::new(), pointer.clone(), value.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: CMemory::new().store(pointer.clone(), value.clone()),
            pointer,
            outcome: CExpressionOutcome::Value(value),
        }
    );
}

#[test]
fn store_preserves_distinct_memory_cell_frame() {
    let stored_pointer = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let loaded_pointer = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
    let theorem = prove_memory_load_after_store_other(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
    )
    .expect("store to distinct pointer should preserve loaded cell");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: CExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn missing_memory_load_is_native_undefined_behavior() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let theorem = prove_memory_load(CMemory::new(), pointer.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: CMemory::new(),
            pointer,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
        }
    );
}

#[test]
fn function_execution_theorem_retains_non_assumable_verification_conditions() {
    let verification_condition = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let theorem = Theorem::new(wrap_proof_facts(
        conclusion,
        &Assumptions::new(),
        &[],
        &[ProofObligation::verification_condition(
            verification_condition.clone(),
        )],
    ));

    assert!(matches!(
        theorem.proposition(),
        Proposition::Implies(condition, _)
            if condition.as_ref() == &verification_condition
    ));
}

#[test]
fn symbolic_path_can_only_certify_its_exact_function_specification() {
    let function = c_function(
        CType::Int32,
        "exact_path",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    let execution = prove_symbolic_c_function_execution_paths(
        CState::new(),
        function.clone(),
        Vec::new(),
        Assumptions::new(),
    );
    let false_specification = c_function_specification(
        CState::new(),
        Vec::new(),
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );

    assert!(
        prove_c_function_satisfies_specification_from_symbolic_path(
            function,
            false_specification,
            &execution.paths()[0],
        )
        .is_none()
    );
}

#[test]
fn verified_function_rule_applies_contract_without_executing_body() {
    let helper = c_function(
        CType::Int32,
        "opaque_helper",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(99)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::new(
            CFunctionContractClaimKey::Ensure(0),
        )],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("result", "opaque_helper", vec![c_int32_literal(5)]),
        c_return(c_variable("result")),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement.clone(),
        Assumptions::new(),
        environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution
        .paths()
        .first()
        .expect("opaque call should produce one path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Return { value, .. },
        ..
    } = proposition
    else {
        panic!("opaque call should return normally")
    };
    assert!(*value != int32(99));
    let propositions = path
        .facts()
        .iter()
        .map(|fact| fact.proposition().clone())
        .collect::<Vec<_>>();
    assert!(
        path.facts().iter().any(ExecutionPureFact::is_certified),
        "verified-call ensures should be marked as kernel-certified facts"
    );
    let assumptions = assumptions_with_propositions(&Assumptions::new(), &propositions);
    let CValue::Int32(result) = value else {
        panic!("opaque helper should return int32")
    };
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(result.clone()),
            Box::new(Bitvector32Term::Constant(5)),
        ),
        true,
    )));

    let body_execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        Assumptions::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
    );
    let mut proposition = body_execution.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Return { value, .. },
            ..
        } if *value == int32(99)
    ));
}

#[test]
fn verified_immutable_calls_allocate_distinct_results() {
    let helper = c_function(
        CType::Int32,
        "opaque_identity",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::new(
            CFunctionContractClaimKey::Ensure(0),
        )],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("first", "opaque_identity", vec![c_int32_literal(5)]),
        c_seq(
            c_call_assign("second", "opaque_identity", vec![c_int32_literal(7)]),
            c_return(c_variable("second")),
        ),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        Assumptions::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("calls should execute");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Return { value, .. },
        ..
    } = proposition
    else {
        panic!("calls should return normally")
    };

    assert_eq!(
        value,
        &CValue::Int32(Bitvector32Term::Variable(Variable(8_100_001)))
    );
}

#[test]
fn verified_function_rule_requires_every_contract_claim_certificate() {
    let function = c_function(
        CType::Int32,
        "two_claims",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![
            CFunctionContractClaim::new(CFunctionContractClaimKey::Ensure(0)),
            CFunctionContractClaim::new(CFunctionContractClaimKey::Ensure(1)),
        ],
        true,
    );
    let specification = c_function_specification(
        CState::new(),
        Vec::new(),
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(0),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification,
        Assumptions::new(),
    )
    .expect("function should satisfy its concrete specification");

    let impostor = c_function(
        CType::Int32,
        "two_claims",
        Vec::new(),
        c_return(c_int32_literal(1)),
    );
    let impostor_specification = c_function_specification(
        CState::new(),
        Vec::new(),
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );
    let impostor_theorem = prove_c_function_satisfies_specification(
        impostor,
        impostor_specification,
        Assumptions::new(),
    )
    .expect("impostor should satisfy its own specification");
    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Ensure(0),
            &impostor_theorem,
        )
        .is_none()
    );

    let first = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::Ensure(0),
        &theorem,
    )
    .expect("first claim should certify");

    assert!(c_verified_function_rule(function.clone(), std::slice::from_ref(&first)).is_none());

    let second = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::Ensure(1),
        &theorem,
    )
    .expect("second claim should certify");
    assert!(c_verified_function_rule(function, &[first, second]).is_some());
}
