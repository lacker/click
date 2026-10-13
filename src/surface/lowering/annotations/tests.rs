use super::*;
use crate::kernel::c_variable;

#[test]
fn struct_pointer_arithmetic_through_uint64_cast_uses_layout_width() {
    let function = crate::languages::c::syntax::parse_function(
        r#"
            struct pair {
                int32 a;
                int64 b;
            };
            int32 f(struct pair* p, int32 i) { return 0; }
        "#,
    )
    .expect("struct pointer function should parse");
    let state = CState::new();
    let snapshots = RecordedSnapshots::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        BTreeMap::new(),
        BTreeMap::new(),
        None,
        &snapshots,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        parameter_pointer_element_widths(function.parameters()),
    );
    let pointer_add = CExpression::Add(
        Box::new(CExpression::Variable("p".into())),
        Box::new(CExpression::Variable("i".into())),
    );
    let cast = CExpression::Cast {
        expression: Box::new(pointer_add),
        target_type: CType::UInt64,
        integer_mode: crate::kernel::CIntegerCastMode::Standard,
        pointee_struct: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    let lowered = lowerer
        .lower_c_fragment_to_spec(&cast, &context)
        .expect("pointer arithmetic should lower");
    let SpecExpression::Cast(pointer, CType::UInt64) = lowered else {
        panic!("expected a preserved uint64 cast around pointer arithmetic");
    };
    let SpecExpression::PointerOffset { byte_width, .. } = pointer.as_ref() else {
        panic!("expected pointer arithmetic to lower as a pointer offset");
    };
    assert_eq!(*byte_width, 16);
}

#[test]
fn integer_binder_contexts_share_unrelated_machine_bindings() {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let mut all_costs = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let context = SpecElaborationContext {
            values: (0..unrelated)
                .map(|index| {
                    (
                        format!("unrelated{index}"),
                        SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(
                            index,
                        )))),
                    )
                })
                .collect(),
            ..SpecElaborationContext::default()
        };
        let mut costs = Vec::new();
        for depth in [8, 16, 32, 64] {
            let before = crate::persistent::persistent_node_allocations();
            let mut scope = context.clone();
            assert_eq!(crate::persistent::persistent_node_allocations(), before);
            for index in 0..depth {
                let mut child = scope.clone();
                child.integer_values.insert(
                    format!("bound{index}"),
                    SpecIntegerExpression::Term(IntegerTerm::var(Variable(index + 2000))),
                );
                assert!(child.values.shares_root_with(&context.values));
                assert!(
                    child
                        .algebraic_values
                        .shares_root_with(&context.algebraic_values)
                );
                assert!(child.array_refs.shares_root_with(&context.array_refs));
                scope = child;
            }
            assert_eq!(context.integer_values.len(), 0);
            assert_eq!(scope.integer_values.len(), depth as usize);
            costs.push(crate::persistent::persistent_node_allocations() - before);
        }
        for pair in costs.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "{costs:?}");
        }
        all_costs.push(costs);
    }
    assert!(
        all_costs.windows(2).all(|pair| pair[0] == pair[1]),
        "{all_costs:?}"
    );
}

#[test]
fn integer_certificate_lowering_scales_with_nodes_not_unrelated_bindings() {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let surface = ClickProposition::Comparison {
        left: ContractExpression::Add(
            Box::new(ContractExpression::Binding("x".into())),
            Box::new(ContractExpression::IntegerLiteral("1".into())),
        ),
        operator: ComparisonOperator::GreaterThan,
        right: ContractExpression::Binding("x".into()),
    };
    let mut costs = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut bindings = crate::persistent::PersistentMap::default();
        bindings = bindings.with_inserted(
            "x".into(),
            SpecIntegerExpression::Term(IntegerTerm::var(Variable(7))),
        );
        for index in 0..unrelated {
            bindings = bindings.with_inserted(
                format!("unused{index}"),
                SpecIntegerExpression::Term(IntegerTerm::var(Variable(index + 100))),
            );
        }
        let mut node_costs = Vec::new();
        for nodes in [8, 16, 32, 64] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..nodes {
                    lower_integer_certificate_proposition(&surface, &bindings).unwrap();
                }
            });
            node_costs.push(work);
        }
        for pair in node_costs.windows(2) {
            assert_eq!(pair[1], 2 * pair[0]);
        }
        costs.push(node_costs[0]);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

thread_local! {
    pub(super) static PROPOSITION_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[test]
fn nested_snapshot_propositions_lower_with_small_frames_and_linear_visits() {
    std::thread::Builder::new()
        .name("small-stack-proposition-lowering".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = CState::new().with_local("x", int32(7));
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let mut snapshots = RecordedSnapshots::default();
            snapshots.insert(SnapshotSelector::Mark("before".into()), state.clone());
            let atom = || ClickProposition::Comparison {
                left: ContractExpression::At {
                    selector: SnapshotSelector::Mark("before".into()),
                    expression: Box::new(ContractExpression::CFragment(CExpression::Variable(
                        "x".into(),
                    ))),
                },
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(7))),
            };
            for depth in [4, 8, 16, 32] {
                let mut proposition = atom();
                for level in 0..depth {
                    let left = Box::new(atom());
                    let right = Box::new(proposition);
                    proposition = match level % 3 {
                        0 => ClickProposition::And(left, right),
                        1 => ClickProposition::Or(left, right),
                        _ => ClickProposition::Implies(left, right),
                    };
                }
                let (mut lowerer, context) = fixed_state_elaboration(
                    BTreeMap::new(),
                    BTreeMap::new(),
                    &state,
                    BTreeMap::from([("x".into(), int32(7))]),
                    BTreeMap::from([("x".into(), int32(9))]),
                    None,
                    &snapshots,
                    SpecDefinitions::new(&predicates, &functions),
                    BTreeSet::new(),
                    BTreeMap::new(),
                );
                PROPOSITION_VISITS.with(|visits| visits.set(0));
                let lowered = lowerer
                    .click_proposition_to_spec_proposition(&proposition, &context)
                    .unwrap();
                assert_eq!(
                    PROPOSITION_VISITS.with(|visits| visits.get()),
                    2 * depth + 1
                );
                let mut pending = vec![&lowered];
                let mut leaves = 0;
                while let Some(node) = pending.pop() {
                    match node {
                        SpecProposition::And(left, right)
                        | SpecProposition::Or(left, right)
                        | SpecProposition::Implies(left, right) => {
                            pending.push(left);
                            pending.push(right);
                        }
                        SpecProposition::Comparison { left, right, .. } => {
                            assert!(
                                matches!(left, SpecExpression::Value(value) if value == &int32(7))
                            );
                            assert!(
                                matches!(right, SpecExpression::Value(value) if value == &int32(7))
                            );
                            leaves += 1;
                        }
                        _ => panic!("lowering changed the proposition shape"),
                    }
                }
                assert_eq!(leaves, depth + 1);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A `decreases` component is refused when it names a state of its own,
/// wherever inside the component that state is named. The kernel reads the one
/// declared component at two states and ranks the values; a component that
/// fixes its own state reads one state twice, so both `old(...)` and any
/// `at(...)` snapshot, including a loop's own entry, are refused.
#[test]
fn a_fixed_state_anywhere_in_a_measure_is_found() {
    let current = ContractExpression::CBinding("n".to_string());
    assert!(fixed_measure_state(&current).is_none());

    let old = ContractExpression::Subtract(
        Box::new(current.clone()),
        Box::new(ContractExpression::Old(Box::new(current.clone()))),
    );
    assert!(matches!(
        fixed_measure_state(&old),
        Some(FixedMeasureState::Old)
    ));

    let loop_entry = SnapshotSelector::ProgramPoint(ProgramPointRef {
        region: CodeRegionRef::Loop(0),
        kind: ProgramPointKind::Entry,
    });
    let at = ContractExpression::Call {
        name: "head".to_string(),
        arguments: vec![ContractExpression::At {
            selector: loop_entry.clone(),
            expression: Box::new(current),
        }],
    };
    let found = fixed_measure_state(&at).expect("a snapshot in a call argument is a snapshot");
    let FixedMeasureState::At(selector) = &found else {
        panic!("the refusal names the snapshot, not `old`");
    };
    assert_eq!(selector, &loop_entry);
    assert_eq!(found.spelling(), "at(loop(0).entry, ...)");
}

#[test]
fn surface_binder_streams_refuse_before_another_producers_range() {
    let mut quantifier = SURFACE_QUANTIFIER_VARIABLE_CEILING - 1;
    assert_eq!(
        allocate_quantifier_variable(&mut quantifier),
        Ok(Variable(SURFACE_QUANTIFIER_VARIABLE_CEILING - 1)),
    );
    assert!(allocate_quantifier_variable(&mut quantifier).is_err());

    let last_algebraic_index = ((ALGEBRAIC_VARIABLE_CEILING - 1 - ALGEBRAIC_VARIABLE_BASE)
        / ALGEBRAIC_BINDER_STRIDE) as usize;
    assert!(algebraic_binder_variable(last_algebraic_index).is_ok());
    assert!(algebraic_binder_variable(last_algebraic_index + 1).is_err());
}

#[test]
fn captured_fold_identity_does_not_exhaust_the_surface_quantifier_stream() {
    let low = Variable(SURFACE_QUANTIFIER_VARIABLE_CEILING - 2);
    let high = Variable((1 << 43) + 17);
    let captured = crate::kernel::SpecIntegerExpression::Add(
        Box::new(crate::kernel::SpecIntegerExpression::Term(
            crate::kernel::IntegerTerm::var(low),
        )),
        Box::new(crate::kernel::SpecIntegerExpression::Term(
            crate::kernel::IntegerTerm::var(high),
        )),
    );
    assert_eq!(max_spec_integer_expression_variable(&captured), Some(low));
}

#[test]
fn old_record_steps_replay_both_operands_and_preserve_int_min_subtraction() {
    let declaration = crate::languages::c::syntax::parse_function(
        "struct item { int value; int other; }; struct item *offset(struct item *p, int i) { return p + i; }",
    ).unwrap();
    let layout = std::sync::Arc::new(declaration.structs()["item"].to_kernel_aggregate_layout());
    let old_pointer = crate::kernel::CPointerValue::new(
        crate::kernel::Pointer {
            block: "old-pointer".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    )
    .with_designation(crate::kernel::PointerDesignation::Unresolved(
        crate::kernel::Variable(98_701),
    ));
    let current_pointer = crate::kernel::CPointerValue::new(
        crate::kernel::Pointer {
            block: "current-pointer".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    )
    .with_designation(crate::kernel::PointerDesignation::Unresolved(
        crate::kernel::Variable(98_702),
    ));
    let snapshots = RecordedSnapshots::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    for (old_index, subtract, expected_bytes) in [
        (2u32, false, 16i64),
        (i32::MIN as u32, true, 17_179_869_184i64),
    ] {
        let entry = CState::new()
            .with_local("p", CValue::Pointer(old_pointer.clone()))
            .with_local("i", int32(old_index));
        let current = entry
            .clone()
            .with_local("p", CValue::Pointer(current_pointer.clone()))
            .with_local("i", int32(7));
        let (mut lowerer, context) = fixed_state_elaboration(
            BTreeMap::new(),
            BTreeMap::new(),
            &entry,
            BTreeMap::from([
                ("p".into(), CValue::Pointer(old_pointer.clone())),
                ("i".into(), int32(old_index)),
            ]),
            BTreeMap::from([
                ("p".into(), CValue::Pointer(current_pointer.clone())),
                ("i".into(), int32(7)),
            ]),
            None,
            &snapshots,
            SpecDefinitions::new(&predicates, &functions),
            BTreeSet::new(),
            parameter_pointer_element_widths(declaration.parameters()),
        );
        let native = CExpression::RecordPointerOffset {
            pointer: Box::new(c_variable("p")),
            index: Box::new(c_variable("i")),
            layout: layout.clone(),
            subtract,
        };
        let expression = ContractExpression::Old(Box::new(ContractExpression::CFragment(native)));
        let lowered = lowerer
            .lower_contract_expression_to_spec(&expression, &context)
            .unwrap();
        assert!(
            matches!(lowered, SpecExpression::Let { .. }),
            "the checked native operation remains scoped"
        );
        let (value, obligations) = crate::kernel::c_evaluate_spec_expression_at_state(
            &current,
            &lowered,
            Some(&entry),
            &PureFactContext::new(),
        )
        .unwrap();
        let CValue::Pointer(pointer) = value else {
            panic!("record step pointer");
        };
        assert_eq!(pointer.pointer().block, old_pointer.pointer().block);
        assert_eq!(
            pointer.pointer().offset,
            crate::kernel::PointerOffsetTerm::Constant(expected_bytes)
        );
        assert!(pointer.same_designation(&old_pointer));
        assert!(obligations.is_empty());
    }
}

#[test]
fn old_member_address_replays_the_original_record_carrier() {
    let declaration = crate::languages::c::syntax::parse_function(
        "struct item { int value; int other; }; int read(struct item *p) { return p->other; }",
    )
    .unwrap();
    let entry_pointer = crate::kernel::CPointerValue::new(
        crate::kernel::Pointer {
            block: "old-record".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    )
    .with_designation(crate::kernel::PointerDesignation::Unresolved(
        crate::kernel::Variable(98_711),
    ));
    let current_pointer = crate::kernel::CPointerValue::new(
        crate::kernel::Pointer {
            block: "current-record".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    );
    let entry = CState::new().with_local("p", CValue::Pointer(entry_pointer.clone()));
    let current = entry
        .clone()
        .with_local("p", CValue::Pointer(current_pointer.clone()));
    let snapshots = RecordedSnapshots::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (mut lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &entry,
        BTreeMap::from([("p".into(), CValue::Pointer(entry_pointer.clone()))]),
        BTreeMap::from([("p".into(), CValue::Pointer(current_pointer))]),
        None,
        &snapshots,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        parameter_pointer_element_widths(declaration.parameters()),
    );
    let address = CExpression::MemberAddress {
        object: Box::new(c_variable("p")),
        selection: std::sync::Arc::new(crate::kernel::CAggregateMemberSelection {
            layout: std::sync::Arc::new(declaration.structs()["item"].to_kernel_aggregate_layout()),
            path: vec!["other".to_string()].into(),
            value_type: CType::Int32,
        }),
    };
    let expression = ContractExpression::Old(Box::new(ContractExpression::CFragment(address)));
    let lowered = lowerer
        .lower_contract_expression_to_spec(&expression, &context)
        .unwrap();
    let (value, _) = crate::kernel::c_evaluate_spec_expression_at_state(
        &current,
        &lowered,
        Some(&entry),
        &PureFactContext::new(),
    )
    .unwrap();
    let CValue::Pointer(pointer) = value else {
        panic!("member address");
    };
    assert_eq!(pointer.pointer().block, entry_pointer.pointer().block);
    assert_eq!(
        pointer.pointer().offset,
        crate::kernel::PointerOffsetTerm::Constant(4)
    );
    assert!(pointer.same_designation(&entry_pointer));
}

#[test]
fn snapshot_scalar_local_address_keeps_its_full_carrier_after_current_scope_ends() {
    let _session = crate::kernel::VerificationSession::enter();
    let declaration = crate::kernel::c_declare_initialized(
        "obj",
        CType::UInt32,
        CExpression::Value(crate::kernel::uint32(7)),
        false,
        false,
        false,
        false,
    );
    let theorem = crate::kernel::prove_symbolic_c_execution_with_environment(
        CState::new(),
        declaration,
        PureFactContext::new(),
        crate::kernel::CExecutionEnvironment::new()
            .with_byte_order(crate::kernel::ByteOrder::Little),
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .unwrap();
    let mut conclusion = theorem.proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    let Proposition::CStatementExecutes {
        outcome: crate::kernel::CStatementOutcome::Normal(declared),
        ..
    } = conclusion
    else {
        panic!("checked declaration completes normally");
    };
    let declared = declared.as_ref().clone();
    let address = CExpression::AddressOf(Box::new(c_variable("obj")));
    let (expected, obligations) = crate::kernel::c_evaluate_spec_expression_at_state(
        &declared,
        &SpecExpression::CExpression(address.clone()),
        None,
        &PureFactContext::new(),
    )
    .unwrap();
    assert!(obligations.is_empty());
    let CValue::Pointer(pointer) = &expected else {
        panic!("declared pointer");
    };
    assert!(matches!(
        pointer.designation(),
        Some(crate::kernel::PointerDesignation::Object { .. })
    ));
    let current = CState::new().with_memory(
        declared
            .memory()
            .without_local_block(&pointer.pointer().block),
    );
    let mut snapshots = RecordedSnapshots::new();
    snapshots.insert(SnapshotSelector::Mark("before".into()), declared.clone());
    snapshots.insert(SnapshotSelector::Mark("after".into()), current.clone());
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (mut lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &declared,
        BTreeMap::from([("obj".into(), crate::kernel::uint32(7))]),
        BTreeMap::new(),
        None,
        &snapshots,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    let fragment = ContractExpression::CFragment(address.clone());
    let unary = ContractExpression::CUnary {
        operand: Box::new(ContractExpression::CFragment(c_variable("obj"))),
        lowered: address,
    };
    for source in [fragment, unary] {
        for selected in [
            ContractExpression::Old(Box::new(source.clone())),
            ContractExpression::At {
                selector: SnapshotSelector::Mark("before".into()),
                expression: Box::new(source.clone()),
            },
        ] {
            let lowered = lowerer
                .lower_contract_expression_to_spec(&selected, &context)
                .unwrap();
            let (value, obligations) = crate::kernel::c_evaluate_spec_expression_at_state(
                &current,
                &lowered,
                Some(&declared),
                &PureFactContext::new(),
            )
            .unwrap();
            assert_eq!(value, expected);
            assert!(obligations.is_empty());
        }
        let wrong = ContractExpression::At {
            selector: SnapshotSelector::Mark("after".into()),
            expression: Box::new(source),
        };
        assert!(
            lowerer
                .lower_contract_expression_to_spec(&wrong, &context)
                .is_err()
        );
    }
}

#[test]
fn proposition_snapshot_selection_matches_full_context_without_unrelated_bindings() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let entry = CState::new().with_local("used", int32(1));
    let atom = |expression| ClickProposition::Comparison {
        left: expression,
        operator: ComparisonOperator::Equal,
        right: ContractExpression::Binding("late".into()),
    };
    let proposition = ClickProposition::And(
        Box::new(atom(ContractExpression::At {
            selector: SnapshotSelector::Mark("before".into()),
            expression: Box::new(ContractExpression::Binding("used".into())),
        })),
        Box::new(atom(ContractExpression::Old(Box::new(
            ContractExpression::Binding("used".into()),
        )))),
    );
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut state = CState::new().with_local("used", int32(2));
        for index in 0..size {
            state = state.with_local(format!("unused{index}"), int32(index));
        }
        let mut snapshots = RecordedSnapshots::new();
        snapshots.insert(SnapshotSelector::Mark("before".into()), state);
        let (mut lowerer, context) = fixed_state_elaboration(
            BTreeMap::new(),
            BTreeMap::new(),
            &entry,
            BTreeMap::from([("used".into(), int32(1))]),
            BTreeMap::from([("used".into(), int32(9)), ("late".into(), int32(3))]),
            None,
            &snapshots,
            SpecDefinitions::new(&predicates, &functions),
            BTreeSet::new(),
            BTreeMap::new(),
        );
        let reference = lowerer
            .click_proposition_to_spec_proposition(&proposition, &context)
            .unwrap();
        let mut names = BTreeSet::new();
        collect_click_proposition_referenced_names(&proposition, &mut names);
        lowerer.capture_referenced_names = Some(names);
        let ((selected, projected), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let selected = lowerer
                    .click_proposition_to_spec_proposition(&proposition, &context)
                    .unwrap();
                let projected = lowerer
                    .snapshot_environment(&SnapshotSelector::Mark("before".into()), &context)
                    .unwrap()
                    .unwrap();
                (selected, projected)
            });
        assert_eq!(selected, reference);
        assert_eq!(projected.values.len(), 2);
        assert!(
            matches!(projected.values.get(&"used".to_string()), Some(SpecExpression::Value(value)) if value == &int32(2))
        );
        assert!(
            matches!(projected.values.get(&"late".to_string()), Some(SpecExpression::Value(value)) if value == &int32(3))
        );
        costs.push(work);
    }
    assert!(
        costs.iter().all(|cost| *cost == costs[0]),
        "snapshot selection costs: {costs:?}"
    );
}
