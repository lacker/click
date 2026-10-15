// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[test]
fn native_statement_execution_clears_specification_pointer_observation() {
    let _session = crate::kernel::VerificationSession::enter();
    let identity = Variable(988_160);
    let address = Pointer::symbolic(identity);
    let pointer = CPointerValue::new(address.clone(), CType::Int32Pointer)
        .with_designation(PointerDesignation::Unresolved(identity));
    let state = CState::new()
        .with_memory(
            CMemory::new()
                .with_block(address.block.clone(), 4)
                .store(address.clone(), int32(31)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                address,
                0.into(),
                1.into(),
                4,
            )),
        ));
    let expressions = [
        c_typed_load(
            CExpression::Value(CValue::Pointer(pointer.clone())),
            CType::Int32,
        ),
        c_cast(
            CExpression::Value(CValue::Pointer(pointer.clone())),
            CType::UInt64,
        ),
        c_pointer_offset_bytes(CExpression::Value(CValue::Pointer(pointer.clone())), 4),
    ];
    let executable = PureFactContext::new();
    for observations in [
        executable.clone().observe_pointer_addresses(),
        executable.clone().allow_symbolic_contract_loads(),
        executable
            .clone()
            .observe_pointer_addresses()
            .allow_symbolic_contract_loads(),
    ] {
        let cleared = observations.clone().without_pointer_address_observation();
        assert_eq!(cleared, executable);
        assert!(cleared.has_same_reasoning_policy(&executable));
        assert!(!cleared.should_require_owned_expression_loads());
        let owned = observations.clone().require_owned_expression_loads();
        assert!(
            owned
                .clone()
                .without_pointer_address_observation()
                .should_require_owned_expression_loads()
        );
        for expression in &expressions {
            let paths = evaluate_c_expression_paths(
                &state,
                expression,
                &observations,
                &mut ExecutionBudget::for_c_expression(expression),
            )
            .unwrap();
            assert!(
                paths
                    .iter()
                    .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
            );
            let statement = CStatement::Return(expression.clone());
            let paths = execute_c_statement_paths(
                &state,
                &statement,
                &observations,
                CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                &mut ExecutionBudget::for_new_execution(),
            )
            .unwrap();
            assert!(!paths.is_empty());
            assert!(
                paths
                    .iter()
                    .all(|path| if matches!(expression, CExpression::Cast { .. }) {
                        matches!(
                            &path.outcome,
                            CStatementOutcome::Return { value: CValue::PointerInteger(value), .. }
                                if value.origin() == &pointer
                        )
                    } else {
                        matches!(path.outcome, CStatementOutcome::UndefinedBehavior(_))
                    }),
                "observation must not authorize native access or formation: {paths:?}"
            );
            if matches!(expression, CExpression::Cast { .. }) {
                let function = c_function(
                    CType::UInt64,
                    "observer_cast",
                    vec![],
                    c_return(expression.clone()),
                );
                let paths = crate::kernel::functions::execute_c_function_call_paths(
                    &state,
                    &function,
                    &[],
                    &observations,
                    CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                    &mut ExecutionBudget::for_new_execution(),
                )
                .unwrap();
                assert!(!paths.is_empty());
                assert!(paths.iter().all(|path| matches!(
                    &path.outcome,
                    CFunctionOutcome::Return { value: CValue::PointerInteger(value), .. }
                        if value.origin() == &pointer
                )));
            }
        }
    }
}

#[test]
fn symbolic_contract_address_observation_preserves_unresolved_carriers_without_access() {
    let _session = crate::kernel::VerificationSession::enter();
    let identity = Variable(988_100);
    let root = Pointer::symbolic(identity);
    let pointer = CPointerValue::new(root.clone(), CType::UInt8Pointer)
        .with_designation(PointerDesignation::Unresolved(identity))
        .with_pointee_constant(true)
        .with_pointee_volatile(true);
    let layout = std::sync::Arc::new(CAggregateLayout::new(
        16,
        4,
        vec![
            CAggregateField::new("value", 4, CType::Int32),
            CAggregateField::new("items", 8, CType::Int32Array(2)),
        ],
    ));
    let member = |name: &str, value_type| CExpression::MemberAddress {
        object: Box::new(CExpression::Value(CValue::Pointer(pointer.clone()))),
        selection: std::sync::Arc::new(CAggregateMemberSelection {
            layout: layout.clone(),
            path: vec![name.into()].into(),
            value_type,
        }),
    };
    let expressions = [
        (member("value", CType::Int32), 4),
        (
            c_typed_load(member("items", CType::Int32Array(2)), CType::Int32Array(2)),
            8,
        ),
        (
            c_pointer_offset_bytes(
                CExpression::Value(CValue::Pointer(
                    pointer.clone().with_type(CType::Int32Pointer),
                )),
                4,
            ),
            4,
        ),
    ];
    let state = CState::new();
    let executable = PureFactContext::new();
    let logical = executable.clone().observe_pointer_addresses();
    assert!(!logical.should_allow_symbolic_contract_loads());
    let owned = logical.clone().require_owned_expression_loads();
    assert!(!owned.should_observe_pointer_addresses());
    assert!(!owned.should_allow_symbolic_contract_loads());
    for (expression, offset) in expressions {
        let paths = evaluate_c_expression_paths(
            &state,
            &expression,
            &logical,
            &mut ExecutionBudget::for_c_expression(&expression),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one logical observation: {paths:?}")
        };
        let CExpressionOutcome::Value(CValue::Pointer(observed)) = &path.outcome else {
            panic!("logical observation must retain the unresolved address: {path:?}")
        };
        assert_eq!(observed.pointer(), &root.offset_by_bytes(offset));
        assert_eq!(observed.c_type(), CType::Int32Pointer);
        assert!(observed.same_designation(&pointer));
        assert!(
            matches!(observed.designation(), Some(PointerDesignation::Unresolved(found)) if *found == identity)
        );
        assert!(observed.pointee_constant() && observed.pointee_volatile());
        assert!(path.obligations.is_empty());
        for assumptions in [&executable, &owned] {
            let paths = evaluate_c_expression_paths(
                &state,
                &expression,
                assumptions,
                &mut ExecutionBudget::for_c_expression(&expression),
            )
            .unwrap();
            assert!(!paths.is_empty());
            assert!(
                paths
                    .iter()
                    .all(|path| matches!(path.outcome, CExpressionOutcome::UndefinedBehavior(_))),
                "unwitnessed executable address must be refused: {paths:?}"
            );
        }
    }
    assert_eq!(state.memory().cells.representation_len(), 0);
}

#[test]
fn pointer_address_observation_keeps_scalar_and_pointer_read_requirements() {
    let _session = crate::kernel::VerificationSession::enter();
    let executable = PureFactContext::new();
    let observation = executable.clone().observe_pointer_addresses();
    assert!(!observation.should_allow_symbolic_contract_loads());
    let owned = observation.clone().require_owned_expression_loads();
    assert!(!owned.should_observe_pointer_addresses());
    assert!(!owned.should_allow_symbolic_contract_loads());

    let backing = CMemory::local_pointer("observed-backing");
    let backing_memory =
        CMemory::new().with_declared_scalar_block(backing.block.clone(), 4, CType::Int32);
    let backing_pointer = backing_memory
        .declared_scalar_pointer(&backing, CType::Int32)
        .unwrap();
    for (index, value) in [int32(31), CValue::Pointer(backing_pointer)]
        .into_iter()
        .enumerate()
    {
        let address = Pointer::symbolic(Variable(988_110 + index as u64));
        let value_type = value.c_type();
        let bytes = value_type.byte_width();
        let expression = c_typed_load(
            CExpression::Value(CValue::typed_pointer(
                address.clone(),
                value_type.pointer_to().unwrap(),
            )),
            value_type,
        );
        let read_permission = |width| {
            ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(address.clone(), 0.into(), 1.into(), width),
            ))
        };
        let initialized = backing_memory
            .clone()
            .with_block(address.block.clone(), bytes)
            .store(address.clone(), value.clone());
        let readable = CState::new()
            .with_memory(initialized.clone())
            .with_resource_context(read_permission(bytes));
        let uninitialized = CState::new()
            .with_memory(
                backing_memory
                    .clone()
                    .with_uninitialized_block(address.block.clone(), bytes),
            )
            .with_resource_context(read_permission(bytes));
        for assumptions in [&executable, &observation, &owned] {
            let evaluate = |state: &CState| {
                evaluate_c_expression_paths(
                    state,
                    &expression,
                    assumptions,
                    &mut ExecutionBudget::for_c_expression(&expression),
                )
                .unwrap()
            };
            let paths = evaluate(&readable);
            let [path] = paths.as_slice() else {
                panic!("one permitted read: {paths:?}");
            };
            assert_eq!(path.outcome, CExpressionOutcome::Value(value.clone()));
            assert!(path.obligations.is_empty());
            for denied in [
                CState::new().with_memory(initialized.clone()),
                CState::new()
                    .with_memory(initialized.clone())
                    .with_resource_context(read_permission(bytes - 1)),
            ] {
                let paths = evaluate(&denied);
                assert!(!paths.is_empty());
                assert!(
                    paths.iter().all(|path| matches!(
                        path.outcome,
                        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
                    )),
                    "address observation must not create byte authority: {paths:?}"
                );
            }
            let paths = evaluate(&uninitialized);
            assert!(!paths.is_empty());
            assert!(
                paths.iter().all(|path| matches!(
                    path.outcome,
                    CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
                )),
                "address observation must not initialize a cell: {paths:?}"
            );
            let wrong_type = CState::new()
                .with_memory(
                    backing_memory
                        .clone()
                        .with_block(address.block.clone(), bytes)
                        .store(
                            address.clone(),
                            if value_type.is_object_pointer() {
                                int32(31)
                            } else {
                                uint8(31)
                            },
                        ),
                )
                .with_resource_context(read_permission(bytes));
            let paths = evaluate(&wrong_type);
            assert!(!paths.is_empty());
            assert!(
                paths.iter().all(|path| matches!(
                    path.outcome,
                    CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch { .. })
                )),
                "address observation must not manufacture a compatible typed cell: {paths:?}"
            );
        }
    }
}

/// The only specification-conditional branch lowering decides is the one a
/// literally constant condition folds away. Folding stays exact in both
/// directions; a condition that needs an ambient fact is not decided here,
/// so both branches are lowered and a proof step picks the arm.
#[test]
fn a_specification_condition_folds_only_when_it_is_constant() {
    let flag = Bitvector32Term::Variable(Variable(4241));
    let constant_true =
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), Bitvector32Term::Constant(2));
    let constant_false =
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(2), Bitvector32Term::Constant(1));
    let ambient = ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), flag.clone());

    for (condition, expected) in [(constant_true, true), (constant_false, false)] {
        assert_eq!(
            constant_spec_condition_value(&Proposition::ConditionIs(condition.clone(), true)),
            Some(expected)
        );
        assert_eq!(
            constant_spec_condition_value(&Proposition::ConditionIs(condition, false)),
            Some(!expected)
        );
    }

    // Ambient facts are exactly what lowering must not consult: the same
    // condition stays undecided however much the surrounding context knows.
    let knows_the_condition = PureFactContext::new().assume_condition(ambient.clone(), true);
    assert_eq!(knows_the_condition.decide(&ambient), Some(true));
    for value in [true, false] {
        assert_eq!(
            constant_spec_condition_value(&Proposition::ConditionIs(ambient.clone(), value)),
            None
        );
    }
}

// A specification's conversion owes each bound the context does not
// prove; C's conversion owes none and is the same low word.
#[test]
fn checked_wide_to_int_narrowing_requires_each_representability_bound() {
    let value = Bitvector32Term::Variable(Variable(912));
    let lower = ConditionTerm::int64_signed_greater_equal(
        value.clone(),
        Bitvector32Term::Int64Constant(i64::from(i32::MIN)),
    );
    let signed_upper = ConditionTerm::int64_signed_less_equal(
        value.clone(),
        Bitvector32Term::Int64Constant(i64::from(i32::MAX)),
    );
    let unsigned_upper = ConditionTerm::uint64_less_equal(
        value.clone(),
        Bitvector32Term::UInt64Constant(i32::MAX as u64),
    );
    for (input, bounds) in [
        (CValue::Int64(value.clone()), vec![lower, signed_upper]),
        (CValue::UInt64(value.clone()), vec![unsigned_upper]),
    ] {
        for provided in 0..=bounds.len() {
            let mut assumptions = PureFactContext::new();
            for bound in &bounds[..provided] {
                assumptions = assumptions.assume_condition(bound.clone(), true);
            }
            let mut obligations = Vec::new();
            let modular = crate::kernel::eval::coerce_c_value_to_type(
                input.clone(),
                CType::Int32,
                &mut obligations,
                &assumptions,
            )
            .unwrap();
            assert_eq!(
                modular,
                CValue::Int32(Bitvector32Term::uint32_from_64(value.clone()))
            );
            assert!(obligations.is_empty());
            let result = crate::kernel::eval::coerce_c_value_to_type_as(
                input.clone(),
                CType::Int32,
                crate::kernel::eval::IntegerConversion::Checked,
                &mut obligations,
                &assumptions,
            )
            .unwrap();
            assert_eq!(result, modular);
            assert_eq!(obligations.len(), bounds.len() - provided);
            for (obligation, bound) in obligations.iter().zip(&bounds[provided..]) {
                assert_eq!(
                    obligation.proposition(),
                    &Proposition::ConditionIs(bound.clone(), true)
                );
            }
        }
    }
}

#[test]
fn wide_to_int_narrowing_checks_signed_and_unsigned_boundaries() {
    use crate::kernel::eval::IntegerConversion;
    let convert = |value: CValue, conversion, obligations: &mut Vec<ProofObligation>| {
        crate::kernel::eval::coerce_c_value_to_type_as(
            value,
            CType::Int32,
            conversion,
            obligations,
            &PureFactContext::new(),
        )
    };
    for value in [
        i64::MIN,
        i64::from(i32::MIN) - 1,
        i64::from(i32::MIN),
        -1,
        0,
        i64::from(i32::MAX),
        i64::from(i32::MAX) + 1,
        i64::MAX,
    ] {
        let mut obligations = Vec::new();
        let input = CValue::Int64(Bitvector32Term::Int64Constant(value));
        // C's conversion keeps the low word, read as signed.
        assert_eq!(
            convert(input.clone(), IntegerConversion::Modular, &mut obligations),
            Some(int32(value as u32))
        );
        assert!(obligations.is_empty());
        let result = convert(input, IntegerConversion::Checked, &mut obligations);
        assert_eq!(result, Some(int32(value as u32)));
        assert_eq!(obligations.is_empty(), i32::try_from(value).is_ok());
        for obligation in &obligations {
            let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
                panic!("narrowing owes an explicit range comparison");
            };
            assert_eq!(
                PureFactContext::decide_intrinsically(condition),
                Some(false)
            );
            assert!(obligation.context().unwrap().starts_with("int32 narrowing"));
        }
    }
    for value in [
        0,
        i32::MAX as u64,
        i32::MAX as u64 + 1,
        u32::MAX as u64,
        u64::MAX,
    ] {
        let mut obligations = Vec::new();
        let input = CValue::UInt64(Bitvector32Term::UInt64Constant(value));
        assert_eq!(
            convert(input.clone(), IntegerConversion::Modular, &mut obligations),
            Some(int32(value as u32))
        );
        assert!(obligations.is_empty());
        let result = convert(input, IntegerConversion::Checked, &mut obligations);
        assert_eq!(result, Some(int32(value as u32)));
        assert_eq!(obligations.is_empty(), value <= i32::MAX as u64);
        for obligation in &obligations {
            let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
                panic!("narrowing owes an explicit range comparison");
            };
            assert_eq!(
                PureFactContext::decide_intrinsically(condition),
                Some(false)
            );
            assert_eq!(obligation.context(), Some("int32 narrowing upper bound"));
        }
    }
}

#[test]
fn wide_equality_bounds_use_incremental_index_and_preserve_branches() {
    for size in [16usize, 64, 256, 1024] {
        let start = crate::persistent::persistent_node_allocations();
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(1000 + i as u64)),
                    Bitvector32Term::UInt64Constant(i as u64),
                ),
                true,
            );
        }
        let allocations = crate::persistent::persistent_node_allocations() - start;
        assert!(
            allocations < 80 * size * (size.ilog2() as usize + 1),
            "{size}: {allocations}"
        );
        let target = Bitvector32Term::Variable(Variable(1000));
        let bound =
            ConditionTerm::uint64_less_equal(target.clone(), Bitvector32Term::UInt64Constant(1));
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&bound));
        assert_eq!(answer, Some(true));
        assert!(
            work <= 16,
            "unrelated equalities inflated query work: {size}: {work}"
        );
        let original = facts.clone();
        let equality = ConditionTerm::uint64_equal(target, Bitvector32Term::UInt64Constant(0));
        let changed = facts.assume_condition(equality, false);
        assert_eq!(changed.decide(&bound), None);
        assert_eq!(original.decide(&bound), Some(true));
    }
}

#[test]
fn wide_equality_bounds_keep_width_sign_and_exact_premises() {
    let x = Bitvector32Term::Variable(Variable(950));
    let y = Bitvector32Term::Variable(Variable(951));
    let signed_bound =
        ConditionTerm::int64_signed_less_equal(x.clone(), Bitvector32Term::Int64Constant(0));
    let unsigned_bound =
        ConditionTerm::uint64_less_equal(x.clone(), Bitvector32Term::UInt64Constant(0));
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::uint64_equal(x.clone(), y.clone()), true)
        .assume_condition(
            ConditionTerm::uint64_equal(y, Bitvector32Term::UInt64Constant(u64::MAX)),
            true,
        );
    assert_eq!(facts.decide(&signed_bound), Some(true));
    assert_eq!(facts.decide(&unsigned_bound), Some(false));
    let narrowed = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::uint32_from_64(x.clone()),
            Bitvector32Term::Constant(u32::MAX),
        ),
        true,
    );
    assert!(facts.proves(&narrowed));
    assert!(facts.derive_atomic_proposition(&narrowed).is_some());
    assert!(facts.derive_simp_atomic_proposition(&narrowed).is_some());
    // A 32-bit equality is not evidence about all 64 bits of a wide term.
    let narrow_facts = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(x, Bitvector32Term::Constant(0)), true);
    assert_eq!(narrow_facts.decide(&unsigned_bound), None);
    let proposition = Proposition::ConditionIs(signed_bound, true);
    let derivation = facts.derive_atomic_proposition(&proposition).unwrap();
    assert!(derivation.check(&facts));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn unsigned_64_to_32_narrowing_preserves_only_low_bits() {
    for (input, expected) in [
        (Bitvector32Term::UInt64Constant(u64::MAX), u32::MAX),
        (Bitvector32Term::UInt64Constant((1u64 << 32) + 7), 7),
        (Bitvector32Term::Int64Constant(-1), u32::MAX),
        (Bitvector32Term::Int64Constant(i64::MIN), 0),
    ] {
        assert_eq!(
            Bitvector32Term::uint32_from_64(input),
            Bitvector32Term::Constant(expected)
        );
    }
    let x = Bitvector32Term::Variable(Variable(1));
    for wide in [
        Bitvector32Term::uint64_from_32(x.clone()),
        Bitvector32Term::int64_from_32(x.clone()),
        Bitvector32Term::int64_from_uint32(x.clone()),
        Bitvector32Term::uint64_from_int32(x.clone()),
    ] {
        assert_eq!(Bitvector32Term::uint32_from_64(wide), x);
    }
    let narrow = Bitvector32Term::uint32_from_64(x.clone());
    assert_ne!(narrow, x);
    assert_ne!(Bitvector32Term::uint64_from_32(narrow), x);
}

#[test]
fn narrowed_shift_bounds_do_not_discard_possible_high_counts() {
    let x = Bitvector32Term::Variable(Variable(1));
    for count in 0..=64 {
        let narrowed =
            Bitvector32Term::uint32_from_64(Bitvector32Term::uint64_logical_shift_right(
                x.clone(),
                Bitvector32Term::Constant(count),
            ));
        let below =
            ConditionTerm::unsigned_less_than(narrowed.clone(), Bitvector32Term::Constant(32));
        let above = ConditionTerm::unsigned_greater_equal(narrowed, Bitvector32Term::Constant(32));
        if (59..64).contains(&count) {
            assert_eq!(below, ConditionTerm::Constant(true));
            assert_eq!(above, ConditionTerm::Constant(false));
        } else {
            assert_ne!(below, ConditionTerm::Constant(true));
            assert_ne!(above, ConditionTerm::Constant(false));
        }
    }
    for mask in [0, 31, 32, u32::MAX] {
        let masked = Bitvector32Term::bitwise_and(x.clone(), Bitvector32Term::Constant(mask));
        let below = ConditionTerm::unsigned_less_than(masked, Bitvector32Term::Constant(32));
        assert_eq!(below == ConditionTerm::Constant(true), mask < 32);
    }
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
fn floating_point_constant_conversions_round_in_integer_space() {
    let state = CState::new();
    let cases = [
        (
            c_cast(c_uint64_literal(16_777_217), CType::Float32),
            CValue::Float32(Bitvector32Term::Constant(0x4b80_0000)),
        ),
        (
            c_cast(c_uint64_literal(9_007_199_254_740_993), CType::Float64),
            CValue::Float64(Bitvector32Term::UInt64Constant(0x4340_0000_0000_0000)),
        ),
        (
            c_cast(c_float64_literal(0x3ff0_0000_1000_0000), CType::Float32),
            CValue::Float32(Bitvector32Term::Constant(0x3f80_0000)),
        ),
        (
            c_cast(c_float32_literal(0x3fc0_0000), CType::Float64),
            CValue::Float64(Bitvector32Term::UInt64Constant(0x3ff8_0000_0000_0000)),
        ),
        (
            c_cast(c_int64_literal(-16_777_217), CType::Float32),
            CValue::Float32(Bitvector32Term::Constant(0xcb80_0000)),
        ),
    ];

    for (expression, expected) in cases {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("constant floating conversion should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn floating_point_to_integer_conversion_truncates_and_rejects_invalid_values() {
    let state = CState::new();
    let valid = [
        (
            c_cast(c_float32_literal(0x4070_0000), CType::Int32),
            CValue::Int32(Bitvector32Term::Constant(3)),
        ),
        (
            c_cast(c_float64_literal(0xc00e_0000_0000_0000), CType::Int64),
            CValue::Int64(Bitvector32Term::Int64Constant(-3)),
        ),
        (
            c_cast(c_float64_literal(0x8000_0000_0000_0000), CType::UInt32),
            CValue::UInt32(Bitvector32Term::Constant(0)),
        ),
    ];
    for (expression, expected) in valid {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("valid floating-to-integer conversion should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    for expression in [
        c_cast(c_float64_literal(0x7ff8_0000_0000_0000), CType::Int32),
        c_cast(c_float64_literal(0x7ff0_0000_0000_0000), CType::Int32),
        c_cast(c_float64_literal(0x41e0_0000_0000_0000), CType::Int32),
        c_cast(c_float64_literal(0x7fef_ffff_ffff_ffff), CType::Int64),
    ] {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("invalid floating-to-integer conversion should retain a diagnostic");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            }
        );
    }
}

#[test]
fn floating_point_conditions_follow_ieee_ordering_and_classification() {
    let state = CState::new();
    let evaluate = |condition| {
        let evaluation =
            prove_symbolic_c_condition_evaluation(state.clone(), condition, PureFactContext::new());
        assert_eq!(evaluation.paths().len(), 1);
        match evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications()
        {
            Proposition::CConditionEvaluates {
                outcome: CConditionOutcome::Value(value),
                ..
            } => *value,
            proposition => panic!("unexpected concrete float condition {proposition:?}"),
        }
    };
    let assert_ordering =
        |left: CExpression, right: CExpression, expected: (bool, bool, bool, bool, bool, bool)| {
            assert_eq!(
                evaluate(c_less_than(left.clone(), right.clone())),
                expected.0
            );
            assert_eq!(
                evaluate(c_less_equal(left.clone(), right.clone())),
                expected.1
            );
            assert_eq!(
                evaluate(c_greater_than(left.clone(), right.clone())),
                expected.2
            );
            assert_eq!(
                evaluate(c_greater_equal(left.clone(), right.clone())),
                expected.3
            );
            assert_eq!(evaluate(c_equal(left.clone(), right.clone())), expected.4);
            assert_eq!(evaluate(c_not_equal(left, right)), expected.5);
        };

    assert_ordering(
        c_float32_literal(1.0f32.to_bits()),
        c_float32_literal(2.0f32.to_bits()),
        (true, true, false, false, false, true),
    );
    assert_ordering(
        c_float64_literal(1.0f64.to_bits()),
        c_float64_literal(2.0f64.to_bits()),
        (true, true, false, false, false, true),
    );
    assert_ordering(
        c_float32_literal(0),
        c_float32_literal(0x8000_0000),
        (false, true, false, true, true, false),
    );
    assert_ordering(
        c_float64_literal(0),
        c_float64_literal(0x8000_0000_0000_0000),
        (false, true, false, true, true, false),
    );
    assert_ordering(
        c_float32_literal(0x7fc0_0000),
        c_float32_literal(1.0f32.to_bits()),
        (false, false, false, false, false, true),
    );
    assert_ordering(
        c_float64_literal(0x7ff8_0000_0000_0000),
        c_float64_literal(1.0f64.to_bits()),
        (false, false, false, false, false, true),
    );

    let classifications = [
        (1.0f32.to_bits(), CFloatClassification::Finite),
        (f32::INFINITY.to_bits(), CFloatClassification::Infinite),
        (0, CFloatClassification::Zero),
        (1, CFloatClassification::Subnormal),
        (0x7fc0_0000, CFloatClassification::Nan),
    ];
    for (bits, expected_classification) in classifications {
        for classification in [
            CFloatClassification::Finite,
            CFloatClassification::Infinite,
            CFloatClassification::Zero,
            CFloatClassification::Subnormal,
            CFloatClassification::Nan,
        ] {
            assert_eq!(
                evaluate(c_float_classification(
                    c_float32_literal(bits),
                    classification,
                )),
                match expected_classification {
                    CFloatClassification::Finite => classification == CFloatClassification::Finite,
                    CFloatClassification::Zero => matches!(
                        classification,
                        CFloatClassification::Finite | CFloatClassification::Zero
                    ),
                    CFloatClassification::Subnormal => matches!(
                        classification,
                        CFloatClassification::Finite | CFloatClassification::Subnormal
                    ),
                    _ => classification == expected_classification,
                }
            );
        }
    }
}

#[test]
fn symbolic_floating_conditions_split_and_preserve_float_truthiness() {
    let variable = Variable(901);
    let state = CState::new().with_local("value", float32(Bitvector32Term::Variable(variable)));
    let outcomes = |condition| {
        prove_symbolic_c_condition_evaluation(state.clone(), condition, PureFactContext::new())
            .paths()
            .iter()
            .map(
                |path| match path.theorem().proposition().peel_implications() {
                    Proposition::CConditionEvaluates { outcome, .. } => outcome.clone(),
                    proposition => panic!("unexpected symbolic float condition {proposition:?}"),
                },
            )
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(
        outcomes(c_less_than(
            c_variable("value"),
            c_float32_literal(1.0f32.to_bits()),
        )),
        BTreeSet::from([
            CConditionOutcome::Value(false),
            CConditionOutcome::Value(true),
        ])
    );
    assert_eq!(
        outcomes(c_float_classification(
            c_variable("value"),
            CFloatClassification::Nan,
        )),
        BTreeSet::from([
            CConditionOutcome::Value(false),
            CConditionOutcome::Value(true),
        ])
    );
    assert_eq!(
        outcomes(c_variable("value")),
        BTreeSet::from([
            CConditionOutcome::Value(false),
            CConditionOutcome::Value(true),
        ])
    );
}

#[test]
fn floating_point_arithmetic_rounds_both_widths_in_integer_space() {
    let state = CState::new();
    let evaluate = |expression| {
        let theorem = prove_c_expression_evaluation(state.clone(), expression)
            .expect("constant floating arithmetic should evaluate");
        match theorem.proposition() {
            Proposition::CExpressionEvaluates { outcome, .. } => outcome.clone(),
            proposition => panic!("unexpected floating arithmetic theorem {proposition:?}"),
        }
    };

    assert_eq!(
        evaluate(c_add(
            c_float32_literal(1.0f32.to_bits()),
            c_float32_literal(2.0f32.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float32(
            Bitvector32Term::Constant(3.0f32.to_bits(),)
        ))
    );
    assert_eq!(
        evaluate(c_subtract(
            c_float32_literal(1.0f32.to_bits()),
            c_float32_literal(2.0f32.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float32(Bitvector32Term::Constant(
            (-1.0f32).to_bits(),
        )))
    );
    assert_eq!(
        evaluate(c_multiply(
            c_float32_literal(1.5f32.to_bits()),
            c_float32_literal(2.0f32.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float32(
            Bitvector32Term::Constant(3.0f32.to_bits(),)
        ))
    );
    assert_eq!(
        evaluate(c_divide(
            c_float32_literal(3.0f32.to_bits()),
            c_float32_literal(2.0f32.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float32(
            Bitvector32Term::Constant(1.5f32.to_bits(),)
        ))
    );

    assert_eq!(
        evaluate(c_add(
            c_float64_literal(1.0f64.to_bits()),
            c_float64_literal(2.0f64.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::UInt64Constant(
            3.0f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(c_multiply(
            c_float64_literal(1.5f64.to_bits()),
            c_float64_literal(2.0f64.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::UInt64Constant(
            3.0f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(c_divide(
            c_float64_literal(3.0f64.to_bits()),
            c_float64_literal(2.0f64.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::UInt64Constant(
            1.5f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(c_float_negate(c_float32_literal(0x8000_0000))),
        CExpressionOutcome::Value(CValue::Float32(Bitvector32Term::Constant(0)))
    );
    assert_eq!(
        evaluate(c_float_negate(c_float64_literal(0))),
        CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::UInt64Constant(
            0x8000_0000_0000_0000,
        )))
    );
}

#[test]
fn floating_point_arithmetic_preserves_ieee_exceptions_and_ties() {
    let state = CState::new();
    let evaluate = |expression| {
        let theorem = prove_c_expression_evaluation(state.clone(), expression)
            .expect("constant floating arithmetic should evaluate");
        match theorem.proposition() {
            Proposition::CExpressionEvaluates { outcome, .. } => outcome.clone(),
            proposition => panic!("unexpected floating arithmetic theorem {proposition:?}"),
        }
    };
    let f32_value =
        |bits| CExpressionOutcome::Value(CValue::Float32(Bitvector32Term::Constant(bits)));
    let f64_value =
        |bits| CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::UInt64Constant(bits)));

    // The halfway case rounds to the even significand; an exact ulp reaches
    // the next representable value.
    assert_eq!(
        evaluate(c_add(
            c_float32_literal(0x3f80_0000),
            c_float32_literal(0x3380_0000),
        )),
        f32_value(0x3f80_0000)
    );
    assert_eq!(
        evaluate(c_add(
            c_float32_literal(0x3f80_0000),
            c_float32_literal(0x3440_0000),
        )),
        f32_value(0x3f80_0002)
    );
    assert_eq!(
        evaluate(c_add(
            c_float32_literal(0x3f80_0000),
            c_float32_literal(0x3400_0000),
        )),
        f32_value(0x3f80_0001)
    );
    assert_eq!(
        evaluate(c_add(
            c_float64_literal(0x3ff0_0000_0000_0000),
            c_float64_literal(0x3ca0_0000_0000_0000),
        )),
        f64_value(0x3ff0_0000_0000_0000)
    );

    assert_eq!(
        evaluate(c_add(
            c_float32_literal(0x7f7f_ffff),
            c_float32_literal(0x7f7f_ffff),
        )),
        f32_value(0x7f80_0000)
    );
    assert_eq!(
        evaluate(c_add(
            c_float32_literal(0x7f80_0000),
            c_float32_literal(0xff80_0000),
        )),
        f32_value(0x7fc0_0000)
    );
    assert_eq!(
        evaluate(c_divide(c_float32_literal(0), c_float32_literal(0),)),
        f32_value(0x7fc0_0000)
    );
    assert_eq!(
        evaluate(c_divide(
            c_float32_literal(0x0080_0000),
            c_float32_literal(2.0f32.to_bits()),
        )),
        f32_value(0x0040_0000)
    );
    assert_eq!(
        evaluate(c_divide(
            c_float32_literal(1),
            c_float32_literal(2.0f32.to_bits()),
        )),
        f32_value(0)
    );
    assert_eq!(
        evaluate(c_divide(
            c_float64_literal(0x0010_0000_0000_0000),
            c_float64_literal(2.0f64.to_bits()),
        )),
        f64_value(0x0008_0000_0000_0000)
    );
    assert_eq!(
        evaluate(c_divide(
            c_float64_literal(1),
            c_float64_literal(2.0f64.to_bits()),
        )),
        f64_value(0)
    );
    assert_eq!(
        evaluate(c_multiply(
            c_float32_literal(f32::INFINITY.to_bits()),
            c_float32_literal(0),
        )),
        f32_value(0x7fc0_0000)
    );
    assert_eq!(
        evaluate(c_divide(
            c_float64_literal(1.0f64.to_bits()),
            c_float64_literal(0),
        )),
        f64_value(0x7ff0_0000_0000_0000)
    );
    assert_eq!(
        evaluate(c_divide(
            c_float64_literal(f64::INFINITY.to_bits()),
            c_float64_literal(f64::INFINITY.to_bits()),
        )),
        f64_value(0x7ff8_0000_0000_0000)
    );
    assert_eq!(
        evaluate(c_add(
            c_float64_literal(0x7fef_ffff_ffff_ffff),
            c_float64_literal(0x7fef_ffff_ffff_ffff),
        )),
        f64_value(0x7ff0_0000_0000_0000)
    );
    assert_eq!(
        evaluate(c_multiply(
            c_float32_literal(0x8000_0000),
            c_float32_literal(1.0f32.to_bits()),
        )),
        f32_value(0x8000_0000)
    );
}

#[test]
fn symbolic_floating_arithmetic_remains_typed_and_opaque() {
    let variable = Variable(902);
    let state = CState::new().with_local("value", float32(Bitvector32Term::Variable(variable)));
    let expression = c_add(c_variable("value"), c_float32_literal(1.0f32.to_bits()));
    let theorem = prove_c_expression_evaluation(state, expression).expect("symbolic float add");
    let Proposition::CExpressionEvaluates {
        outcome: CExpressionOutcome::Value(CValue::Float32(term)),
        ..
    } = theorem.proposition()
    else {
        panic!("symbolic float addition should produce a float value");
    };
    assert!(matches!(term, Bitvector32Term::Float32Binary { .. }));
}

#[test]
fn mixed_floating_arithmetic_promotes_to_the_wider_or_present_float_type() {
    let state = CState::new();
    let evaluate = |expression| {
        let theorem = prove_c_expression_evaluation(state.clone(), expression)
            .expect("mixed floating arithmetic should evaluate");
        match theorem.proposition() {
            Proposition::CExpressionEvaluates { outcome, .. } => outcome.clone(),
            proposition => panic!("unexpected mixed floating theorem {proposition:?}"),
        }
    };

    assert_eq!(
        evaluate(c_add(
            c_float32_literal(1.5f32.to_bits()),
            c_float64_literal(2.0f64.to_bits()),
        )),
        CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::UInt64Constant(
            3.5f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(c_add(
            c_float32_literal(1.5f32.to_bits()),
            c_int32_literal(2)
        )),
        CExpressionOutcome::Value(CValue::Float32(
            Bitvector32Term::Constant(3.5f32.to_bits(),)
        ))
    );
    assert_eq!(
        evaluate(c_less_than(
            c_float64_literal(1.0f64.to_bits()),
            c_int32_literal(2),
        )),
        CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Constant(1)))
    );
}

#[test]
fn symbolic_float_conversions_remain_typed_and_float_to_integer_is_guarded() {
    let f32_variable = Variable(903);
    let f64_variable = Variable(904);
    let integer_variable = Variable(905);
    let state = CState::new()
        .with_local("f32", float32(Bitvector32Term::Variable(f32_variable)))
        .with_local("f64", float64(Bitvector32Term::Variable(f64_variable)))
        .with_local(
            "integer",
            int32(Bitvector32Term::Variable(integer_variable)),
        );

    let theorem =
        prove_c_expression_evaluation(state.clone(), c_cast(c_variable("integer"), CType::Float64))
            .expect("symbolic integer-to-float conversion should evaluate");
    let Proposition::CExpressionEvaluates {
        outcome: CExpressionOutcome::Value(CValue::Float64(term)),
        ..
    } = theorem.proposition()
    else {
        panic!("symbolic integer-to-float conversion should produce a double");
    };
    assert!(matches!(
        term,
        Bitvector32Term::PureFunctionApplication { .. }
    ));

    let theorem =
        prove_c_expression_evaluation(state.clone(), c_cast(c_variable("f32"), CType::Float64))
            .expect("symbolic float widening conversion should evaluate");
    let Proposition::CExpressionEvaluates {
        outcome: CExpressionOutcome::Value(CValue::Float64(term)),
        ..
    } = theorem.proposition()
    else {
        panic!("symbolic float widening conversion should produce a double");
    };
    assert!(matches!(
        term,
        Bitvector32Term::PureFunctionApplication { .. }
    ));

    let paths = evaluate_c_expression_paths(
        &state,
        &c_cast(c_variable("f64"), CType::Int32),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("symbolic float-to-integer conversion should retain its guard");
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        paths[0].outcome,
        CExpressionOutcome::Value(CValue::Int32(
            Bitvector32Term::PureFunctionApplication { .. }
        ))
    ));
    assert_eq!(paths[0].obligations.len(), 3);
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
            state: Box::new(state),
            expression: c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn wide_shift_counts_are_checked_before_narrowing() {
    for (count_case, count_value_bits) in [2_u64, 0x1_0000_0002].into_iter().enumerate() {
        for shift_left in [false, true] {
            for left_is_64_bit in [false, true] {
                for unsigned_count in [false, true] {
                    let count_variable = Variable(
                        93_900
                            + count_case as u64 * 8
                            + u64::from(shift_left) * 4
                            + u64::from(left_is_64_bit) * 2
                            + u64::from(unsigned_count),
                    );
                    let count_term = Bitvector32Term::Variable(count_variable);
                    let (count_value, count_type, count_fact) = if unsigned_count {
                        (
                            CValue::UInt64(count_term.clone()),
                            CType::UInt64,
                            ConditionTerm::uint64_equal(
                                count_term.clone(),
                                Bitvector32Term::UInt64Constant(count_value_bits),
                            ),
                        )
                    } else {
                        (
                            CValue::Int64(count_term.clone()),
                            CType::Int64,
                            ConditionTerm::int64_equal(
                                count_term.clone(),
                                Bitvector32Term::Int64Constant(count_value_bits as i64),
                            ),
                        )
                    };
                    let (left_value, left_type) = if left_is_64_bit {
                        (
                            CValue::Int64(Bitvector32Term::Int64Constant(1)),
                            CType::Int64,
                        )
                    } else {
                        (CValue::Int32(Bitvector32Term::Constant(1)), CType::Int32)
                    };
                    let mut state = CState::new()
                        .with_local("left", left_value.clone())
                        .with_local("count", count_value.clone());
                    state.locals.set_typed("left", left_value, left_type);
                    state.locals.set_typed("count", count_value, count_type);

                    let left = c_variable("left");
                    let right = c_variable("count");
                    let expression = if shift_left {
                        c_shift_left(left, right)
                    } else {
                        c_shift_right(left, right)
                    };
                    let assumptions = PureFactContext::new().assume_condition(count_fact, true);
                    let paths = evaluate_c_expression_paths(
                        &state,
                        &expression,
                        &assumptions,
                        &mut ExecutionBudget::for_c_expression(&expression),
                    )
                    .expect("wide shift evaluation should stay within its execution budget");

                    if count_value_bits == 2 {
                        assert!(
                            paths
                                .iter()
                                .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_))),
                            "in-range count unexpectedly lost its value path"
                        );
                        assert!(
                            !paths.iter().any(|path| matches!(
                                path.outcome,
                                CExpressionOutcome::UndefinedBehavior(
                                    CUndefinedBehavior::InvalidShift
                                )
                            )),
                            "in-range count was reported as undefined behavior"
                        );
                    } else {
                        assert!(
                            paths.iter().any(|path| matches!(
                                path.outcome,
                                CExpressionOutcome::UndefinedBehavior(
                                    CUndefinedBehavior::InvalidShift
                                )
                            )),
                            "left_shift={shift_left}, left64={left_is_64_bit}, unsigned_count={unsigned_count}: {paths:?}"
                        );
                        assert!(
                            !paths
                                .iter()
                                .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_))),
                            "an out-of-range 64-bit count must not be accepted via its low word"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn condition_evaluation_certifies_c_truthiness_directly() {
    let state = CState::new();
    let condition = c_less_than(c_int32_literal(1), c_int32_literal(2));
    let evaluation = prove_symbolic_c_condition_evaluation(
        state.clone(),
        condition.clone(),
        PureFactContext::new(),
    );

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state: Box::new(state),
            condition,
            outcome: CConditionOutcome::Value(true),
        }
    );
}

#[test]
fn void_truthiness_is_an_explicit_type_error() {
    let state = CState::new();
    let condition = c_void_value();
    let evaluation = prove_symbolic_c_condition_evaluation(
        state.clone(),
        condition.clone(),
        PureFactContext::new(),
    );

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state: Box::new(state.clone()),
            condition,
            outcome: CConditionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        }
    );

    for expression in [
        c_not(c_void_value()),
        c_and(c_void_value(), c_int32_literal(1)),
        c_or(c_void_value(), c_int32_literal(1)),
    ] {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("invalid void truthiness should retain its runtime-error frontier");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            }
        );
    }
}

#[test]
fn void_local_declaration_is_an_explicit_type_error() {
    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_declare("invalid", CType::Void),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("invalid void declarations should execute to a type error");

    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    );

    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_if(c_void_value(), CStatement::Skip, CStatement::Skip),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("a void condition should execute to a type error");
    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    );
}

#[test]
fn symbolic_condition_evaluation_exposes_both_truthiness_paths() {
    let x = Variable(90);
    let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(x)));
    let condition = c_greater_equal(c_variable("x"), c_int32_literal(0));
    let evaluation =
        prove_symbolic_c_condition_evaluation(state, condition, PureFactContext::new());

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
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("concrete subtraction should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn nonnegative_ordered_subtraction_does_not_overflow() {
    let position = Bitvector32Term::Variable(Variable(24));
    let length = Bitvector32Term::Variable(Variable(25));
    let assumptions = PureFactContext::new()
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
            state: Box::new(state),
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
                state: Box::new(state.clone()),
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
        .with_local("p", CValue::pointer(p))
        .with_local("same", CValue::pointer(same))
        .with_local("next", CValue::pointer(next))
        .with_local("other", CValue::pointer(other));
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
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn pointer_values_preserve_their_exact_c_types_without_changing_address_identity() {
    let address = Pointer {
        block: "same-address".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let int32_pointer = CValue::typed_pointer(address.clone(), CType::Int32Pointer);
    let uint8_pointer = CValue::typed_pointer(address.clone(), CType::UInt8Pointer);

    assert_eq!(int32_pointer.c_type(), CType::Int32Pointer);
    assert_eq!(uint8_pointer.c_type(), CType::UInt8Pointer);
    let CValue::Pointer(int32_pointer) = int32_pointer else {
        unreachable!();
    };
    let CValue::Pointer(uint8_pointer) = uint8_pointer else {
        unreachable!();
    };
    assert_eq!(int32_pointer.pointer(), uint8_pointer.pointer());
}

#[test]
fn address_of_dereference_preserves_the_complete_pointer_without_accessing_storage() {
    let base = Pointer::symbolic(Variable(438_001));
    let address = base.offset_by_bytes(4);
    let object = PointerDesignation::Object {
        root: base.clone(),
        path: vec![PointerDomainSelection::Member("value".into())].into(),
        base,
        element_type: CType::Int32,
        stride: 4,
        count: IntegerTerm::constant_i64(1).into(),
    };
    // This address is one past the described scalar. Forming &*p must retain
    // its descriptor without executing a read or granting access to storage.
    for designation in [
        None,
        Some(PointerDesignation::Unresolved(Variable(438_002))),
        Some(object),
    ] {
        let mut pointer = CPointerValue::new(address.clone(), CType::Int32Pointer)
            .with_pointee_volatile(true)
            .with_pointee_constant(true);
        if let Some(designation) = designation {
            pointer = pointer.with_designation(designation);
        }
        let mut state = CState::new();
        state.locals.set_typed_with_all_qualifiers(
            "p",
            CValue::Pointer(pointer.clone()),
            CType::Int32Pointer,
            false,
            true,
            false,
            true,
        );
        let expression = CExpression::AddressOf(Box::new(CExpression::Load(Box::new(
            CExpression::Variable("p".into()),
        ))));
        let paths = evaluate_c_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("address formation must have one path");
        };
        assert_eq!(
            path.outcome,
            CExpressionOutcome::Value(CValue::Pointer(pointer))
        );
        assert!(path.facts.is_empty());
        assert!(path.obligations.is_empty());
    }
}

#[test]
fn memory_lvalues_retain_pointer_designation_and_independent_access_qualifiers() {
    let pointer = CPointerValue::new(
        Pointer::symbolic(Variable(438_003)),
        CType::Int32PointerPointer,
    )
    .with_pointee_constant(true)
    .with_designation(PointerDesignation::Unresolved(Variable(438_004)));
    let expression = CExpression::TypedLoad {
        pointer: Box::new(CExpression::Value(CValue::Pointer(pointer.clone()))),
        value_type: CType::Int32Pointer,
        volatile: true,
        pointee_constant: true,
        source: Default::default(),
    };
    let state = CState::new();
    let paths = evaluate_c_lvalue_paths(
        &state,
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("typed lvalue formation must have one path");
    };
    let CLValueOutcome::LValue(lvalue) = &path.outcome else {
        panic!("expected memory lvalue");
    };
    assert_eq!(
        lvalue.storage,
        CLValueStorage::Memory {
            pointer: pointer.clone()
        }
    );
    assert!(lvalue.is_volatile());
    assert!(lvalue.is_constant());
    assert!(lvalue.pointee_is_constant());
    assert_eq!(lvalue.pointer(&state).as_ref(), Some(pointer.pointer()));

    let paths = evaluate_c_expression_paths(
        &state,
        &CExpression::AddressOf(Box::new(expression)),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(
        paths[0].outcome,
        CExpressionOutcome::Value(CValue::Pointer(pointer.with_pointee_volatile(true)))
    );
}

#[test]
fn pointer_transformations_preserve_access_qualifiers() {
    let address = Pointer {
        block: "qualified-object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = CValue::typed_pointer(address.clone(), CType::Int32Pointer)
        .with_pointer_pointee_constant(true)
        .with_pointer_pointee_volatile(true);
    let mut state = CState::new().with_memory(CMemory::new().with_block("qualified-object", 8));
    state.locals.set_typed_with_all_qualifiers(
        "p",
        value.clone(),
        CType::Int32Pointer,
        false,
        true,
        false,
        true,
    );
    for (expression, expected_address, expected_type) in [
        (
            c_add(c_variable("p"), c_int32_literal(0)),
            address.clone(),
            CType::Int32Pointer,
        ),
        (
            c_add(c_variable("p"), c_int32_literal(1)),
            address.offset_by_bytes(4),
            CType::Int32Pointer,
        ),
        (
            c_pointer_offset_bytes(c_variable("p"), 4),
            address.offset_by_bytes(4),
            CType::Int32Pointer,
        ),
        (
            c_cast_with_pointee_qualifiers(
                CExpression::Value(value),
                CType::UInt8Pointer,
                true,
                true,
            ),
            address,
            CType::UInt8Pointer,
        ),
    ] {
        let theorem = prove_c_expression_evaluation(state.clone(), expression)
            .expect("qualified pointer transformation should evaluate");
        let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
            panic!("expected expression evaluation");
        };
        let CExpressionOutcome::Value(CValue::Pointer(pointer)) = outcome else {
            panic!("qualified pointer transformation must produce a pointer: {outcome:?}");
        };
        assert_eq!(pointer.pointer(), &expected_address);
        assert_eq!(pointer.c_type(), expected_type);
        assert!(pointer.pointee_constant());
        assert!(pointer.pointee_volatile());
    }
}

#[test]
fn pointer_arithmetic_store_reload_retains_const_and_rejects_implicit_discard() {
    let address = Pointer {
        block: "qualified-object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let slot = Pointer {
        block: "qualified-slot".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = CState::new()
        .with_memory(
            CMemory::new()
                .with_block("qualified-object", 4)
                .with_block("qualified-slot", 8),
        )
        .with_resource_context(own_memory_context(slot.clone(), 0, 2));
    let value = CValue::typed_pointer(address.clone(), CType::Int32Pointer)
        .with_pointer_pointee_constant(true);
    state.locals.set_typed_with_all_qualifiers(
        "p",
        value,
        CType::Int32Pointer,
        false,
        false,
        false,
        true,
    );
    let expression = c_add(c_variable("p"), c_int32_literal(0));
    for destination_constant in [false, true] {
        let statement = c_seq(
            c_qualified_typed_store(
                c_pointer_value(slot.clone()),
                expression.clone(),
                CType::Int32Pointer,
                destination_constant,
                false,
            ),
            c_return(c_typed_load(
                c_pointer_value(slot.clone()),
                CType::Int32Pointer,
            )),
        );
        let theorem = prove_symbolic_c_execution(state.clone(), statement, PureFactContext::new())
            .expect("pointer store should retain the conversion frontier");
        let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
            panic!("expected statement execution");
        };
        if destination_constant {
            assert!(
                matches!(outcome, CStatementOutcome::Return { value: CValue::Pointer(pointer), .. }
                if pointer.pointer() == &address && pointer.pointee_constant())
            );
        } else {
            assert!(matches!(
                outcome,
                CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            ));
        }
    }
}

#[test]
fn explicit_wide_integer_pointer_cast_accepts_only_proven_null_without_origin() {
    let word = Bitvector32Term::Variable(Variable(4242));
    for value in [CValue::UInt64(word.clone()), CValue::Int64(word.clone())] {
        for known_value in [None, Some(0), Some(4)] {
            let mut assumptions = PureFactContext::new();
            if let Some(known) = known_value {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::uint64_equal(
                        word.clone(),
                        Bitvector32Term::UInt64Constant(known),
                    ),
                    true,
                );
            }
            let mut obligations = Vec::new();
            let cast = crate::kernel::eval::cast_c_value_to_type(
                value.clone(),
                CType::UInt8Pointer,
                crate::kernel::eval::IntegerConversion::Modular,
                &mut obligations,
                &assumptions,
            );
            if known_value == Some(0) {
                assert_eq!(
                    cast.unwrap(),
                    CValue::typed_pointer(Pointer::null(), CType::UInt8Pointer),
                );
            } else {
                assert!(matches!(cast, Err(CRuntimeError::PointerConversion(_))));
            }
            // An unknown integer must not acquire a pointer by leaving an
            // unproved null obligation behind.
            assert!(obligations.is_empty());
        }
    }
}

#[test]
fn integer_cast_cannot_erase_a_retained_object_domain() {
    let address = Pointer::symbolic(Variable(4243));
    let domain = PointerDesignation::Object {
        root: address.clone(),
        path: Default::default(),
        base: address.clone(),
        element_type: CType::Int32,
        stride: 4,
        count: IntegerTerm::constant_i64(1).into(),
    };
    let pointer = CPointerValue::new(address, CType::Int32Pointer).with_designation(domain);
    let assumptions = PureFactContext::new();
    let mut obligations = Vec::new();
    for target in [CType::Int64, CType::UInt64] {
        let word = crate::kernel::eval::cast_c_value_to_type(
            CValue::Pointer(pointer.clone()),
            target,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut obligations,
            &assumptions,
        )
        .unwrap();
        let CValue::PointerInteger(carrier) = &word else {
            panic!("an executable pointer cast must retain its full origin")
        };
        assert_eq!(carrier.origin(), &pointer);
        let restored = crate::kernel::eval::cast_c_value_to_type(
            word,
            CType::Int32Pointer,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut obligations,
            &assumptions,
        )
        .unwrap();
        assert_eq!(restored, CValue::Pointer(pointer.clone()));
    }
    let CValue::Pointer(byte_view) = crate::kernel::eval::cast_c_value_to_type(
        CValue::Pointer(pointer.clone()),
        CType::UInt8Pointer,
        crate::kernel::eval::IntegerConversion::Modular,
        &mut obligations,
        &assumptions,
    )
    .unwrap() else {
        panic!("pointer cast must preserve the carrier")
    };
    assert!(pointer.same_designation(&byte_view));
    assert!(obligations.is_empty());
}

#[test]
fn pointer_cast_retags_the_view_but_pointer_type_mismatch_is_not_implicit() {
    let address = Pointer {
        block: "typed-pointer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = CState::new();
    state.locals.set_typed_with_all_qualifiers(
        "int32_p",
        CValue::typed_pointer_with_pointee_constant(address.clone(), CType::Int32Pointer, true),
        CType::Int32Pointer,
        false,
        false,
        false,
        true,
    );
    state.locals.set_typed(
        "uint8_p",
        CValue::pointer(address.clone()),
        CType::UInt8Pointer,
    );

    let cast = c_cast(c_variable("int32_p"), CType::UInt8Pointer);
    let cast_theorem = prove_c_expression_evaluation(state.clone(), cast.clone())
        .expect("an explicit pointer cast should evaluate");
    let Proposition::CExpressionEvaluates {
        outcome: CExpressionOutcome::Value(value),
        ..
    } = cast_theorem.proposition()
    else {
        panic!("explicit pointer cast did not produce a value");
    };
    assert_eq!(value.c_type(), CType::UInt8Pointer);
    let CValue::Pointer(value) = value else {
        unreachable!();
    };
    assert_eq!(value.pointer(), &address);
    assert!(
        value.pointee_constant(),
        "a byte view must retain source const qualification"
    );
    let (spec_value, _) = c_evaluate_spec_expression_at_state(
        &state,
        &SpecExpression::Cast(
            Box::new(SpecExpression::Value(
                CValue::typed_pointer_with_pointee_constant(
                    address.clone(),
                    CType::Int32Pointer,
                    true,
                ),
            )),
            CType::UInt8Pointer,
        ),
        None,
        &PureFactContext::new(),
    )
    .unwrap();
    let CValue::Pointer(spec_pointer) = spec_value else {
        panic!("byte-view spec cast must yield a pointer");
    };
    assert_eq!(spec_pointer.pointer(), &address);
    assert!(spec_pointer.pointee_constant());

    let equality = c_equal(c_variable("int32_p"), c_variable("uint8_p"));
    let equality_theorem = prove_c_expression_evaluation(state, equality.clone())
        .expect("a mismatched pointer comparison should retain its error frontier");
    assert!(matches!(
        equality_theorem.proposition(),
        Proposition::CExpressionEvaluates {
            expression,
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            ..
        } if expression == &equality
    ));
}

#[test]
fn spec_pointer_equality_lowers_to_a_pure_fact() {
    let left = Pointer::symbolic(Variable(22_100));
    let right = Pointer::symbolic(Variable(22_101));
    let equality = ConditionTerm::pointer_equal(left.clone(), right.clone());

    assert_eq!(
        c_value_comparison_proposition(
            &CValue::pointer(left.clone()),
            CComparisonOperator::Equal,
            &CValue::pointer(right.clone()),
        ),
        Some(Proposition::ConditionIs(equality.clone(), true)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::pointer(left.clone()),
            CComparisonOperator::NotEqual,
            &CValue::pointer(right),
        ),
        Some(Proposition::ConditionIs(equality, false)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::pointer(left),
            CComparisonOperator::LessThan,
            &CValue::Int32(Bitvector32Term::Constant(0)),
        ),
        None,
    );
}

#[test]
fn finite_float_context_proves_reflexive_comparisons() {
    let value = Bitvector32Term::Variable(Variable(22_102));
    let finite = ConditionTerm::float64_classification(value.clone(), CFloatClassification::Finite);
    let assumptions = PureFactContext::new().assume_condition(finite, true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::float64_compare(
            value.clone(),
            value.clone(),
            CComparisonOperator::Equal,
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::float64_compare(
            value.clone(),
            value,
            CComparisonOperator::NotEqual,
        )),
        Some(false)
    );
}

#[test]
fn spec_pointer_order_lowers_same_block_offsets() {
    let left = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::pointer(left),
            CComparisonOperator::LessThan,
            &CValue::pointer(right),
        ),
        Some(Proposition::ConditionIs(
            ConditionTerm::Constant(true),
            true,
        )),
    );
}

#[test]
fn symbolic_pointer_truthiness_keeps_null_and_nonnull_paths() {
    let paths = c_truthiness_paths(
        CValue::pointer(Pointer::symbolic(Variable(22_000))),
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
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
        .with_local("nullp", CValue::pointer(null))
        .with_local("p", CValue::pointer(nonnull));
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
                state: Box::new(state.clone()),
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
            state: Box::new(state),
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
        .with_local("nullp", CValue::pointer(null))
        .with_local("p", CValue::pointer(p))
        .with_local("same", CValue::pointer(same))
        .with_local("next", CValue::pointer(next));
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
                state: Box::new(state.clone()),
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
    let invalid_load = c_typed_load(c_pointer_value(invalid_pointer), CType::Int32);
    let state = CState::new().with_resource_context(view_memory_context(
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
                state: Box::new(state.clone()),
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
fn void_pointer_operations_distinguish_dereferences_from_gnu_byte_arithmetic() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    // The generic pointer helper now carries an int32 pointee type. Use
    // void* to exercise operations with no available pointee type.
    let pointer_value = || c_typed_pointer_value(pointer.clone(), CType::VoidPointer);
    let expressions = [
        c_load(pointer_value()),
        c_index(pointer_value(), c_int32_literal(1)),
    ];

    for expression in expressions {
        let theorem = prove_c_expression_evaluation(CState::new(), expression.clone())
            .expect("a void-pointer dereference should produce an explicit model error");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(CState::new()),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType,),
            }
        );
    }
    // GNU C permits formation by byte arithmetic, without permitting a
    // dereference through void*. Check both operand orders independently.
    for expression in [
        c_add(pointer_value(), c_int32_literal(1)),
        c_add(c_int32_literal(1), pointer_value()),
    ] {
        let theorem = prove_c_expression_evaluation(CState::new(), expression.clone())
            .expect("GNU C void-pointer byte arithmetic");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(CState::new()),
                expression,
                outcome: CExpressionOutcome::Value(CValue::typed_pointer(
                    pointer.offset_by_bytes(1),
                    CType::VoidPointer,
                )),
            }
        );
    }
}

#[test]
fn function_pointer_operations_report_indeterminate_pointee_type() {
    let pointer = Pointer::function("callback");
    let function_type = CType::FunctionPointer(CType::function_pointer_signature(
        CType::Int32,
        &[CType::Int32],
    ));
    let mut state = CState::new();
    state
        .locals
        .set_typed("callback", CValue::pointer(pointer), function_type);
    let expressions = [
        c_load(c_variable("callback")),
        c_add(c_variable("callback"), c_int32_literal(1)),
        c_pointer_offset_bytes(c_variable("callback"), 4),
    ];

    for expression in expressions {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("a function-pointer object operation should produce a model error");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
            }
        );
    }
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
        .with_local("p", CValue::pointer(left))
        .with_local("q", CValue::pointer(right));
    let statement = c_if(
        c_equal(c_variable("p"), c_variable("q")),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

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
            state: Box::new(state.clone()),
            statement: Box::new(statement.clone()),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state: Box::new(state.clone()),
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
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: Box::new(state),
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
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("nonzero int32 condition should take then branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state: Box::new(state),
            },
        }
    );

    let state = CState::new();
    let statement = c_if(
        c_int32_literal(0),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("zero int32 condition should take else branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn assignment_and_sequence_update_native_state() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_seq(c_assign("x", c_int32_literal(2)), c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(2));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(2),
                state: Box::new(final_state),
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources.clone());
    let statement = c_seq(
        c_typed_store(
            c_pointer_value(pointer.clone()),
            c_int32_literal(9),
            CType::Int32,
        ),
        c_return(c_typed_load(c_pointer_value(pointer.clone()), CType::Int32)),
    );
    let final_state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("store then load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn viewed_memory_resource_permits_symbolic_external_load_from_incomplete_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_resource_context(view_memory_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                // The symbolic read is canonical at creation: its load
                // variable, which names this load.
                value: int32(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Bits32,
                ))),
                state: Box::new(state),
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let statement = c_seq(
        c_typed_store(
            c_pointer_value(pointer.clone()),
            c_int32_literal(9),
            CType::Int32,
        ),
        c_return(c_typed_load(c_pointer_value(pointer.clone()), CType::Int32)),
    );
    let final_state = CState::new()
        .with_memory(memory.store(pointer, int32(9)))
        .with_resource_context(resources);
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("in-range block store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: Box::new(final_state),
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
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(memory.clone())
        .with_resource_context(view_memory_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("in-range missing load should produce symbolic value");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Bits32
                ))),
                state: Box::new(state),
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
    let resources = view_memory_context(base.clone(), 1, 2);
    let state = CState::new()
        .with_local("p", CValue::pointer(base.clone()))
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("pointer arithmetic load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(23),
                state: Box::new(
                    CState::new()
                        .with_local(
                            "p",
                            CValue::pointer(Pointer {
                                block: "block".into(),
                                offset: PointerOffsetTerm::Constant(0),
                            }),
                        )
                        .with_memory(
                            CMemory::new()
                                .with_block("block", 16)
                                .store(second, int32(23),),
                        )
                        .with_resource_context(resources)
                ),
            },
        }
    );
}

#[test]
fn pointer_addition_rejects_an_int32_index_beyond_the_object() {
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(base))
        .with_memory(CMemory::new().with_block("array", 8));
    let expression = c_add(c_variable("p"), c_int32_literal(3));

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete out-of-object pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn uint64_pointer_index_bounds_use_the_full_value() {
    let index = Bitvector32Term::Variable(Variable(93_815));
    let offset = PointerOffsetTerm::Int64Scaled {
        value: Box::new(index.clone()),
        byte_width: 1,
        unsigned: true,
    };
    assert_eq!(byte_offset_from_pointer_offset(&offset), None);

    let base = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = CState::new()
        .with_local("array", CValue::pointer(base.clone()))
        .with_local("index", CValue::UInt64(index.clone()))
        .with_memory(CMemory::new().with_block("bytes", 8));
    state
        .locals
        .set_typed("array", CValue::pointer(base), CType::UInt8Pointer);
    state
        .locals
        .set_typed("index", CValue::UInt64(index.clone()), CType::UInt64);
    let expression = c_add(c_variable("array"), c_variable("index"));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(index, Bitvector32Term::UInt64Constant(0x1_0000_0003)),
        true,
    );
    let mut budget = ExecutionBudget::for_c_expression(&expression);
    let paths = evaluate_c_expression_paths(&state, &expression, &assumptions, &mut budget)
        .expect("wide pointer arithmetic should stay within its execution budget");

    assert!(paths.iter().any(|path| matches!(
        path.outcome,
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic)
    )));
    assert!(
        !paths
            .iter()
            .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
    );
}

#[test]
fn pointer_index_sum_overflow_is_pointer_undefined_behavior() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new().with_local("p", CValue::pointer(base));
    let expression = c_add(
        c_add(c_variable("p"), c_int32_literal(i32::MAX as u32)),
        c_int32_literal(1),
    );

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete cumulative pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn pointer_index_sum_overflow_is_undefined_for_a_uint8_pointer() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = CState::new().with_local("p", CValue::pointer(base.clone()));
    state
        .locals
        .set_typed("p", CValue::pointer(base), CType::UInt8Pointer);
    let expression = c_add(
        c_add(c_variable("p"), c_int32_literal(i32::MAX as u32)),
        c_int32_literal(1),
    );

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete uint8 cumulative pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic,),
        }
    );
}

#[test]
fn pointer_addition_allows_the_one_past_int32_element() {
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(base.clone()))
        .with_memory(CMemory::new().with_block("array", 8));
    let expression = c_add(c_variable("p"), c_int32_literal(2));
    let result = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("one-past pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::Value(CValue::pointer(result)),
        }
    );
}

#[test]
fn pointer_addition_rejects_a_uint8_index_beyond_the_object() {
    let base = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = CState::new()
        .with_local("p", CValue::pointer(base.clone()))
        .with_memory(CMemory::new().with_block("bytes", 4));
    state
        .locals
        .set_typed("p", CValue::pointer(base), CType::UInt8Pointer);
    let expression = c_add(c_variable("p"), c_int32_literal(5));

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete uint8 out-of-object pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic,),
        }
    );
}

#[test]
fn byte_offset_rejects_a_pointer_beyond_the_object() {
    let base = Pointer {
        block: "object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(base))
        .with_memory(CMemory::new().with_block("object", 4));
    let expression = c_pointer_offset_bytes(c_variable("p"), 5);

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete out-of-object byte offset should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic,),
        }
    );
}

#[test]
fn pointer_relational_comparison_orders_same_block_elements() {
    let first = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let state = CState::new()
        .with_local("first", CValue::pointer(first))
        .with_local("second", CValue::pointer(second));
    let examples = [
        (c_less_than(c_variable("first"), c_variable("second")), 1),
        (c_less_equal(c_variable("first"), c_variable("second")), 1),
        (c_greater_than(c_variable("second"), c_variable("first")), 1),
        (
            c_greater_equal(c_variable("second"), c_variable("first")),
            1,
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("same-block pointer comparison should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::Value(int32(expected)),
            }
        );
    }
}

#[test]
fn pointer_subtraction_returns_same_block_element_distance() {
    let start = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let end = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let state = CState::new()
        .with_local("start", CValue::pointer(start))
        .with_local("end", CValue::pointer(end));
    let expression = c_subtract(c_variable("end"), c_variable("start"));

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("same-block pointer subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::Value(int32(2)),
        }
    );
}

#[test]
fn uint8_pointer_subtraction_returns_byte_distance() {
    let start = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let end = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(3),
    };
    let mut state = CState::new()
        .with_local("start", CValue::pointer(start.clone()))
        .with_local("end", CValue::pointer(end.clone()));
    state
        .locals
        .set_typed("start", CValue::pointer(start), CType::UInt8Pointer);
    state
        .locals
        .set_typed("end", CValue::pointer(end), CType::UInt8Pointer);
    let expression = c_subtract(c_variable("end"), c_variable("start"));

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("same-block uint8 pointer subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::Value(int32(3)),
        }
    );
}

#[test]
fn pointer_subtraction_by_one_steps_back_one_element() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer))
        .with_memory(CMemory::new().with_block("array", 12));
    let expression = c_subtract(c_variable("p"), c_int32_literal(1));
    let result = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("pointer subtraction by one should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::Value(CValue::pointer(result)),
        }
    );
}

#[test]
fn pointer_comparison_rejects_different_blocks_as_undefined_behavior() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("left", CValue::pointer(left))
        .with_local("right", CValue::pointer(right));
    let expression = c_less_than(c_variable("left"), c_variable("right"));

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("cross-block pointer comparison should evaluate to UB");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn pointer_subtraction_rejects_different_blocks_as_undefined_behavior() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("left", CValue::pointer(left))
        .with_local("right", CValue::pointer(right));
    let expression = c_subtract(c_variable("left"), c_variable("right"));

    let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
        .expect("cross-block pointer subtraction should evaluate to UB");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn pointer_order_and_subtraction_require_external_parameters_to_share_an_object() {
    let external = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let left = external(31_000);
    let right = external(31_001);
    let state = CState::new()
        .with_local("left", CValue::pointer(left))
        .with_local("right", CValue::pointer(right));

    for expression in [
        c_less_than(c_variable("left"), c_variable("right")),
        c_less_equal(c_variable("left"), c_variable("right")),
        c_greater_than(c_variable("left"), c_variable("right")),
        c_greater_equal(c_variable("left"), c_variable("right")),
        c_subtract(c_variable("left"), c_variable("right")),
    ] {
        let mut budget = ExecutionBudget::for_c_expression(&expression);
        let paths =
            evaluate_c_expression_paths(&state, &expression, &PureFactContext::new(), &mut budget)
                .expect("external pointer operation should stay within its execution budget");
        assert!(
            paths
                .iter()
                .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
        assert!(paths.iter().any(|path| matches!(
            path.outcome,
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic)
        )));
    }

    for expression in [
        c_equal(c_variable("left"), c_variable("right")),
        c_not_equal(c_variable("left"), c_variable("right")),
    ] {
        let mut budget = ExecutionBudget::for_c_expression(&expression);
        let paths =
            evaluate_c_expression_paths(&state, &expression, &PureFactContext::new(), &mut budget)
                .expect("external pointer equality should stay within its execution budget");
        assert!(!paths.is_empty());
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
    }
}

#[test]
fn null_pointers_have_no_object_provenance_for_ordering_or_subtraction() {
    let null = Pointer::null();
    assert!(disprove_builtin_prop(&pointer_same_object_proposition(
        &null, &null
    )));

    let state = CState::new()
        .with_local("left", CValue::pointer(null.clone()))
        .with_local("right", CValue::pointer(null));
    for expression in [
        c_less_than(c_variable("left"), c_variable("right")),
        c_less_equal(c_variable("left"), c_variable("right")),
        c_greater_than(c_variable("left"), c_variable("right")),
        c_greater_equal(c_variable("left"), c_variable("right")),
        c_subtract(c_variable("left"), c_variable("right")),
    ] {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("a null pointer operation should evaluate to undefined behavior");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: CExpressionOutcome::UndefinedBehavior(
                    CUndefinedBehavior::PointerArithmetic,
                ),
            }
        );
    }

    for expression in [
        c_equal(c_variable("left"), c_variable("right")),
        c_not_equal(c_variable("left"), c_variable("right")),
    ] {
        let mut budget = ExecutionBudget::for_c_expression(&expression);
        let paths =
            evaluate_c_expression_paths(&state, &expression, &PureFactContext::new(), &mut budget)
                .expect("null pointer equality should stay within its execution budget");
        assert!(!paths.is_empty());
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
    }
}

#[test]
fn an_external_pointer_does_not_share_an_object_with_itself_until_nonnull() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(31_050))),
            byte_width: 4,
        },
    };
    let state = CState::new().with_local("pointer", CValue::pointer(pointer));

    for expression in [
        c_less_than(c_variable("pointer"), c_variable("pointer")),
        c_less_equal(c_variable("pointer"), c_variable("pointer")),
        c_greater_than(c_variable("pointer"), c_variable("pointer")),
        c_greater_equal(c_variable("pointer"), c_variable("pointer")),
        c_subtract(c_variable("pointer"), c_variable("pointer")),
    ] {
        let mut budget = ExecutionBudget::for_c_expression(&expression);
        let paths =
            evaluate_c_expression_paths(&state, &expression, &PureFactContext::new(), &mut budget)
                .expect("external pointer operation should stay within its execution budget");
        assert!(
            paths
                .iter()
                .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
        assert!(paths.iter().any(|path| matches!(
            path.outcome,
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic)
        )));
    }
}

#[test]
fn nonempty_loadability_establishes_external_pointer_object_provenance() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(31_060))),
            byte_width: 4,
        },
    };
    let state = CState::new().with_local("pointer", CValue::pointer(pointer.clone()));
    let loadable = |bytes| Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(bytes),
        wide: false,
    };

    let nonempty = PureFactContext::new().assume_proposition(loadable(4));
    for expression in [
        c_less_equal(c_variable("pointer"), c_variable("pointer")),
        c_subtract(c_variable("pointer"), c_variable("pointer")),
    ] {
        let mut budget = ExecutionBudget::for_c_expression(&expression);
        let paths = evaluate_c_expression_paths(&state, &expression, &nonempty, &mut budget)
            .expect("viewable pointer operation should stay within its execution budget");
        assert!(!paths.is_empty());
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
    }

    let empty = PureFactContext::new().assume_proposition(loadable(0));
    let expression = c_less_equal(c_variable("pointer"), c_variable("pointer"));
    let mut budget = ExecutionBudget::for_c_expression(&expression);
    let paths = evaluate_c_expression_paths(&state, &expression, &empty, &mut budget)
        .expect("empty-viewable pointer operation should stay within its execution budget");
    assert!(paths.iter().any(|path| matches!(
        path.outcome,
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic)
    )));
}

#[test]
fn loadable_object_provenance_lookup_ignores_unrelated_external_pointers() {
    let external = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let target = external(31_070);
    let loadable = |base| Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base,
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };

    let samples = [4usize, 16, 64, 256]
        .into_iter()
        .map(|size| {
            let mut assumptions =
                PureFactContext::new().assume_proposition(loadable(target.clone()));
            for index in 0..size {
                assumptions =
                    assumptions.assume_proposition(loadable(external(32_000 + index as u64)));
            }
            let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .memory_loadable_candidates_for_object(&target)
                    .count()
            });
            assert_eq!(count, 1);
            work
        })
        .collect::<Vec<_>>();
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "object-provenance lookup scanned unrelated external pointers: {samples:?}"
    );
}

#[test]
fn pointer_arithmetic_preserves_external_object_identity() {
    let left = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(31_100))),
            byte_width: 4,
        },
    };
    let right = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(31_101))),
            byte_width: 4,
        },
    };
    let derived_left = left.offset_by_int32_elements(Bitvector32Term::Variable(Variable(31_102)));
    let derived_right = right.offset_by_int32_elements(Bitvector32Term::Constant(1));

    assert_eq!(
        pointer_object_identity_condition(&derived_left, &derived_right),
        pointer_object_identity_condition(&left, &right)
    );

    let raw_address_equality = pointer_equality_condition(left.clone(), right.clone());
    let equal_addresses = PureFactContext::new().assume_condition(raw_address_equality, true);
    assert_eq!(
        equal_addresses.decide(&pointer_object_identity_condition(&left, &right)),
        None,
        "address equality must not imply same-object provenance"
    );
}

#[test]
fn viewed_memory_resource_permits_pointer_addition_load_beyond_memory_block() {
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
        .with_local("p", CValue::pointer(base.clone()))
        .with_memory(memory.clone())
        .with_resource_context(view_memory_context(base, 1, 2));
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(derived),
                    crate::kernel::LoadKind::Bits32,
                ))),
                state: Box::new(state),
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
    let resources = own_memory_context(base.clone(), 0, 3);
    let state = CState::new()
        .with_local("p", CValue::pointer(base.clone()))
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
            CValue::pointer(Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
        .with_local("i", int32(3))
        .with_memory(final_memory)
        .with_resource_context(resources);
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(3),
                state: Box::new(final_state),
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
        .with_local("p", CValue::pointer(base.clone()))
        .with_local("i", int32(i_bits.clone()))
        .with_memory(memory.clone())
        .with_resource_context(own_memory_context(base.clone(), 0, n_bits.clone()));
    let statement = c_store(c_add(c_variable("p"), c_variable("i")), c_int32_literal(7));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::Multiply(
                Box::new(n_bits.clone()),
                Box::new(Bitvector32Term::Constant(4)),
            ),
            wide: false,
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
fn signed_order_solver_knows_int32_universal_bounds() {
    let x = Bitvector32Term::Variable(Variable(71));
    let int_min = Bitvector32Term::Constant(i32::MIN as u32);
    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
    let assumptions = PureFactContext::new();

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
fn strict_positive_bound_rules_out_decrement_overflow() {
    let value = Bitvector32Term::Variable(Variable(72_001));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(
            value,
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
}

#[test]
fn nonnegative_bound_rules_out_decrement_overflow() {
    let value = Bitvector32Term::Variable(Variable(72_002));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(
            value,
            Bitvector32Term::Constant(1),
        )),
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
    let lower_only = PureFactContext::new().assume_condition(
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
fn nonnegative_successor_requires_no_overflow_evidence() {
    let x = Bitvector32Term::Variable(Variable(74_001));
    let successor = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            successor.clone(),
            Bitvector32Term::Constant(0),
        )),
        None,
    );
    assert!(
        assumptions
            .derive_simp_proposition(&Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(successor, Bitvector32Term::Constant(0),),
                true,
            ))
            .is_none()
    );
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
    let assumptions = PureFactContext::new()
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
        4,
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
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(length, capacity), true);
    // Publish the symbolic supplier at construction, before containment queries.
    let resources =
        ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(available);

    assert!(resources.satisfies_fact(&required, &assumptions));
    assert!(resources.without_fact(&required, &assumptions).is_some());
}

#[test]
fn addition_cancels_a_negated_pointer_base() {
    let base = Bitvector32Term::Variable(Variable(90));
    let index = Bitvector32Term::Variable(Variable(91));
    let negative_base = Bitvector32Term::subtract(Bitvector32Term::Constant(0), base.clone());

    assert_eq!(
        Bitvector32Term::add(negative_base, Bitvector32Term::add(base, index.clone()),),
        index
    );
}

#[test]
fn negative_equality_fact_decides_equality_false() {
    let x = Bitvector32Term::Variable(Variable(79));
    let assumptions = PureFactContext::new().assume_condition(
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
    let assumptions = PureFactContext::new()
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
    let assumptions = PureFactContext::new()
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
    let assumptions = PureFactContext::new()
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
    let assumptions = PureFactContext::new()
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
    let assumptions = PureFactContext::new()
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
    let assumptions = PureFactContext::new()
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
fn excluded_range_endpoints_force_the_remaining_value() {
    // `0 <= k < 4` with `k != 0`, `k != 1` and `k != 3` leaves only `k == 2`;
    // without the exclusion at either end the value stays undecided.
    let k = Bitvector32Term::Variable(Variable(87));
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(4)),
            true,
        );
    let exclude = |assumptions: PureFactContext, value: u32| {
        assumptions.assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(value)),
            false,
        )
    };
    let is_two = ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(2));
    let all = exclude(exclude(exclude(bounded.clone(), 0), 1), 3);
    assert_eq!(all.decide(&is_two), Some(true));
    let low_only = exclude(exclude(bounded.clone(), 0), 1);
    assert_eq!(low_only.decide(&is_two), None);
    let high_only = exclude(exclude(bounded, 1), 3);
    assert_eq!(high_only.decide(&is_two), None);
}

#[test]
fn a_signed_interval_moves_past_excluded_endpoints() {
    let k = Bitvector32Term::Variable(Variable(88));
    let assumptions = [1, 2, 3, 5].into_iter().fold(
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(4)),
                true,
            ),
        |assumptions, value| {
            assumptions.assume_condition(
                ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(value)),
                false,
            )
        },
    );
    assert_eq!(assumptions.signed_interval(&k), Some((0, 3)));
    // `k != 5` lies outside the range and moves nothing.
    assert_eq!(
        assumptions.signed_interval_past_exclusions(&k),
        Some((0, 0))
    );
}

#[test]
fn singleton_integer_range_forces_equality() {
    let k = Bitvector32Term::Variable(Variable(86));
    let assumptions = PureFactContext::new()
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
fn signed_byte_narrowing_checks_each_bound_and_unsigned_inputs() {
    use crate::kernel::eval::IntegerConversion;
    let convert = |value: CValue,
                   conversion,
                   obligations: &mut Vec<ProofObligation>,
                   assumptions: &PureFactContext| {
        crate::kernel::eval::coerce_c_value_to_type_as(
            value,
            CType::Int8,
            conversion,
            obligations,
            assumptions,
        )
    };
    for (input, valid) in [
        (int32((-129i32) as u32), false),
        (int32((-128i32) as u32), true),
        (int32(127), true),
        (int32(128), false),
        (int16((-129i32) as u32), false),
        (int16((-128i32) as u32), true),
        (uint8(127), true),
        (uint8(128), false),
        (uint8(255), false),
    ] {
        let mut obligations = Vec::new();
        // C's conversion is the low byte, read as signed, owing nothing.
        let word = match &input {
            CValue::Int32(Bitvector32Term::Constant(word))
            | CValue::Int16(Bitvector32Term::Constant(word))
            | CValue::UInt8(Bitvector32Term::Constant(word)) => *word,
            other => panic!("{other:?}"),
        };
        assert_eq!(
            convert(
                input.clone(),
                IntegerConversion::Modular,
                &mut obligations,
                &PureFactContext::new()
            ),
            Some(int8(i32::from(word as u8 as i8) as u32)),
            "{input:?}"
        );
        assert!(obligations.is_empty());
        let result = convert(
            input.clone(),
            IntegerConversion::Checked,
            &mut obligations,
            &PureFactContext::new(),
        );
        assert_eq!(result.unwrap().c_type(), CType::Int8, "{input:?}");
        assert_eq!(obligations.is_empty(), valid, "{input:?}");
        for obligation in &obligations {
            let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
                panic!("narrowing owes an explicit range comparison");
            };
            assert_eq!(
                PureFactContext::decide_intrinsically(condition),
                Some(false)
            );
            assert!(obligation.context().unwrap().starts_with("int8 narrowing"));
        }
    }
    let value = Bitvector32Term::Variable(Variable(815));
    let bounds = [
        ConditionTerm::signed_greater_equal(
            value.clone(),
            Bitvector32Term::Constant((-128i32) as u32),
        ),
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(127)),
    ];
    for mask in 0u32..4 {
        let mut assumptions = PureFactContext::new();
        for (index, bound) in bounds.iter().enumerate() {
            if mask & (1 << index) != 0 {
                assumptions = assumptions.assume_condition(bound.clone(), true);
            }
        }
        let mut obligations = Vec::new();
        let result = convert(
            int32(value.clone()),
            IntegerConversion::Checked,
            &mut obligations,
            &assumptions,
        );
        assert_eq!(result, Some(int8(value.clone())));
        assert_eq!(obligations.len(), 2 - mask.count_ones() as usize);
        // C's conversion owes nothing, and its term is the typed conversion
        // node whatever the context knows; the identity inside the range is
        // reasoning (`narrowed_cast_identity`), not a choice made here.
        let mut obligations = Vec::new();
        let modular = convert(
            int32(value.clone()),
            IntegerConversion::Modular,
            &mut obligations,
            &assumptions,
        );
        assert!(obligations.is_empty());
        assert_eq!(
            modular,
            Some(int8(Bitvector32Term::machine_integer_cast(
                crate::kernel::MachineIntegerType::Int32,
                crate::kernel::MachineIntegerType::Int8,
                value.clone(),
            )))
        );
    }
}

#[test]
fn signed_byte_arithmetic_promotes_with_range_facts() {
    let value = CExpression::Value(int8(Bitvector32Term::Variable(Variable(817))));
    let expression = CExpression::Subtract(
        Box::new(CExpression::Multiply(
            Box::new(value),
            Box::new(c_int32_literal(2)),
        )),
        Box::new(c_int32_literal(1)),
    );
    let paths = evaluate_c_expression_paths(
        &CState::new(),
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(
        matches!(
            paths[0].outcome,
            CExpressionOutcome::Value(CValue::Int32(_))
        ),
        "{paths:?}"
    );
}

#[test]
fn exact_signed_constant_bounds_preserve_frozen_load_identity() {
    let pointer = Pointer {
        block: "bounded".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("bounded", 8);
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(load.clone(), Bitvector32Term::Constant(2)),
        true,
    );
    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_greater_than(
            load.clone(),
            Bitvector32Term::Constant(1)
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_than(
            load,
            Bitvector32Term::Constant(1)
        )),
        Some(true)
    );
    let changed = memory
        .clone()
        .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(0)));
    let changed_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(changed),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let other_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(Pointer {
            block: pointer.block,
            offset: PointerOffsetTerm::Constant(4),
        }),
        crate::kernel::LoadKind::Bits32,
    );
    for unrelated in [changed_load, other_load] {
        assert_ne!(
            assumptions.decide_condition_for_simp(&ConditionTerm::signed_greater_than(
                unrelated,
                Bitvector32Term::Constant(1)
            )),
            Some(true)
        );
    }
}

#[test]
fn exact_signed_constant_bounds_check_signed_endpoints() {
    let value = Bitvector32Term::Variable(Variable(87_900));
    let empty = PureFactContext::new();
    for (bound, greater, expected) in [(i32::MAX, true, false), (i32::MIN, false, false)] {
        let condition = if greater {
            ConditionTerm::signed_greater_than(
                value.clone(),
                Bitvector32Term::Constant(bound as u32),
            )
        } else {
            ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(bound as u32))
        };
        assert_eq!(empty.decide_condition_for_simp(&condition), Some(expected));
    }
    let at_max = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(
            value.clone(),
            Bitvector32Term::Constant(i32::MAX as u32),
        ),
        true,
    );
    assert_eq!(
        at_max.decide_condition_for_simp(&ConditionTerm::signed_greater_than(
            value.clone(),
            Bitvector32Term::Constant((i32::MAX - 1) as u32)
        )),
        Some(true)
    );
    let at_min = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(i32::MIN as u32)),
        true,
    );
    assert_eq!(
        at_min.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            value,
            Bitvector32Term::Constant((i32::MIN + 1) as u32)
        )),
        Some(true)
    );
}

#[test]
fn exact_signed_constant_bound_lookup_ignores_unrelated_facts() {
    let value = Bitvector32Term::Variable(Variable(87_901));
    let query = ConditionTerm::signed_greater_than(value.clone(), Bitvector32Term::Constant(1));
    let mut samples = Vec::new();
    for size in [64, 256, 1024] {
        let mut assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(2)),
            true,
        );
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Variable(Variable(90_000 + index)),
                    Bitvector32Term::Constant(2),
                ),
                true,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.decide_condition_for_simp(&query)
        });
        assert_eq!(result, Some(true));
        samples.push(work);
    }
    assert!(
        samples[2] <= samples[0].saturating_mul(2) + 10,
        "{samples:?}"
    );
}

#[test]
fn exact_signed_mirror_normalization_checks_snapshot_address_and_selected_premise() {
    let pointer = Pointer {
        block: "mirror".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("mirror", 8);
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), load.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(load, Bitvector32Term::Constant(1)),
        true,
    );
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            std::slice::from_ref(&premise),
            &facts
        )
        .is_ok()
    );
    let changed = memory
        .clone()
        .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(0)));
    for (snapshot, address) in [
        (changed, pointer.clone()),
        (
            memory,
            Pointer {
                block: pointer.block,
                offset: PointerOffsetTerm::Constant(4),
            },
        ),
    ] {
        let unrelated = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(snapshot),
            Box::new(address),
            crate::kernel::LoadKind::Bits32,
        );
        let bad = Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(unrelated, Bitvector32Term::Constant(1)),
            true,
        );
        assert!(
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &bad,
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
    }
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            &[premise],
            &crate::kernel::proof::ProofFacts::from_ordered(&[])
        )
        .is_err()
    );
}

#[test]
fn exact_signed_mirror_normalization_ignores_unrelated_facts() {
    let value = Bitvector32Term::Variable(Variable(87_910));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(value, Bitvector32Term::Constant(1)),
        true,
    );
    let mut samples = Vec::new();
    for size in [64, 256, 1024] {
        let mut premises = vec![premise.clone()];
        for index in 0..size {
            premises.push(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Variable(Variable(91_000 + index)),
                    Bitvector32Term::Constant(2),
                ),
                true,
            ));
        }
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                std::slice::from_ref(&premise),
                &facts,
            )
        });
        assert!(result.is_ok());
        samples.push(work);
    }
    assert!(
        samples[2] <= samples[0].saturating_mul(2) + 10,
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn resource_object_provenance_does_not_scan_same_raw_block() {
    let pointer = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(895_000 + id)),
    };
    let target = pointer(0);
    let expression = c_less_equal(c_variable("pointer"), c_variable("pointer"));
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let assumptions = PureFactContext::new();
        let mut resources = ResourceContext::new_with_equalities(&assumptions);
        for id in 1..=size {
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(pointer(id), 0u32.into(), 4u32.into(), 1),
            ));
        }
        resources = resources.unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1),
        ));
        let state = CState::new()
            .with_local("pointer", CValue::pointer(target.clone()))
            .with_resource_context(resources);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut budget = ExecutionBudget::for_c_expression(&expression);
            evaluate_c_expression_paths(&state, &expression, &assumptions, &mut budget).unwrap()
        });
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] + 2000,
        "provenance scanned the raw block: {samples:?}"
    );
}

#[test]
fn uint64_bit_reinterpretation_has_a_distinct_checked_cast_boundary() {
    let assert_type_mismatch = |expression| {
        let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
        assert!(matches!(
            theorem.proposition(),
            Proposition::CExpressionEvaluates {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                ..
            }
        ));
    };
    for bits in [0u64, 1, i64::MAX as u64, 1u64 << 63, u64::MAX] {
        let expression = c_uint64_bits_to_int64(c_uint64_literal(bits));
        let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
        let Proposition::CExpressionEvaluates {
            outcome: CExpressionOutcome::Value(CValue::Int64(value)),
            ..
        } = theorem.proposition()
        else {
            panic!("expected signed bits");
        };
        assert_eq!(value.int64_as_const(), Some(bits as i64));
        // Bit reinterpretation accepts every bit pattern. Ordinary conversion
        // preserves the value only within the signed destination's range.
        let ordinary = c_cast(c_uint64_literal(bits), CType::Int64);
        if bits <= i64::MAX as u64 {
            let theorem = prove_c_expression_evaluation(CState::new(), ordinary).unwrap();
            let Proposition::CExpressionEvaluates {
                outcome: CExpressionOutcome::Value(CValue::Int64(value)),
                ..
            } = theorem.proposition()
            else {
                panic!("representable ordinary cast must preserve its value");
            };
            assert_eq!(value.int64_as_const(), Some(bits as i64));
        } else {
            assert!(prove_c_expression_evaluation(CState::new(), ordinary).is_none());
        }
    }
    assert_type_mismatch(c_uint64_bits_to_int64(c_int32_literal(1)));
    let mut malformed = c_uint64_bits_to_int64(c_uint64_literal(1));
    let CExpression::Cast { target_type, .. } = &mut malformed else {
        unreachable!()
    };
    *target_type = CType::UInt64;
    assert_type_mismatch(malformed);
}

#[test]
fn reinterpreted_unsigned_arithmetic_keeps_signed_operators_and_definedness() {
    let source = Bitvector32Term::uint64_subtract(
        Bitvector32Term::Variable(Variable(139_001)),
        Bitvector32Term::UInt64Constant(1),
    );
    let converted = Bitvector32Term::int64_from_uint64_bits(source.clone());
    assert_eq!(converted, source); // Preserve the symbolic 64-bit expression.
    let wrapped = Bitvector32Term::UInt64Add(
        Box::new(Bitvector32Term::UInt64Constant(u64::MAX)),
        Box::new(Bitvector32Term::UInt64Constant(1)),
    );
    assert_eq!(wrapped.int64_as_const(), Some(0));
    let high = Bitvector32Term::UInt64Constant(1u64 << 63);
    assert_eq!(
        Bitvector32Term::int64_divide(high, Bitvector32Term::Int64Constant(-1)).int64_as_const(),
        None
    );
    assert_eq!(
        Bitvector32Term::int64_divide(
            Bitvector32Term::Int64Constant(1),
            Bitvector32Term::Int64Constant(0)
        )
        .int64_as_const(),
        None
    );
}

#[test]
fn modulo_casts_are_explicit_integer_boundaries_and_preserve_operand_definedness() {
    let outcome = |expression| {
        let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
        let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
            panic!("expected evaluation");
        };
        outcome.clone()
    };
    for target in [
        CType::Int8,
        CType::Int16,
        CType::Int32,
        CType::Int64,
        CType::UInt8,
        CType::UInt16,
        CType::UInt32,
        CType::UInt64,
    ] {
        for flag in [false, true] {
            let actual = outcome(c_integer_cast_modulo(
                CExpression::Value(CValue::Bool(Bitvector32Term::Constant(u32::from(flag)))),
                target,
            ));
            let ty = MachineIntegerType::from_c_type(target).unwrap();
            let expected = ty
                .constant_value(
                    MachineIntegerConstant::from_unsigned(ty.format(), u128::from(flag)).unwrap(),
                )
                .unwrap();
            assert_eq!(actual, CExpressionOutcome::Value(expected));
        }
    }
    for expression in [
        c_integer_cast_modulo(c_int32_literal(1), CType::Bool),
        c_integer_cast_modulo(c_int32_literal(1), CType::Float64),
        c_integer_cast_modulo(c_int32_literal(1), CType::Int32Pointer),
        c_integer_cast_modulo(
            CExpression::Value(CValue::Float32(Bitvector32Term::Constant(0))),
            CType::Int32,
        ),
        c_integer_cast_modulo(
            CExpression::Value(CValue::typed_pointer(Pointer::null(), CType::Int32Pointer)),
            CType::UInt64,
        ),
    ] {
        assert_eq!(
            outcome(expression),
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        );
    }
    let overflow = c_add(c_int32_literal(i32::MAX as u32), c_int32_literal(1));
    assert!(matches!(
        outcome(c_integer_cast_modulo(overflow, CType::UInt8)),
        CExpressionOutcome::UndefinedBehavior(_)
    ));
    // The explicit rule wraps; an ordinary C narrowing still requires bounds.
    assert_eq!(
        outcome(c_integer_cast_modulo(
            c_int64_literal(i64::MAX),
            CType::Int32
        )),
        CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Constant(u32::MAX)))
    );
    assert!(
        prove_c_expression_evaluation(
            CState::new(),
            c_cast(c_int64_literal(i64::MAX), CType::Int32),
        )
        .is_none()
    );
}

#[test]
fn unsigned_narrowing_distributes_constant_subtraction_modulo_the_low_word() {
    let value = Bitvector32Term::Variable(Variable(983_120));
    for decrement in [0, 1, 1u64 << 32, u64::MAX] {
        assert_eq!(
            Bitvector32Term::uint32_from_64(Bitvector32Term::uint64_subtract(
                value.clone(),
                Bitvector32Term::UInt64Constant(decrement)
            )),
            Bitvector32Term::subtract(
                Bitvector32Term::uint32_from_64(value.clone()),
                Bitvector32Term::Constant(decrement as u32)
            ),
        );
        for input in [0, 1, (1u64 << 32) + 7, u64::MAX] {
            assert_eq!(
                Bitvector32Term::uint32_from_64(Bitvector32Term::uint64_subtract(
                    Bitvector32Term::UInt64Constant(input),
                    Bitvector32Term::UInt64Constant(decrement)
                )),
                Bitvector32Term::Constant(input.wrapping_sub(decrement) as u32),
            );
        }
    }
}

#[test]
fn pointer_alignment_observes_only_a_boolean_and_keeps_integer_origin_separate() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(988_150);
    let address = Pointer::symbolic(variable);
    let carrier = CPointerValue::new(address.clone(), CType::Int32Pointer)
        .with_designation(PointerDesignation::Unresolved(variable));
    let state = CState::new();
    for assumptions in [
        PureFactContext::new(),
        PureFactContext::new().observe_pointer_addresses(),
    ] {
        let expression = CExpression::PointerAligned {
            pointer: Box::new(CExpression::Value(CValue::Pointer(carrier.clone()))),
            alignment: 4,
        };
        let paths = evaluate_c_expression_paths(
            &state,
            &expression,
            &assumptions,
            &mut ExecutionBudget::for_c_expression(&expression),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one alignment observation: {paths:?}");
        };
        let CExpressionOutcome::Value(CValue::Bool(value)) = &path.outcome else {
            panic!("alignment produces only a Boolean: {path:?}");
        };
        let expected = ConditionTerm::pointer_aligned(address.clone(), 4);
        assert_eq!(
            value,
            &Bitvector32Term::if_then_else(
                expected.clone(),
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(0),
            )
        );
        assert_eq!(
            crate::kernel::spec::c_value_comparison_proposition(
                &CValue::Bool(value.clone()),
                CComparisonOperator::Equal,
                &bool_value(1),
            ),
            Some(Proposition::ConditionIs(expected, true))
        );
        let cast = c_cast(
            CExpression::Value(CValue::Pointer(carrier.clone())),
            CType::UInt64,
        );
        let cast_paths = evaluate_c_expression_paths(
            &state,
            &cast,
            &assumptions,
            &mut ExecutionBudget::for_c_expression(&cast),
        )
        .unwrap();
        if assumptions.should_observe_pointer_addresses() {
            assert!(matches!(cast_paths.as_slice(), [path] if path.outcome ==
                CExpressionOutcome::Value(CValue::UInt64(Bitvector32Term::pointer_address(address.clone())))));
            assert!(matches!(
                crate::kernel::eval::cast_c_value_to_type(
                    CValue::UInt64(Bitvector32Term::pointer_address(address.clone())),
                    CType::Int32Pointer,
                    crate::kernel::eval::IntegerConversion::Modular,
                    &mut Vec::new(),
                    &assumptions,
                ),
                Err(CRuntimeError::PointerConversion(_))
            ));
        } else {
            assert!(matches!(cast_paths.as_slice(), [path] if matches!(
                &path.outcome,
                CExpressionOutcome::Value(CValue::PointerInteger(value))
                    if value.origin() == &carrier
            )));
        }
    }
    for alignment in [0, 3] {
        let expression = CExpression::PointerAligned {
            pointer: Box::new(CExpression::Value(CValue::Pointer(carrier.clone()))),
            alignment,
        };
        let paths = evaluate_c_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::for_c_expression(&expression),
        )
        .unwrap();
        assert!(paths.iter().all(|path| matches!(
            path.outcome,
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        )));
    }
    assert!(
        matches!(carrier.designation(), Some(PointerDesignation::Unresolved(found)) if *found == variable)
    );
}
