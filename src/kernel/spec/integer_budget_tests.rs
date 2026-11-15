use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::binary_node;
use num_bigint::BigInt;
use num_traits::One;

#[test]
fn deferred_integer_multiply_precharges_product_work_without_active_tactic() {
    // Each operand is individually below the configured setup allowance,
    // while their product is deliberately above it.  This exercises the
    // same configured allowance used during setup, without an active
    // tactic supplying a separate work limit.
    let operand_bits = 1_000usize;
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 10_000,
        smart: 10_000,
        control: 10_000,
    };
    let expression = SpecIntegerExpression::Multiply(
        Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(
            BigInt::one() << operand_bits,
        ))),
        Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(
            BigInt::one() << operand_bits,
        ))),
    );

    let result = crate::instrumentation::with_tactic_work_limits(limits, || {
        evaluate_spec_integer_expression_paths_in(
            SpecScope::unbound(&ExecutionState::default(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
    });

    assert_eq!(result, Err(ExecutionLimit::Deadline));
}

#[test]
fn from_machine_requires_program_overflow_path_fact() {
    let left = Variable(31);
    let right = Variable(32);
    let left_bits = MachineTerm::Variable(left);
    let right_bits = MachineTerm::Variable(right);
    let state = ExecutionState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let expression = SpecIntegerExpression::FromMachine(Box::new(
        SpecExpression::ProgramExpression(crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        )),
    ));

    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&state, None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("symbolic machine addition should produce paths");
    let domain = Proposition::signed_arithmetic_domain(
        MachineIntegerType::Int32,
        MachineBinaryOp::Add,
        &left_bits,
        &right_bits,
    );
    assert_eq!(paths.len(), 1);
    assert!(
        paths[0]
            .facts
            .contains(&ExecutionPureFact::new(domain.clone()))
    );
    assert_eq!(paths[0].obligations.len(), 1);
    assert_eq!(paths[0].obligations[0].proposition, domain);
    assert!(!paths[0].obligations[0].assumable);
}

#[test]
fn integer_existential_scopes_definedness_with_its_witness() {
    fn contains(proposition: &Proposition, wanted: &Proposition) -> bool {
        if proposition == wanted {
            return true;
        }
        match proposition {
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                contains(left, wanted) || contains(right, wanted)
            }
            Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
                contains(body, wanted)
            }
            _ => false,
        }
    }

    let left = Variable(701);
    let right = Variable(702);
    let witness = Variable(703);
    let left_bits = MachineTerm::Variable(left);
    let right_bits = MachineTerm::Variable(right);
    let state = ExecutionState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let body = SpecProposition::ExistsInteger {
        name: "z".to_string(),
        variable: witness,
        body: Box::new(SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(IntegerTerm::var(witness)),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::FromMachine(Box::new(SpecExpression::ProgramExpression(
                crate::kernel::program_expression::add(
                    crate::kernel::program_expression::variable("left"),
                    crate::kernel::program_expression::variable("right"),
                ),
            ))),
        }),
    };

    let paths = lower_spec_proposition_at_state_with_loop_entry_in(
        &state,
        &body,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("the Integer existential should lower");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].facts.is_empty());
    assert!(paths[0].obligations.is_empty());
    let Proposition::Exists {
        var,
        sort: Sort::Integer,
        body,
        ..
    } = &paths[0].proposition
    else {
        panic!("the lowered proposition must retain its Integer existential");
    };
    assert_eq!(*var, witness);
    let overflow = Proposition::signed_arithmetic_domain(
        MachineIntegerType::Int32,
        crate::kernel::MachineBinaryOp::Add,
        &left_bits,
        &right_bits,
    );
    assert!(
        contains(body, &overflow),
        "the C definedness guard must stay inside the existential body: {body:?}"
    );
    assert!(
        contains(
            body,
            &Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::var(witness).into(),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        binary_node!(
                            Int32,
                            Add,
                            Box::new(MachineTerm::Variable(left)),
                            Box::new(MachineTerm::Variable(right)),
                        ),
                    ))
                    .into(),
                ),
                true,
            )
        ),
        "the existential body must still compare the selected witness"
    );
}

#[test]
fn from_machine_keeps_signed_and_unsigned_values_distinct() {
    let signed = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
        ProgramValue::Int32(MachineTerm::constant(u32::MAX)),
    )));
    let unsigned = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
        ProgramValue::UInt32(MachineTerm::constant(u32::MAX)),
    )));
    let evaluate = |expression| {
        evaluate_spec_integer_expression_paths_in(
            SpecScope::unbound(&ExecutionState::default(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .unwrap()
        .pop()
        .unwrap()
        .value
    };

    assert_eq!(evaluate(signed), IntegerTerm::constant_i64(-1));
    assert_eq!(
        evaluate(unsigned),
        IntegerTerm::constant(BigInt::from(u32::MAX))
    );
}

#[test]
fn bitvector_substitution_reaches_machine_integer_proposition() {
    let variable = Variable(47);
    let proposition = Proposition::ConditionIs(
        ConditionTerm::integer_equal(
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                MachineTerm::Variable(variable),
            )),
            IntegerTerm::constant_i64(7),
        ),
        true,
    );
    let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
        &proposition,
        variable,
        &MachineTerm::constant(7),
    );
    // Substitution reached inside the machine-backed Integer term. The
    // observation it left behind is decided -- `to_integer(7)` is the
    // mathematical 7, the same Integer the evaluation below produces for
    // the same machine constant -- so the equation against 7 is decided
    // too, by the Integer equality's own smart constructor.
    assert_eq!(
        substituted,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    );

    let expression = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
        ProgramValue::Int32(MachineTerm::constant(7)),
    )));
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&ExecutionState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .unwrap();
    assert_eq!(paths[0].value, IntegerTerm::constant_i64(7));
}

#[test]
fn integer_fold_loadable_obligation_keeps_carriers_separate() {
    let shared_id = Variable(71_100);
    let index = IntegerRangeFoldIndex::Int32 {
        start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
        end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(4)),
    };
    let integer_address = MachineTerm::IntegerToMachine {
        value: IntegerTerm::var(shared_id).into(),
        destination: MachineIntegerType::Int32,
    };
    let integer_address_requirement = Proposition::MemoryLoadable {
        memory: Memory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::scaled_int32_node(integer_address, 4),
        },
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let wrapped = integer_range_fold_body_obligation(
        integer_address_requirement,
        &index,
        shared_id,
        shared_id,
    );
    let Proposition::ForAll {
        var: accumulator,
        sort: Sort::Integer,
        body: item_body,
        ..
    } = wrapped
    else {
        panic!("an Integer address must retain its Integer binder");
    };
    assert_eq!(accumulator, shared_id);
    assert!(matches!(
        item_body.as_ref(),
        Proposition::ForAll {
            var,
            sort: Sort::ProgramInt32,
            ..
        } if *var == shared_id
    ));

    let c_address_requirement = Proposition::MemoryLoadable {
        memory: Memory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(shared_id), 4),
        },
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let wrapped =
        integer_range_fold_body_obligation(c_address_requirement, &index, shared_id, shared_id);
    let Proposition::ForAll {
        var,
        sort: Sort::ProgramInt32,
        ..
    } = wrapped
    else {
        panic!("a C item with the same numeric id must not bind an Integer");
    };
    assert_eq!(var, shared_id);
}

#[test]
fn integer_fold_loadable_obligation_sees_integer_in_registered_pointer() {
    let accumulator = Variable(71_106);
    let item = Variable(71_107);
    let memory = crate::kernel::intern_memory(Memory::new().with_block("array", 16));
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::scaled_int32_node(
            MachineTerm::IntegerToMachine {
                value: IntegerTerm::var(accumulator).into(),
                destination: MachineIntegerType::Int32,
            },
            4,
        ),
    };
    let load = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Int32,
    );
    let requirement = Proposition::MemoryLoadable {
        memory: Memory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(load), 4),
        },
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let index = IntegerRangeFoldIndex::Int32 {
        start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
        end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(4)),
    };
    let wrapped = integer_range_fold_body_obligation(requirement, &index, accumulator, item);
    assert!(matches!(
        wrapped,
        Proposition::ForAll {
            var,
            sort: Sort::Integer,
            ..
        } if var == accumulator
    ));

    let direct_requirement = Proposition::MemoryLoadable {
        memory: Memory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Variable(load),
        },
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let direct_wrapped =
        integer_range_fold_body_obligation(direct_requirement, &index, accumulator, item);
    assert!(matches!(
        direct_wrapped,
        Proposition::ForAll {
            var,
            sort: Sort::Integer,
            ..
        } if var == accumulator
    ));
}

#[test]
fn integer_fold_loadable_obligation_keeps_accumulator_for_two_hop_direct_offset() {
    let accumulator = Variable(71_108);
    let item = Variable(71_109);
    let memory = crate::kernel::intern_memory(Memory::new().with_block("array", 16));
    let inner = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::IntegerToMachine {
                    value: IntegerTerm::var(accumulator).into(),
                    destination: MachineIntegerType::Int32,
                },
                4,
            ),
        },
        crate::kernel::LoadKind::Int32,
    );
    let outer = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(0)),
                Box::new(PointerOffsetTerm::Variable(inner)),
            ),
        },
        crate::kernel::LoadKind::Int32,
    );
    let requirement = Proposition::MemoryLoadable {
        memory: Memory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Variable(outer),
        },
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let index = IntegerRangeFoldIndex::Int32 {
        start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
        end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(4)),
    };
    let wrapped = integer_range_fold_body_obligation(requirement, &index, accumulator, item);
    assert!(matches!(
        wrapped,
        Proposition::ForAll {
            var,
            sort: Sort::Integer,
            ..
        } if var == accumulator
    ));
}

#[test]
fn fold_body_drops_only_exact_registered_load_definition_conjuncts() {
    let memory = crate::kernel::intern_memory(Memory::new().with_block("array", 16));
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let load = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Int32,
    );
    let (registered_memory, registered_pointer) =
        crate::kernel::eval::registered_load_for_variable(&load)
            .expect("the load variable must retain its exact descriptor");
    let defining = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(load)),
            right: Box::new(MachineTerm::MemoryLoad(
                registered_memory.clone(),
                Box::new(registered_pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    let loadable = Proposition::MemoryLoadable {
        memory: registered_memory.as_ref().clone(),
        base: registered_pointer.clone(),
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let exact = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(defining.clone()),
        Box::new(loadable.clone()),
    ))
    .expect("the viewability conjunct must remain");
    assert!(matches!(exact, Proposition::MemoryLoadable { .. }));

    let guarded = Proposition::Implies(Box::new(defining), Box::new(loadable.clone()));
    let retained_guard = drop_verified_load_definition_conjuncts(guarded.clone())
        .expect("a guarded definition must remain a guarded obligation");
    assert_eq!(retained_guard, guarded);

    let tampered_pointer = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(load)),
            right: Box::new(MachineTerm::MemoryLoad(
                registered_memory.clone(),
                Box::new(Pointer {
                    offset: PointerOffsetTerm::Constant(4),
                    ..registered_pointer.clone()
                }),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    let retained_pointer = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(tampered_pointer),
        Box::new(loadable),
    ))
    .expect("a tampered definition must remain an obligation");
    assert!(matches!(retained_pointer, Proposition::And(_, _)));

    let tampered_memory = crate::kernel::intern_memory(Memory::new().with_block("other", 16));
    let tampered_state = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(load)),
            right: Box::new(MachineTerm::MemoryLoad(
                tampered_memory,
                Box::new(registered_pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    let retained_state = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(tampered_state),
        Box::new(Proposition::MemoryLoadable {
            memory: registered_memory.as_ref().clone(),
            base: registered_pointer.clone(),
            bytes: MachineTerm::constant(4),
            wide: false,
        }),
    ))
    .expect("a tampered state must remain an obligation");
    assert!(matches!(retained_state, Proposition::And(_, _)));

    let unknown = Variable((1u64 << 40) + 123_456_789);
    let unknown_definition = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(unknown)),
            right: Box::new(MachineTerm::MemoryLoad(
                registered_memory,
                Box::new(registered_pointer),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    let retained_unknown = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(unknown_definition),
        Box::new(Proposition::MemoryLoadable {
            memory: memory.as_ref().clone(),
            base: pointer,
            bytes: MachineTerm::constant(4),
            wide: false,
        }),
    ))
    .expect("an unknown reserved variable must remain an obligation");
    assert!(matches!(retained_unknown, Proposition::And(_, _)));
}

#[test]
fn defined_memory_load_retains_typed_validity_after_dropping_registry_metadata() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let proposition = SpecProposition::Defined(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(Memory::new()),
        pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
            PointerValue::new(pointer, ProgramType::Int32Pointer),
        ))),
        value_type: ProgramType::Int32,
    });

    let paths = lower_spec_proposition_at_state_with_loop_entry_in(
        &ExecutionState::default(),
        &proposition,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("a symbolic load should lower to a definedness obligation");
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        &paths[0].proposition,
        Proposition::MemoryReadDefined {
            value_type: ProgramType::Int32,
            ..
        }
    ));
    assert!(!matches!(
        &paths[0].proposition,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    ));
}

#[test]
fn defined_memory_load_retains_typed_validity_for_an_already_known_cell() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let proposition = SpecProposition::Defined(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(Memory::new().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        )),
        pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
            PointerValue::new(pointer, ProgramType::Int32Pointer),
        ))),
        value_type: ProgramType::Int32,
    });

    let paths = lower_spec_proposition_at_state_with_loop_entry_in(
        &ExecutionState::default(),
        &proposition,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("a symbolic load should lower to a definedness obligation");
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        &paths[0].proposition,
        Proposition::MemoryReadDefined {
            value_type: ProgramType::Int32,
            ..
        }
    ));
    assert!(!matches!(
        &paths[0].proposition,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    ));
}

#[test]
fn integer_existential_branch_filters_exact_load_definitions_only() {
    fn contains(proposition: &Proposition, wanted: &Proposition) -> bool {
        if proposition == wanted {
            return true;
        }
        match proposition {
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                contains(left, wanted) || contains(right, wanted)
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => contains(body, wanted),
            _ => false,
        }
    }

    let memory = crate::kernel::intern_memory(Memory::new().with_block("array", 16));
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let load = crate::kernel::eval::load_variable_for_exact_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Int32,
        4,
    );
    let (registered_memory, registered_pointer) =
        crate::kernel::eval::registered_load_for_variable(&load)
            .expect("the exact load must have a registry descriptor");
    let defining = |memory: SharedMemory, pointer: Pointer, variable: Variable| {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(variable)),
                right: Box::new(MachineTerm::MemoryLoad(
                    memory,
                    Box::new(pointer),
                    crate::kernel::LoadKind::Int32,
                )),
            },
            true,
        )
    };
    let exact = defining(registered_memory.clone(), registered_pointer.clone(), load);
    let loadable = Proposition::MemoryLoadable {
        memory: registered_memory.as_ref().clone(),
        base: registered_pointer.clone(),
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let marker = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let exact_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(exact.clone())].into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(exact.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let exact_branch = existential_body_branch(&exact_path);
    assert!(!contains(&exact_branch, &exact));
    assert!(contains(&exact_branch, &loadable));
    assert!(contains(&exact_branch, &marker));

    let tampered_pointer = Pointer {
        offset: PointerOffsetTerm::Constant(4),
        ..registered_pointer.clone()
    };
    let tampered_pointer_definition = defining(registered_memory.clone(), tampered_pointer, load);
    let tampered_pointer_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(
            tampered_pointer_definition.clone(),
        )]
        .into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(tampered_pointer_definition.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let tampered_pointer_branch = existential_body_branch(&tampered_pointer_path);
    assert!(contains(
        &tampered_pointer_branch,
        &tampered_pointer_definition
    ));
    assert!(contains(&tampered_pointer_branch, &loadable));

    let other_memory = crate::kernel::intern_memory(Memory::new().with_block("other", 16));
    let tampered_state_definition = defining(other_memory, registered_pointer.clone(), load);
    let tampered_state_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(
            tampered_state_definition.clone(),
        )]
        .into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(tampered_state_definition.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let tampered_state_branch = existential_body_branch(&tampered_state_path);
    assert!(contains(&tampered_state_branch, &tampered_state_definition));

    let unknown = Variable((1u64 << 40) + 123_456_789);
    let unknown_definition = defining(registered_memory, registered_pointer, unknown);
    let unknown_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(unknown_definition.clone())].into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(unknown_definition.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let unknown_branch = existential_body_branch(&unknown_path);
    assert!(contains(&unknown_branch, &unknown_definition));

    // The normalizer does not manufacture a source memory guard. A path
    // carrying only a registered definition therefore retains no
    // MemoryLoadable evidence and cannot satisfy a missing-guard goal.
    let missing_loadability_path = SpecPropositionPath {
        proposition: marker,
        facts: vec![ExecutionPureFact::certified(exact.clone())].into(),
        obligations: vec![ProofObligation::verification_condition(exact)],
        introductions: LoweringIntroductions::new(),
    };
    let missing_loadability_branch = existential_body_branch(&missing_loadability_path);
    assert!(!contains(&missing_loadability_branch, &loadable));
}

#[test]
fn empty_integer_fold_preserves_shape_without_live_load_obligation() {
    let missing_pointer = Pointer {
        block: PointerBlock::Concrete("missing".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let body = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(Memory::new()),
        pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
            PointerValue::new(missing_pointer.clone(), ProgramType::Int32Pointer),
        ))),
        value_type: ProgramType::Int32,
    }));
    let expression = SpecIntegerExpression::RangeFold {
        index: SpecIntegerRangeFoldIndex::Int32 {
            start: Box::new(SpecExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(4),
            ))),
            end: Box::new(SpecExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(4),
            ))),
        },
        initial: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(19))),
        accumulator: Variable(71_101),
        item: Variable(71_102),
        body: Box::new(body),
    };
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&ExecutionState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("an empty range still typechecks its body");
    assert_eq!(paths.len(), 1);
    let IntegerTerm::RangeFold { body, .. } = &paths[0].value else {
        panic!("empty fold capture lost the fold shape");
    };
    let IntegerTerm::Machine(machine) = body.as_ref() else {
        panic!("empty fold body lost its symbolic load")
    };
    let load_pointer = match machine.value() {
        MachineTerm::MemoryLoad(_, pointer, _) => pointer.as_ref().clone(),
        MachineTerm::Variable(load) => crate::kernel::eval::registered_load_for_variable(load)
            .map(|(_, pointer)| pointer)
            .expect("registered symbolic load must retain its pointer"),
        _ => panic!("empty fold body lost its symbolic load"),
    };
    assert_eq!(load_pointer, missing_pointer);
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn nonempty_integer_fold_is_logical_but_checked_reads_remain_scoped() {
    let item = Variable(71_103);
    let pointer = SpecExpression::PointerOffset {
        pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
            PointerValue::new(
                Pointer {
                    block: PointerBlock::Symbolic(Variable(71_104)),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramType::Int32Pointer,
            ),
        ))),
        elements: Box::new(SpecExpression::Value(ProgramValue::Int32(
            MachineTerm::Variable(item),
        ))),
        byte_width: 4,
    };
    let body = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(Memory::new()),
        pointer: Box::new(pointer),
        value_type: ProgramType::Int32,
    }));
    let expression = SpecIntegerExpression::RangeFold {
        index: SpecIntegerRangeFoldIndex::Int32 {
            start: Box::new(SpecExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(0),
            ))),
            end: Box::new(SpecExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(4),
            ))),
        },
        initial: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
        accumulator: Variable(71_105),
        item,
        body: Box::new(body),
    };
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&ExecutionState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("a symbolic body load should produce one scoped path");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].obligations.is_empty());
    let checked = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&ExecutionState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::checked(&mut ExecutionBudget::default()),
    )
    .expect("checked fold preserves the binder around read validity");
    assert_eq!(checked.len(), 1);
    assert!(checked[0].obligations.iter().any(|obligation| {
        matches!(obligation.proposition(), Proposition::ForAll {
                var, sort: Sort::ProgramInt32, body,
.. } if *var == item && matches!(body.as_ref(), Proposition::Implies(_, _)))
    }));
}

#[test]
fn integer_to_machine_converts_exact_boundaries_without_wrapping() {
    let cases = [
        (
            MachineIntegerType::Int8,
            BigInt::from(i8::MIN),
            crate::kernel::int8(i8::MIN as i32 as u32),
        ),
        (
            MachineIntegerType::Int16,
            BigInt::from(i16::MIN),
            crate::kernel::int16(i16::MIN as i32 as u32),
        ),
        (
            MachineIntegerType::Int32,
            BigInt::from(i32::MIN),
            ProgramValue::Int32(MachineTerm::constant(i32::MIN as u32)),
        ),
        (
            MachineIntegerType::UInt8,
            BigInt::from(u8::MAX),
            crate::kernel::uint8(u8::MAX as u32),
        ),
        (
            MachineIntegerType::UInt16,
            BigInt::from(u16::MAX),
            crate::kernel::uint16(u16::MAX as u32),
        ),
        (
            MachineIntegerType::UInt32,
            BigInt::from(u32::MAX),
            ProgramValue::UInt32(MachineTerm::uint32_constant(u32::MAX)),
        ),
        (
            MachineIntegerType::Int64,
            BigInt::from(i64::MIN),
            ProgramValue::Int64(MachineTerm::int64_constant(i64::MIN)),
        ),
        (
            MachineIntegerType::UInt64,
            BigInt::from(u64::MAX),
            ProgramValue::UInt64(MachineTerm::uint64_constant(u64::MAX)),
        ),
    ];
    for (destination, integer, expected) in cases {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(integer))),
            destination,
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .expect("representable Integer constants should convert");
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value.clone().into_native(), expected);
    }
}

#[test]
fn integer_to_machine_rejects_out_of_range_constants() {
    let cases = [
        (MachineIntegerType::Int8, BigInt::from(i8::MIN) - 1),
        (MachineIntegerType::Int8, BigInt::from(i8::MAX) + 1),
        (MachineIntegerType::Int16, BigInt::from(i16::MAX) + 1),
        (MachineIntegerType::Int32, BigInt::from(i32::MIN) - 1),
        (MachineIntegerType::UInt8, BigInt::from(-1)),
        (MachineIntegerType::UInt16, BigInt::from(u16::MAX) + 1),
        (MachineIntegerType::UInt32, BigInt::from(u32::MAX) + 1),
        (MachineIntegerType::Int64, BigInt::from(i64::MAX) + 1),
        (MachineIntegerType::UInt64, BigInt::from(u64::MAX) + 1),
    ];
    for (destination, integer) in cases {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(integer))),
            destination,
        };
        let result = evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        );
        assert_eq!(result, Err(ExecutionLimit::Paths));
    }
}

#[test]
fn integer_to_machine_symbolic_values_keep_carrier_and_range_obligations() {
    let variable = Variable(990);
    let value = IntegerTerm::Variable(variable);
    let cases = [
        (
            MachineIntegerType::Int8,
            BigInt::from(i8::MIN),
            BigInt::from(i8::MAX),
        ),
        (
            MachineIntegerType::Int16,
            BigInt::from(i16::MIN),
            BigInt::from(i16::MAX),
        ),
        (
            MachineIntegerType::Int32,
            BigInt::from(i32::MIN),
            BigInt::from(i32::MAX),
        ),
        (
            MachineIntegerType::UInt8,
            BigInt::from(0),
            BigInt::from(u8::MAX),
        ),
        (
            MachineIntegerType::UInt16,
            BigInt::from(0),
            BigInt::from(u16::MAX),
        ),
        (
            MachineIntegerType::UInt32,
            BigInt::from(0),
            BigInt::from(u32::MAX),
        ),
        (
            MachineIntegerType::Int64,
            BigInt::from(i64::MIN),
            BigInt::from(i64::MAX),
        ),
        (
            MachineIntegerType::UInt64,
            BigInt::from(0),
            BigInt::from(u64::MAX),
        ),
    ];
    for (destination, expected_lower, expected_upper) in cases {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(value.clone())),
            destination,
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .expect("symbolic conversion should produce a path");
        assert_eq!(paths.len(), 1);
        assert!(paths[0].facts.is_empty());
        assert!(matches!(
            &paths[0].value.clone().into_native(),
            ProgramValue::Int8(MachineTerm::IntegerToMachine { destination: d, .. }) | ProgramValue::Int16(MachineTerm::IntegerToMachine { destination: d, .. })
                | ProgramValue::Int32(MachineTerm::IntegerToMachine { destination: d, .. })
                | ProgramValue::UInt8(MachineTerm::IntegerToMachine { destination: d, .. })
                | ProgramValue::UInt16(MachineTerm::IntegerToMachine { destination: d, .. })
                | ProgramValue::UInt32(MachineTerm::IntegerToMachine { destination: d, .. })
                | ProgramValue::Int64(MachineTerm::IntegerToMachine { destination: d, .. })
                | ProgramValue::UInt64(MachineTerm::IntegerToMachine { destination: d, .. })
                if *d == destination
        ));
        assert_eq!(paths[0].obligations.len(), 2);
        assert!(
            paths[0]
                .obligations
                .iter()
                .all(|obligation| !obligation.is_assumable())
        );
        let lower = IntegerTerm::constant(expected_lower);
        let upper = IntegerTerm::constant(expected_upper);
        assert!(paths[0].obligations.iter().any(|obligation| {
            *obligation.proposition()
                == Proposition::ConditionIs(
                    ConditionTerm::integer_greater_equal(value.clone(), lower.clone()),
                    true,
                )
        }));
        assert!(paths[0].obligations.iter().any(|obligation| {
            *obligation.proposition()
                == Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(value.clone(), upper.clone()),
                    true,
                )
        }));
    }

    let left = Variable(991);
    let right = Variable(992);
    let state = ExecutionState::new()
        .with_local("left", int32(MachineTerm::Variable(left)))
        .with_local("right", int32(MachineTerm::Variable(right)));
    let expression = SpecExpression::IntegerToMachine {
        value: Box::new(SpecIntegerExpression::FromMachine(Box::new(
            SpecExpression::ProgramExpression(crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("left"),
                crate::kernel::program_expression::variable("right"),
            )),
        ))),
        destination: MachineIntegerType::Int32,
    };
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &state,
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("child expression effects should be preserved");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].facts.contains(&ExecutionPureFact::new(
        Proposition::signed_arithmetic_domain(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            &MachineTerm::Variable(left),
            &MachineTerm::Variable(right),
        )
    )));
    assert_eq!(paths[0].obligations.len(), 3);
    assert!(
        paths[0]
            .obligations
            .iter()
            .all(|obligation| !obligation.is_assumable())
    );
    assert!(
        paths[0]
            .obligations
            .iter()
            .any(|obligation| obligation.proposition()
                == &Proposition::signed_arithmetic_domain(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    &MachineTerm::Variable(left),
                    &MachineTerm::Variable(right),
                ))
    );
}
