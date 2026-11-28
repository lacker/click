#[test]
fn balanced_unit_sum_domain_requires_all_three_original_domains() {
    use crate::kernel::OldConditionTerm;
    let a = OldMachineTerm::Variable(Variable(100));
    let b = OldMachineTerm::Variable(Variable(101));
    let one = OldMachineTerm::constant(1);
    let guards = [
        OldConditionTerm::signed_add_overflows(a.clone(), b.clone()),
        OldConditionTerm::signed_add_overflows(a.clone(), one.clone()),
        OldConditionTerm::signed_subtract_overflows(b.clone(), one.clone()),
    ];
    let goal = Proposition::condition_is(
        OldConditionTerm::signed_add_overflows(
            OldMachineTerm::add(a.clone(), one.clone()),
            OldMachineTerm::subtract(b.clone(), one.clone()),
        ),
        false,
    );
    for missing in 0..=3 {
        let facts = guards
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != missing)
            .fold(PureFactContext::new(), |facts, (_, condition)| {
                facts.assume_condition(condition.clone(), false)
            });
        assert_eq!(facts.settles_exactly(&goal), missing == 3);
    }
    // Return reverses the two original summands. Commutativity must
    // preserve the check without dropping either child-domain premise.
    let reversed_guards = [
        OldConditionTerm::signed_add_overflows(b.clone(), a.clone()),
        guards[1].clone(),
        guards[2].clone(),
    ];
    for missing in 0..=3 {
        let facts = reversed_guards
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != missing)
            .fold(PureFactContext::new(), |facts, (_, condition)| {
                facts.assume_condition(condition.clone(), false)
            });
        assert_eq!(facts.settles_exactly(&goal), missing == 3);
    }
    // The original sum fits, but the increment wraps at MAX, or the
    // predecessor wraps at MIN. Modular equality must not certify either.
    for (left, right) in [(i32::MAX, 0), (0, i32::MIN)] {
        assert!(left.checked_add(right).is_some());
        assert!(
            left.checked_add(1)
                .and_then(|x| right.checked_sub(1).and_then(|y| x.checked_add(y)))
                .is_none()
        );
    }
}

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
// These operation tests also exercise kernel proposition search explicitly.
use crate::kernel::{
    Address, AddressBase, AddressOffset, ComparisonOperator, CompositeResourceDefinition,
    OldMachineTerm, ProgramType, ProgramValue, ResourceAccessMode, ResourceFact, ResourceSpec,
    SpecExpression, SymbolicMemory, int32, program_function,
};

/// One arm state holding a checked view rooted in a fresh borrow.
fn arm_holding_a_view(name: &str) -> (ExecutionState, crate::kernel::borrows::BorrowBinding) {
    let support_fact = ResourceFact::own_token(format!("{name}_support"), Vec::new());
    let viewed = ResourceFact::view_token(format!("{name}_view"), Vec::new());
    let resources = crate::kernel::ResourceContext::new()
        .unchecked_with_facts([support_fact.clone(), viewed.clone()]);
    let support = resources.owned_occurrences_for_fact(&support_fact)[0];
    let occurrence = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::borrows::BorrowLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let opening = ledger
        .lend(owner, reader, support, support_fact)
        .expect("the arm's view is backed by a fresh borrow");
    let binding = crate::kernel::borrows::BorrowBinding {
        borrow: opening.borrow,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    let state = ExecutionState::new()
        .with_borrow_ledger(Some(ledger))
        .with_borrow_participant(Some(reader))
        .with_resource_context_and_borrow_dependencies(resources, [(occurrence, binding.clone())]);
    (state, binding)
}

#[test]
fn frame_exchange_retains_the_exits_exact_stable_view_dependency() {
    let (state, binding) = arm_holding_a_view("loop_exit");
    let body = state.resources();
    let original = body.occurrences_for_fact(&binding.viewed)[0];
    let (exit, inserted) = body
        .clone()
        .without_bound_view_occurrence(original, &binding)
        .unwrap()
        .unchecked_with_facts_and_occurrences([binding.viewed.clone()]);
    let final_occurrence = inserted[0].1;
    let exit = exit.with_borrow_dependency(final_occurrence, binding.clone());
    let outside = ResourceFact::own_composite("outside".into(), Vec::new());
    let frame = body.clone().unchecked_with_fact(outside.clone());
    let restored = exit
        .restore_frame_after_exchange(body, &frame, &PureFactContext::new())
        .unwrap();
    assert!(restored.contains_exact_representation(&outside));
    assert_eq!(restored.borrow_dependency(final_occurrence), Some(&binding));
    assert!(restored.borrow_dependency(original).is_none());
    assert!(restored.view_fact_at_occurrence(original).is_none());
}

fn successor_carrying(binding: &crate::kernel::borrows::BorrowBinding) -> ExecutionState {
    let resources =
        crate::kernel::ResourceContext::new().unchecked_with_facts([binding.viewed.clone()]);
    let occurrence = resources.occurrences_for_fact(&binding.viewed)[0];
    // A fresh interface context: the occurrence is new, so only the
    // binding's own content can connect it to an arm's authority.
    ExecutionState::new()
        .with_resource_context_and_borrow_dependencies(resources, [(occurrence, binding.clone())])
}

#[test]
fn an_interface_successor_may_only_carry_a_borrow_an_arm_held() {
    let (left, left_binding) = arm_holding_a_view("left");
    let (right, right_binding) = arm_holding_a_view("right");

    // No claimed authority at all is always inherited.
    assert!(interface_successor_borrows_are_inherited(
        &ExecutionState::new(),
        [&left, &right]
    ));
    // Either arm's own root is, whichever arm held it.
    assert!(interface_successor_borrows_are_inherited(
        &successor_carrying(&left_binding),
        [&left, &right]
    ));
    assert!(interface_successor_borrows_are_inherited(
        &successor_carrying(&right_binding),
        [&left, &right]
    ));
    // A root neither arm reached is not admitted by the join.
    let (_, outside) = arm_holding_a_view("outside");
    assert!(!interface_successor_borrows_are_inherited(
        &successor_carrying(&outside),
        [&left, &right]
    ));
    // Nor is one arm's root once that arm is not part of the join.
    assert!(!interface_successor_borrows_are_inherited(
        &successor_carrying(&right_binding),
        [&left, &left]
    ));
}

#[test]
fn interface_inheritance_tracks_duplicate_bindings_and_replacement() {
    let (arm, binding) = arm_holding_a_view("same_spelling");
    let (_, replacement) = arm_holding_a_view("same_spelling");
    assert_eq!(binding.viewed, replacement.viewed);
    assert_ne!(binding, replacement);
    let claim = successor_carrying(&binding);
    let replacement_claim = successor_carrying(&replacement);
    assert!(!interface_successor_borrows_are_inherited(
        &replacement_claim,
        [&arm, &arm],
    ));

    let original = arm.resources().occurrences_for_fact(&binding.viewed)[0];
    let (duplicated, inserted) = arm
        .resources()
        .clone()
        .unchecked_with_facts_and_occurrences([binding.viewed.clone()]);
    let duplicate = inserted[0].1;
    let once = duplicated
        .with_borrow_dependency(duplicate, binding.clone())
        .without_bound_view_occurrence(original, &binding)
        .expect("the original binding can be removed independently");
    let once = arm.clone().with_resource_context(once);
    assert!(interface_successor_borrows_are_inherited(
        &claim,
        [&once, &once]
    ));

    let rebound_bindings = once.borrow_bindings().with_inserted(duplicate, replacement);
    let rebound = once.clone().with_resource_context(
        once.resources()
            .clone()
            .with_borrow_dependency_state(rebound_bindings.state()),
    );
    assert!(!interface_successor_borrows_are_inherited(
        &claim,
        [&rebound, &rebound],
    ));
    assert!(interface_successor_borrows_are_inherited(
        &replacement_claim,
        [&rebound, &rebound],
    ));
    assert!(interface_successor_borrows_are_inherited(
        &claim,
        [&arm, &arm]
    ));
}

fn constructor_partition_fixture(
    width: usize,
) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
    constructor_partition_fixture_with_type(width, ProgramType::Int32)
}

fn constructor_partition_fixture_with_type(
    width: usize,
    payload_type: ProgramType,
) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType,
        AlgebraicVariantType,
    };
    let variants: Arc<[AlgebraicVariantType]> = (0..width)
        .map(|index| AlgebraicVariantType {
            name: format!("C{index}"),
            fields: vec![AlgebraicValueType::Program(payload_type)],
        })
        .collect::<Vec<_>>()
        .into();
    let key = AlgebraicValueType::Algebraic {
        name: "Cases".into(),
        arguments: vec![],
    };
    let value = AlgebraicTerm {
        algebraic_type: AlgebraicType {
            rigid: false,
            name: "Cases".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
        },
        node: AlgebraicTermNode::Variable(Variable(8)),
    };
    let state = ExecutionState::new();
    let function = program_function(
        ProgramType::Int32,
        "entry",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(algebraic_binder(0)),
        ))),
    );
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    assert!(
        core.record_checked_function_entry(&function, &[], &state, PureFactContext::new())
            .is_ok()
    );
    (core, value)
}

#[test]
fn constructor_partition_checks_complete_coverage_and_exact_scopes() {
    for width in [1, 2, 4, 16] {
        let (core, value) = constructor_partition_fixture(width);
        let root = PureFactStore::default();
        let (partition, fields, _) = core
            .algebraic_case_partition(
                &root,
                &value,
                &crate::kernel::ExecutionEnvironment::new(),
                &[],
                None,
                0,
            )
            .unwrap();
        assert_eq!(fields.len(), width);
        let mut traces = Vec::new();
        for index in 0..width {
            let mut arm = core.clone();
            assert!(arm.record_proof_case_arm(
                partition.clone(),
                index,
                root.with_fact(partition.case_fact(index).unwrap().clone())
            ));
            traces.push(arm.execution_evidence[0].clone());
        }
        assert!(crate::kernel::api::proof_case_partitions_are_exhaustive(
            &traces
        ));
        if width > 1 {
            assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
                &traces[1..]
            ));
        }
        let mut wrong = core.clone();
        assert!(!wrong.record_proof_case_arm(partition.clone(), width, root.clone()));
        assert!(!wrong.record_proof_case_arm(partition.clone(), 0, root.clone()));
        let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
        let extra = facts.with_fact(Proposition::Predicate {
            name: "unjustified".into(),
            arguments: vec![],
        });
        assert!(!wrong.record_proof_case_arm(partition.clone(), 0, extra));
        wrong.state = ExecutionState::new().with_local("changed", int32(1)).into();
        // A witness belongs to the exact state its partition was issued
        // against, so the moved frontier cannot take an arm of the old one.
        assert!(!wrong.record_proof_case_arm(partition.clone(), 0, facts));
        // It can issue its own, though: a proof `match` runs at any
        // frontier the proof has reached, not only at an unchanged entry.
        let (moved, _, _) = wrong
            .algebraic_case_partition(
                &root,
                &value,
                &crate::kernel::ExecutionEnvironment::new(),
                &[],
                None,
                0,
            )
            .expect("a frontier that has moved still issues its partition");
        let moved_facts = root.with_fact(moved.case_fact(0).unwrap().clone());
        assert!(wrong.record_proof_case_arm(moved, 0, moved_facts));
    }
}

#[test]
fn constructor_partition_exclusion_requires_false_in_that_arm() {
    let (core, mut value) = constructor_partition_fixture(2);
    value.node = crate::kernel::AlgebraicTermNode::Constructor {
        variant: "C0".into(),
        fields: vec![crate::kernel::AlgebraicValue::Program(int32(11))],
    };
    let root = PureFactStore::default();
    let (partition, _, _) = core
        .algebraic_case_partition(
            &root,
            &value,
            &crate::kernel::ExecutionEnvironment::new(),
            &[],
            None,
            0,
        )
        .unwrap();
    let live = partition.facts_for_case(0).unwrap();
    let dead = partition.facts_for_case(1).unwrap();
    assert!(partition.excluding_constructor_case_in(0, &live).is_none());
    assert!(partition.excluding_constructor_case_in(1, &live).is_none());
    assert!(partition.excluding_constructor_case_in(2, &dead).is_none());
    let excluded = partition.excluding_constructor_case_in(1, &dead).unwrap();
    assert!(!Arc::ptr_eq(&partition.identity, &excluded.identity));
    let mut old_arm = core.clone();
    let live_facts = partition.facts_for_case(0).unwrap();
    assert!(old_arm.record_proof_case_arm(partition, 0, live_facts));
    assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
        &old_arm.execution_evidence
    ));
    let mut live_arm = core;
    let live_facts = excluded.facts_for_case(0).unwrap();
    assert!(live_arm.record_proof_case_arm(excluded, 0, live_facts));
    assert!(crate::kernel::api::proof_case_partitions_are_exhaustive(
        &live_arm.execution_evidence
    ));
    // New exclusion evidence cannot discharge an old partition's missing arm.
    assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
        &[
            old_arm.execution_evidence[0].clone(),
            live_arm.execution_evidence[0].clone(),
        ]
    ));
}

fn algebraic_binder(index: u64) -> Variable {
    Variable::produced(crate::kernel::Producer::AlgebraicBinder, index)
}

fn binder_index(variable: &Variable) -> u64 {
    variable
        .algebraic_binder_index()
        .expect("a case witness is an algebraic binder")
}

#[test]
fn constructor_partition_witnesses_avoid_source_facts_and_previous_matches() {
    let (core, value) = constructor_partition_fixture(2);
    let occupied = algebraic_binder(1);
    let root = PureFactStore::from_ordered(&[Proposition::Equal(
        crate::kernel::Term::ProgramValue(
            ProgramValue::Int32(OldMachineTerm::Variable(occupied)).into(),
        ),
        crate::kernel::Term::ProgramValue(int32(0).into()),
    )]);
    let env = crate::kernel::ExecutionEnvironment::new();
    let (partition, fields, next) = core
        .algebraic_case_partition(&root, &value, &env, &[], None, 0)
        .unwrap();
    assert!(fields.iter().flatten().all(|(var, _)| *var != occupied));
    let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
    let (_, later, _) = core
        .algebraic_case_partition(&facts, &value, &env, &[], None, next)
        .unwrap();
    assert!(
        later
            .iter()
            .flatten()
            .all(|(var, _)| binder_index(var) >= next)
    );
    assert!(
        core.algebraic_case_partition(&root, &value, &env, &[], None, u64::MAX)
            .is_none()
    );
}

/// A frontier that is not a function entry reserves the region's own entry
/// state, so a witness cannot name a value the region started with. Witnesses
/// are algebraic binders, which no execution issues, so how many identities
/// the execution has issued since does not constrain them.
#[test]
fn constructor_partition_witnesses_avoid_the_region_state_and_issued_variables() {
    let (_, value) = constructor_partition_fixture(2);
    let occupied = algebraic_binder(0);
    let state = ExecutionState::new().with_local(
        "cursor",
        ProgramValue::Int32(OldMachineTerm::Variable(occupied)),
    );
    let core = ExecutionProofCore::at_entry(state, ExecutionFrontier::default());
    let root = PureFactStore::default();
    let env = crate::kernel::ExecutionEnvironment::new();
    let (_, fields, _) = core
        .algebraic_case_partition(&root, &value, &env, &[], None, 0)
        .expect("a loop-body frontier issues its partition");
    assert!(fields.iter().flatten().all(|(var, _)| *var != occupied));

    let mut issued = core.clone();
    issued
        .advance_kernel_variable_mark(200_000)
        .expect("the counter moves forward");
    assert_eq!(issued.issued_kernel_variable_bound(), 1_200_000);
    let (_, fields, _) = issued
        .algebraic_case_partition(&root, &value, &env, &[], None, 1)
        .expect("issued identities do not constrain algebraic binders");
    assert!(
        fields
            .iter()
            .flatten()
            .any(|(var, _)| *var == algebraic_binder(1))
    );
}

/// The counter is the kernel's: it moves forward through
/// [`ExecutionProofCore::advance_kernel_variable_mark`] and a rewind is
/// refused rather than silently re-issuing identities a live value carries.
#[test]
fn an_execution_counter_cannot_be_rewound() {
    let mut core =
        ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
    assert_eq!(core.kernel_variable_mark(), 0);
    assert_eq!(
        core.issued_kernel_variable_bound(),
        ExecutionBudget::KERNEL_VARIABLE_BASE
    );
    assert!(core.advance_kernel_variable_mark(12).is_ok());
    assert!(core.advance_kernel_variable_mark(12).is_ok());
    assert!(core.advance_kernel_variable_mark(30).is_ok());
    assert_eq!(
        core.advance_kernel_variable_mark(29),
        Err("an execution's fresh-variable counter cannot move backwards")
    );
    assert_eq!(core.kernel_variable_mark(), 30);
    assert_eq!(
        core.issued_kernel_variable_bound(),
        ExecutionBudget::KERNEL_VARIABLE_BASE + 30
    );
}

#[test]
fn constructor_partition_reserves_algebraic_variables_in_opaque_environment_terms() {
    use crate::kernel::{AlgebraicTermNode, ExecutionEnvironment, PureFunctionArgument};
    let (core, mut value) = constructor_partition_fixture(2);
    value.node = AlgebraicTermNode::Variable(algebraic_binder(1));
    let function = program_function(
        ProgramType::Int32,
        "opaque_environment",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::ClickFunctionApplication {
                name: "opaque".into(),
                arguments: vec![PureFunctionArgument::Algebraic(value.clone())],
            },
        ))),
    );
    let environment = ExecutionEnvironment::new().with_function(function);
    value.node = AlgebraicTermNode::Variable(Variable(8));
    let (_, fields, _) = core
        .algebraic_case_partition(
            &PureFactStore::default(),
            &value,
            &environment,
            &[],
            None,
            0,
        )
        .unwrap();
    assert!(
        fields
            .iter()
            .flatten()
            .all(|(var, _)| binder_index(var) > 1)
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn constructor_partition_freshness_is_indexed_and_output_linear() {
    for size in [16, 64, 256] {
        let (core, value) = constructor_partition_fixture(2);
        let mut facts = PureFactStore::from_ordered(
            &(0..size)
                .map(|index| Proposition::Predicate {
                    name: format!("ambient{index}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        );
        let environment = crate::kernel::ExecutionEnvironment::new();
        let builds = MATCH_SCOPE_INDEX_BUILDS.with(std::cell::Cell::get);
        let probes = MATCH_FRESHNESS_PROBES.with(std::cell::Cell::get);
        let mut next = 0;
        for _ in 0..size {
            let (partition, fields, successor) = core
                .algebraic_case_partition(&facts, &value, &environment, &[], None, next)
                .unwrap();
            assert_eq!(fields.iter().map(Vec::len).sum::<usize>(), 2);
            facts = facts.with_fact(partition.case_fact(0).unwrap().clone());
            next = successor;
        }
        assert_eq!(
            MATCH_SCOPE_INDEX_BUILDS.with(std::cell::Cell::get) - builds,
            1
        );
        assert_eq!(
            MATCH_FRESHNESS_PROBES.with(std::cell::Cell::get) - probes,
            2 * size + 1
        );
    }
}

#[test]
fn cached_body_loadability_preserves_exact_range_and_state_barriers() {
    let before = SymbolicMemory::new();
    let at = |block: &str| Address::new(block.into(), AddressOffset::constant(0));
    let cached = before.clone().with_seeded_cells(
        at("cache"),
        4,
        crate::kernel::ProgramType::Int32,
        0,
        8,
        crate::kernel::intern_memory_ref(&before),
    );
    let view = |memory, pointer, width, wide| Proposition::MemoryLoadable {
        point: Default::default(),
        memory,
        base: pointer,
        bytes: crate::kernel::StoredMachineTerm::new(
            if wide {
                crate::kernel::MachineIntegerType::UInt64
            } else {
                crate::kernel::MachineIntegerType::Int32
            },
            OldMachineTerm::constant(width),
        ),
        wide,
    };
    let allowed = [view(before.clone(), at("body"), 8, false)]
        .into_iter()
        .collect();
    let check = |fact| cached_body_loadability(&fact, &before, &allowed, &mut HashMap::new());
    assert!(check(view(cached.clone(), at("body"), 8, false)));
    assert!(!check(view(cached.clone(), at("body"), 12, false)));
    assert!(!check(view(cached.clone(), at("other"), 8, false)));
    assert!(!check(view(cached.clone(), at("body"), 8, true)));
    assert!(!check(view(
        cached.clone().store(at("body"), int32(7)),
        at("body"),
        8,
        false
    )));
    let havoc =
        cached.with_call_memory_havoc(Variable(901_020), &[], &PureFactContext::new(), None);
    assert!(!check(view(havoc, at("body"), 8, false)));
    assert!(!check(Proposition::MemoryCanStore {
        point: Default::default(),
        memory: before.clone(),
        pointer: at("body"),
        byte_width: 8
    }));
}

#[test]
fn instance_rewrite_refusal_retains_rejected_and_allowed_facts() {
    use crate::kernel::{
        ComparisonOperator, ResourceFieldSchema, ResourceFieldType, ResourceInstance,
        SpecExpression,
    };
    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(crate::kernel::ProgramType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        InstanceId::from_variable(Variable(901_001)),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![],
        None,
        false,
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::Value(int32(7)),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(7)),
        }],
    )
    .with_instance_schema(Some(schema));
    let selected = ResourceFact::own(Resource::Instance(instance.clone()));
    let before = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = PureFactStore::default();
    let function = program_function(
        crate::kernel::ProgramType::Int32,
        "refusal",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(int32(0))),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let (after, allowed) = crate::kernel::rewrite_resource_instance(
        &before,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let supported = allowed
        .iter()
        .cloned()
        .fold(facts.clone(), |facts, fact| facts.with_fact(fact));
    assert!(
        CheckedResourceRewrite::check_with_children_diagnostic(
            &function,
            &before,
            &facts,
            &selected,
            &after,
            &supported,
            &CheckedCallEvents::default(),
            None,
            &[]
        )
        .is_ok()
    );
    let rejected = Proposition::Predicate {
        name: "unsupported_fact".into(),
        arguments: vec![],
    };
    let unsupported = supported.with_fact(rejected.clone());
    let error = CheckedResourceRewrite::check_with_children_diagnostic(
        &function,
        &before,
        &facts,
        &selected,
        &after,
        &unsupported,
        &CheckedCallEvents::default(),
        None,
        &[],
    )
    .err()
    .expect("unsupported facts must still be rejected");
    assert_eq!(
        error.message,
        "instance rewrite introduced an unchecked fact"
    );
    let retained = error
        .rejected_fact
        .expect("the comparison must survive the refusal");
    assert_eq!(retained.rejected, rejected);
    assert!(!retained.allowed.is_empty());
    for fact in allowed {
        assert!(retained.allowed.contains(&fact));
    }
}

fn returned_proposition_trace(
    state: &ExecutionState,
    facts: &PureFactStore,
) -> (ProgramFunction, Vec<CheckedExecutionEvent>) {
    let statement = ProgramStatement::Return(ProgramExpression::Value(int32(0)));
    let function = program_function(ProgramType::Int32, "test", vec![], statement.clone());
    let events = vec![
        CheckedExecutionEvent::Statement(Theorem::new(Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state.clone()),
            },
        })),
        CheckedExecutionEvent::Context(Box::new(facts.assumptions().clone())),
    ];
    (function, events)
}

#[test]
fn return_proof_publication_shares_candidate_fact_and_effect_objects() {
    for size in [4, 64, 1024] {
        let facts: ExecutionFacts = (0..size)
            .map(|index| {
                ExecutionPureFact::new(Proposition::condition_is(
                    crate::kernel::OldConditionTerm::equal(
                        crate::kernel::OldMachineTerm::Variable(crate::kernel::Variable(index)),
                        crate::kernel::OldMachineTerm::constant(0),
                    ),
                    false,
                ))
            })
            .collect();
        let state = ExecutionState::new();
        let effects: ExecutionFacts = [ExecutionPureFact::certified(
            Proposition::MemoryMutatesOnly {
                before_point: Default::default(),
                after_point: Default::default(),
                before: state.memory().clone(),
                after: state.memory().clone(),
                writes: vec![],
            },
        )]
        .into();
        let candidate = crate::kernel::FunctionExecutionCandidate {
            data: Arc::new(crate::kernel::FunctionExecutionCandidateData {
                completion_delta: None,
                outcome: Arc::new(FunctionOutcome::Return {
                    value: int32(0).into(),
                    state: Box::new(state.clone()),
                }),
                facts: facts.clone(),
                effect_facts: effects.clone(),
                effects_public_first: true,
                obligations: Arc::new(vec![]),
                borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
            }),
        };
        let context = CheckedReturnContext::from_candidate(
            StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state),
            },
            &candidate,
        );
        assert_eq!(context.facts.len(), size as usize + 1);
        for (original, retained) in facts.iter().zip(&context.facts) {
            assert!(std::ptr::eq(original, retained));
        }
        assert!(std::ptr::eq(&effects[0], &context.facts[size as usize]));
        assert!(context.facts[size as usize].is_certified());
        drop(candidate);
        drop(facts);
        drop(effects);
        assert_eq!(context.facts.len(), size as usize + 1);
    }
}

fn returned_proposition_context(state: &ExecutionState) -> Arc<CheckedReturnContext> {
    Arc::new(CheckedReturnContext {
        origin: StatementOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state.clone()),
        },
        published: FunctionOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state.clone()),
        },
        facts: ExecutionFacts::new(),
    })
}

fn returned_proposition_event(
    context: &Arc<CheckedReturnContext>,
    state: &ExecutionState,
    base: &PureFactStore,
    roots: &PureFactStore,
    proposition: Proposition,
) -> CheckedExecutionEvent {
    CheckedExecutionEvent::ReturnProposition(Box::new(CheckedReturnProposition {
        base: base.clone(),
        context: context.clone(),
        proof: super::super::CheckedProposition::new(
            proposition,
            roots.clone(),
            Some(super::super::OutcomeProofCore {
                publication: None,
                identity: super::super::OutcomeIdentity::fresh(),
                result: int32(0).into(),
                state: state.clone().into(),
                store_consequences_available: false,
                is_exceptional: false,
                effect_facts: ExecutionFacts::new().into(),
            }),
            None,
            None,
        ),
    }))
}

#[test]
fn return_proposition_rejects_sibling_assumptions_and_other_memory() {
    let fact = Proposition::condition_is(
        crate::kernel::OldConditionTerm::equal(
            OldMachineTerm::Variable(Variable(42)),
            OldMachineTerm::constant(0),
        ),
        true,
    );
    let state = ExecutionState::new();
    let empty = PureFactStore::default();
    let sibling = empty.clone().with_fact(fact.clone());
    let (function, original) = returned_proposition_trace(&state, &empty);
    let context = returned_proposition_context(&state);
    for base in [&empty, &sibling] {
        let mut events = original.clone();
        events.push(returned_proposition_event(
            &context,
            &state,
            base,
            &sibling,
            fact.clone(),
        ));
        assert_eq!(
            trace_completion(&function, &events, empty.assumptions(), false).err(),
            Some("return proof assumes an unjustified path fact")
        );
        let mut refused = None;
        assert_eq!(
            trace_completion_from_entry(
                &function,
                &events,
                empty.assumptions(),
                false,
                None,
                &mut refused,
            )
            .err(),
            Some("return proof assumes an unjustified path fact"),
        );
        assert_eq!(refused.as_ref(), Some(&fact));
    }
    let (function, mut events) = returned_proposition_trace(&state, &sibling);
    let mut other_state = state.clone();
    other_state.memory = SymbolicMemory::new().with_block("other_memory_state", 4);
    let other_context = returned_proposition_context(&other_state);
    let wrong_state =
        returned_proposition_event(&other_context, &other_state, &sibling, &sibling, fact);
    let CheckedExecutionEvent::ReturnProposition(retained) = &wrong_state else {
        unreachable!()
    };
    assert!(CheckedReturnProposition::check(retained.proof.clone(), &sibling, context,).is_err());
    events.push(wrong_state);
    assert_eq!(
        trace_completion(&function, &events, sibling.assumptions(), false).err(),
        Some("return proof belongs to a different execution path")
    );
}

#[test]
fn return_proposition_checks_resource_compositions_without_granting_ownership() {
    let state = ExecutionState::new();
    let base = PureFactStore::default();
    let context = returned_proposition_context(&state);
    for overlaps in [false, true] {
        let pointer = crate::kernel::Address::symbolic(Variable(42));
        let fact = Proposition::ResourceComposition(ResourceContext::new().unchecked_with_facts([
            ResourceFact::own_memory(crate::kernel::MemoryRange::new(
                pointer.clone(),
                0.into(),
                1.into(),
            )),
            ResourceFact::own_memory(crate::kernel::MemoryRange::new(
                pointer,
                if overlaps { 0.into() } else { 1.into() },
                2.into(),
            )),
        ]));
        let roots = base.clone().with_fact(fact.clone());
        let (function, mut events) = returned_proposition_trace(&state, &base);
        events.push(returned_proposition_event(
            &context, &state, &base, &roots, fact,
        ));
        let result = trace_completion(&function, &events, base.assumptions(), false);
        if overlaps {
            assert_eq!(
                result.err(),
                Some("return proof assumes an unjustified path fact")
            );
        } else {
            let (StatementOutcome::Return { state: after, .. }, _, _) = result.unwrap() else {
                panic!("expected a returned state");
            };
            assert_eq!(after.resources(), state.resources());
        }
    }
}

#[test]
fn return_proposition_accepts_materialized_reads_without_widening_or_value_facts() {
    let pointer = Address::symbolic(Variable(42));
    let memory = SymbolicMemory::new().store(pointer.clone(), int32(7));
    let state = ExecutionState::new().with_memory(memory.clone());
    let empty = PureFactStore::default();
    let (function, original) = returned_proposition_trace(&state, &empty);
    let context = returned_proposition_context(&state);
    let read = |memory, base, bytes: OldMachineTerm| Proposition::MemoryLoadable {
        point: Default::default(),
        memory,
        base,
        bytes: (bytes).into(),
        wide: false,
    };
    let valid = read(memory.clone(), pointer.clone(), OldMachineTerm::constant(4));
    let bad_value = Proposition::condition_is(
        crate::kernel::OldConditionTerm::equal(
            OldMachineTerm::Variable(Variable(43)),
            OldMachineTerm::constant(7),
        ),
        true,
    );
    let cases = [
        (valid, true),
        (
            read(memory.clone(), pointer.clone(), OldMachineTerm::constant(8)),
            false,
        ),
        (
            read(
                memory.clone(),
                Address::symbolic(Variable(44)),
                OldMachineTerm::constant(4),
            ),
            false,
        ),
        (
            read(
                SymbolicMemory::new(),
                pointer.clone(),
                OldMachineTerm::constant(4),
            ),
            false,
        ),
        (
            read(
                memory.without_local_block(&pointer.base),
                pointer,
                OldMachineTerm::constant(4),
            ),
            false,
        ),
        (bad_value, false),
    ];
    for (fact, accepted) in cases {
        let roots = empty.clone().with_fact(fact.clone());
        let mut events = original.clone();
        events.push(returned_proposition_event(
            &context, &state, &empty, &roots, fact,
        ));
        let result = trace_completion(&function, &events, empty.assumptions(), false);
        assert_eq!(result.is_ok(), accepted);
        if let Ok((StatementOutcome::Return { state: after, .. }, _, _)) = result {
            assert_eq!(after.resources(), state.resources());
            assert_eq!(after.memory(), state.memory());
        }
    }
}

/// A certified store's loadability fact names the stored cell's own
/// width, so return certification accepts it as that materialized read.
/// A pointer cell is eight bytes; a four-byte fact over it was refused as
/// an unjustified path fact once a post-return `have` imported it.
#[test]
fn return_proposition_accepts_the_store_loadability_of_a_pointer_cell() {
    let pointer = Address::symbolic(Variable(42));
    let value = ProgramValue::pointer(Address::symbolic(Variable(43)));
    let memory = SymbolicMemory::new().store(pointer.clone(), value.clone());
    let state = ExecutionState::new().with_memory(memory.clone());
    let empty = PureFactStore::default();
    let store = crate::kernel::ExecutionPureFact::certified_store(
        SymbolicMemory::new(),
        Default::default(),
        crate::kernel::ProgramPoint::of_memory(&memory),
        pointer,
        value,
        None,
    );
    let [fact]: [Proposition; 1] = crate::kernel::certified_store_loadability_facts(&vec![store])
        .try_into()
        .expect("one loadability fact");
    let (function, mut events) = returned_proposition_trace(&state, &empty);
    let context = returned_proposition_context(&state);
    let roots = empty.clone().with_fact(fact.clone());
    events.push(returned_proposition_event(
        &context, &state, &empty, &roots, fact,
    ));
    assert!(trace_completion(&function, &events, empty.assumptions(), false).is_ok());
}

#[test]
fn return_argument_facts_require_an_ordinary_positive_or_viewed_resource() {
    use crate::kernel::{ComparisonOperator, SpecExpression, SpecProposition, program_parameter};
    let value = ProgramValue::Int32(OldMachineTerm::Variable(Variable(42)));
    let fact = Proposition::condition_is(
        crate::kernel::OldConditionTerm::signed_less_equal(
            1.into(),
            OldMachineTerm::Variable(Variable(42)),
        ),
        true,
    );
    let definition = CompositeResourceDefinition::new(
        "positive",
        vec![program_parameter("n", ProgramType::Int32)],
        None,
        false,
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::Value(int32(1)),
            operator: ComparisonOperator::LessEqual,
            right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "n",
            )),
        }],
    );
    let owned = ResourceFact::own_composite("positive".into(), vec![value.clone()]);
    let viewed = ResourceFact::view_composite("positive".into(), vec![value]);
    let zero = ResourceFact::Own(owned.resource().clone(), Box::new(0.into()));
    for (resource, authorized, accepted) in [
        (Some(owned.clone()), false, true),
        (Some(viewed), false, true),
        (Some(zero), false, false),
        (None, false, false),
        (Some(owned), true, false),
    ] {
        let resources = resource
            .into_iter()
            .fold(ResourceContext::new(), |r, fact| {
                r.unchecked_with_fact(fact)
            });
        let state = ExecutionState::new().with_resource_context(resources);
        let empty = PureFactStore::default();
        let roots = empty.with_fact(fact.clone());
        let (function, mut events) = returned_proposition_trace(&state, &empty);
        let function = function.with_composite_resource_definitions(vec![
            definition.clone().with_authorized(authorized),
        ]);
        let context = returned_proposition_context(&state);
        events.push(returned_proposition_event(
            &context,
            &state,
            &empty,
            &roots,
            fact.clone(),
        ));
        let result = trace_completion(&function, &events, empty.assumptions(), false);
        assert_eq!(result.is_ok(), accepted);
        if let Ok((StatementOutcome::Return { state: after, .. }, _, _)) = result {
            assert_eq!(after.resources(), state.resources());
        }
    }
}

#[test]
fn return_argument_facts_do_not_project_mutable_memory_invariants() {
    use crate::kernel::{
        ComparisonOperator, MemorySegment, SpecExpression, SpecProposition, program_parameter,
    };
    let pointer = Address::symbolic(Variable(42));
    let held = ResourceFact::own_composite(
        "cell".into(),
        vec![ProgramValue::typed_pointer(
            pointer.clone(),
            ProgramType::Int32Pointer,
        )],
    );
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::index(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(7)),
        }],
    );
    assert!(
        crate::kernel::functions::evaluate_composite_resource_fact_propositions(
            &held,
            std::slice::from_ref(&definition),
            &SymbolicMemory::new(),
            &ResourceContext::new(),
            &PureFactContext::new().require_owned_expression_loads()
        )
        .is_none()
    );
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().store(pointer, int32(9)))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(held));
    let empty = PureFactStore::default();
    let false_fact = Proposition::condition_is(
        crate::kernel::OldConditionTerm::equal(9.into(), 7.into()),
        true,
    );
    let roots = empty.with_fact(false_fact.clone());
    let (function, mut events) = returned_proposition_trace(&state, &empty);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let context = returned_proposition_context(&state);
    events.push(returned_proposition_event(
        &context, &state, &empty, &roots, false_fact,
    ));
    assert!(trace_completion(&function, &events, empty.assumptions(), false).is_err());
}

#[test]
fn return_composite_presentations_reject_other_execution_paths() {
    let before = ExecutionState::new();
    let selected = ResourceFact::own_composite("empty".into(), vec![]);
    let after = before
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = PureFactStore::default();
    let definition = CompositeResourceDefinition::new("empty", vec![], None, false, vec![], vec![]);
    let (function, events) = returned_proposition_trace(&before, &facts);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let checked = CheckedResourceRewrite::check_with_children(
        &function,
        &before,
        &facts,
        &selected,
        &after,
        &facts,
        &CheckedCallEvents::default(),
        None,
    )
    .unwrap();
    let mut rewrite = checked.clone();
    rewrite.return_presentation = Some(Arc::new(CheckedReturnPresentation {
        published_facts: Vec::new(),
        context: returned_proposition_context(&before),
        selected,
        rewrite: checked,
    }));
    let check_trace = |rewrite| {
        let mut trace = events.clone();
        trace.push(CheckedExecutionEvent::ResourceRewrite(rewrite));
        trace_completion(&function, &trace, facts.assumptions(), false)
    };
    assert!(check_trace(Box::new(rewrite.clone())).is_ok());
    Arc::make_mut(rewrite.return_presentation.as_mut().unwrap()).context =
        returned_proposition_context(
            &before.with_memory(SymbolicMemory::new().with_block("other", 4)),
        );
    assert_eq!(
        check_trace(Box::new(rewrite)).err(),
        Some("return composite presentation belongs to a different execution path")
    );
}

pub(super) fn bound_return_producer() -> (ExecutionProofCore, ProgramFunction, PureFactStore) {
    let state = ExecutionState::new();
    let facts = PureFactStore::from_ordered(&[Proposition::condition_is(
        crate::kernel::OldConditionTerm::Constant(true),
        true,
    )]);
    let (function, events) = returned_proposition_trace(&state, &facts);
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    let mut trace = ExecutionEvidence::default();
    for event in events {
        trace.push(event);
    }
    core.execution_evidence = vec![trace].into();
    core.evidence_completed = true;
    let candidates = crate::kernel::program_function_execution_candidates_from_outcomes(
        state.clone(),
        function.clone(),
        vec![],
        vec![(
            FunctionOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state),
            },
            vec![],
            vec![],
        )],
    );
    let execution = core
        .checked_function_execution(
            &candidates,
            &function,
            facts.assumptions().clone(),
            crate::kernel::ExecutionEnvironment::new(),
            crate::kernel::ExecutionSemantics::APPLY_VERIFIED_RULES,
            crate::kernel::FunctionContractExecutionMode::VerifyLoops,
        )
        .unwrap();
    core.open_return_outcome(0, &execution.open_outcome(0).unwrap(), &facts);
    (core, function, facts)
}

#[test]
fn return_producer_rejects_foreign_fact_lineage_at_the_operation() {
    let (mut core, _, facts) = bound_return_producer();
    let sibling = PureFactStore::from_ordered(&[Proposition::condition_is(
        crate::kernel::OldConditionTerm::Constant(false),
        true,
    )]);
    assert!(core.retain_return_facts(0, &sibling).is_err());
    assert!(
        core.retain_return_facts(0, &facts).is_ok(),
        "a refused operation does not change the producer"
    );
    core.execution_evidence[0].events = Default::default();
    assert!(
        core.return_producers.get(&0).unwrap().finish().is_ok(),
        "publication uses the checked completion, not the C event history"
    );
}

#[test]
fn return_resource_observations_construct_successors_and_reject_other_paths() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance};
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        InstanceId::from_variable(Variable(1)),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new("cell", vec![], None, false, vec![], vec![])
        .with_instance_schema(Some(schema));
    let selected = ResourceFact::own(Resource::Instance(instance.clone()));
    let before = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = PureFactStore::default();
    let (after, _) = crate::kernel::rewrite_resource_instance(
        &before,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let (function, events) = returned_proposition_trace(&before, &facts);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let mut core = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let mut trace = ExecutionEvidence::default();
    for event in &events {
        trace.push(event.clone());
    }
    core.execution_evidence = vec![trace].into();
    core.evidence_completed = true;
    let candidates = crate::kernel::program_function_execution_candidates_from_outcomes(
        before.clone(),
        function.clone(),
        vec![],
        vec![(
            FunctionOutcome::Return {
                value: int32(0).into(),
                state: Box::new(before.clone()),
            },
            vec![],
            vec![],
        )],
    );
    let execution = core
        .checked_function_execution(
            &candidates,
            &function,
            facts.assumptions().clone(),
            crate::kernel::ExecutionEnvironment::new(),
            crate::kernel::ExecutionSemantics::APPLY_VERIFIED_RULES,
            crate::kernel::FunctionContractExecutionMode::VerifyLoops,
        )
        .unwrap();
    core.open_return_outcome(0, &execution.open_outcome(0).unwrap(), &facts);
    core.return_proof_contexts = core
        .return_proof_contexts
        .with_inserted(0, returned_proposition_context(&before));
    let (produced, produced_facts) = core
        .rewrite_return_resource_instance_with_children(&function, 0, &facts, &instance, true, None)
        .unwrap();
    assert_eq!(produced.state, after);
    assert_eq!(
        produced_facts.introduced_since(&facts).unwrap().len(),
        produced.semantic_facts.len()
    );
    let mut without_history = core.clone();
    without_history.execution_evidence[0].events = Default::default();
    let returned = without_history
        .checked_return_path(0)
        .unwrap_or_else(|error| panic!("{}", error.reason));
    assert!(matches!(returned.path().completion_origin.as_ref(),
        Some(FunctionOutcome::Return { state, .. }) if state.resources() == produced.state.resources()));
    let retained = core.return_resource_rewrites.get(&0).unwrap().to_vec();
    let CheckedExecutionEvent::ResourceRewrite(constructed) = retained.last().unwrap() else {
        panic!("the constructor retains its exchange");
    };
    assert!(matches!(
        constructed
            .after_state
            .resources()
            .instance_consumption(instance.identity()),
        Some(crate::kernel::primitives::InstanceConsumption::Opened { .. })
    ));
    let observation = constructed.return_observation.clone().unwrap();
    assert_eq!(observation.after, produced.state);
    assert_eq!(observation.semantic_facts, produced.semantic_facts);
    let check = |after_facts: &PureFactStore, observation| {
        CheckedResourceRewrite::check_with_return_observation(
            &function,
            &before,
            &facts,
            &selected,
            &after,
            after_facts,
            &CheckedCallEvents::default(),
            None,
            Some(observation),
            &[],
            None,
        )
    };
    let checked = check(&facts, observation.clone()).unwrap();
    let mut valid = events.clone();
    valid.push(CheckedExecutionEvent::ResourceRewrite(Box::new(
        checked.clone(),
    )));
    assert!(trace_completion(&function, &valid, facts.assumptions(), false).is_ok());
    for extra in [
        Proposition::MemoryLoadable {
            point: Default::default(),
            memory: before.memory().clone(),
            base: Address::symbolic(Variable(42)),
            bytes: 4.into(),
            wide: false,
        },
        Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(false), true),
    ] {
        assert!(check(&facts.with_fact(extra), observation.clone()).is_err());
    }
    let mut wrong_path = checked;
    let mut other = before.clone();
    other.memory = SymbolicMemory::new().with_block("other", 4);
    Arc::make_mut(wrong_path.return_observation.as_mut().unwrap()).context =
        returned_proposition_context(&other);
    let mut invalid = events;
    invalid.push(CheckedExecutionEvent::ResourceRewrite(Box::new(wrong_path)));
    assert_eq!(
        trace_completion(&function, &invalid, facts.assumptions(), false).err(),
        Some("return resource observation belongs to a different execution path"),
    );
}

#[test]
fn return_exchange_keeps_the_published_body_state() {
    use crate::kernel::{
        Pointer, ResourceFieldSchema, ResourceFieldType, ResourceInstance, SpecPoint,
    };
    let pointer = Address::symbolic(Variable(810_000));
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        InstanceId::from_variable(Variable(810_001)),
        "observed".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "observed",
        vec![],
        None,
        false,
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                point: SpecPoint::Current,
                pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(Pointer::new(
                    pointer.clone(),
                    ProgramType::Int32Pointer,
                )))),
                value_type: ProgramType::Int32,
                exact: false,
            },
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(7)),
        }],
    )
    .with_instance_schema(Some(schema));
    let physical = ExecutionState::new();
    // Publication may materialize an observed value without modifying the
    // retained execution state. The exchange belongs to that publication.
    let published = physical
        .clone()
        .with_memory(physical.memory().clone().store(pointer, int32(7)));
    let facts = PureFactStore::default();
    assert!(
        crate::kernel::rewrite_resource_instance(
            &physical,
            &instance,
            &definition,
            facts.assumptions(),
            false,
        )
        .is_err()
    );
    let (function, events) = returned_proposition_trace(&physical, &facts);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let mut core = ExecutionProofCore::at_entry(physical.clone(), ExecutionFrontier::default());
    let mut trace = ExecutionEvidence::default();
    for event in events {
        trace.push(event);
    }
    core.execution_evidence = vec![trace].into();
    core.evidence_completed = true;
    let mut context = returned_proposition_context(&physical);
    Arc::make_mut(&mut context).published = FunctionOutcome::Return {
        value: int32(0).into(),
        state: Box::new(published.clone()),
    };
    core.return_proof_contexts = core.return_proof_contexts.with_inserted(0, context);
    let (produced, _) = core
        .rewrite_return_resource_instance_with_children(
            &function, 0, &facts, &instance, false, None,
        )
        .unwrap();
    let events = core.return_resource_rewrites.get(&0).unwrap().to_vec();
    let (outcome, _, _) = trace_completion(&function, &events, facts.assumptions(), false).unwrap();
    let StatementOutcome::Return { state, .. } = outcome else {
        panic!("return expected")
    };
    assert_eq!(state.memory(), physical.memory());
    assert_eq!(state.resources(), produced.state.resources());
}

#[test]
fn return_instance_guard_and_body_cannot_use_sibling_assumptions() {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
        AlgebraicValueType, AlgebraicVariantType, OldConditionTerm, ResourceFieldSchema,
        ResourceFieldType, ResourceInstance, ResourceMatchArm, ResourceMatchBody, Term, Variable,
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Left".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Right".into(),
            fields: vec![],
        },
    ]
    .into();
    let ty = AlgebraicType {
        name: "Case".into(),
        arguments: vec![],
        rigid: false,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Case".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let model = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(43)),
    };
    let schema = ResourceFieldSchema::new(vec![
        (
            "value".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        ),
        ("model".into(), ResourceFieldType::Algebraic(ty.clone())),
    ])
    .unwrap();
    let instance = ResourceInstance::new(
        InstanceId::from_variable(Variable(1)),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into(), AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let word = OldMachineTerm::Variable(Variable(42));
    let guard = OldConditionTerm::equal(word.clone(), OldMachineTerm::constant(0));
    let condition = SpecProposition::Comparison {
        left: SpecExpression::Value(ProgramValue::Int32(word)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(0)),
    };
    for mode in 0..3 {
        let guarded = mode == 0;
        let matched = mode == 2;
        let definition = CompositeResourceDefinition::new(
            "cell",
            vec![],
            guarded.then(|| condition.clone()),
            false,
            vec![],
            if guarded || matched {
                vec![]
            } else {
                vec![condition.clone()]
            },
        )
        .with_instance_schema(Some(schema.clone()))
        .with_resource_match_body(matched.then(|| {
            ResourceMatchBody {
                field_index: 1,
                algebraic_type: ty.clone(),
                arms: ["Left", "Right"]
                    .into_iter()
                    .map(|variant| ResourceMatchArm {
                        children: vec![],
                        variant: variant.into(),
                        bindings: vec![],
                        binding_types: vec![],
                        binding_variables: vec![],
                        contains: vec![],
                        facts: vec![],
                    })
                    .collect(),
            }
        }));
        let selected = ResourceFact::own(Resource::Instance(instance.clone()));
        let before = ExecutionState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
        let case_fact = |variant: &str| {
            Proposition::Equal(
                Term::Algebraic(model.clone().into()),
                Term::Algebraic(
                    AlgebraicTerm {
                        algebraic_type: ty.clone(),
                        node: AlgebraicTermNode::Constructor {
                            variant: variant.into(),
                            fields: vec![],
                        },
                    }
                    .into(),
                ),
            )
        };
        let left = PureFactStore::default().with_fact(if matched {
            case_fact("Left")
        } else {
            Proposition::condition_is(guard.clone(), true)
        });
        let right = PureFactStore::default().with_fact(if matched {
            case_fact("Right")
        } else {
            Proposition::condition_is(guard.clone(), false)
        });
        let (open, _) = crate::kernel::rewrite_resource_instance(
            &before,
            &instance,
            &definition,
            left.assumptions(),
            true,
        )
        .unwrap();
        let statement = ProgramStatement::Return(ProgramExpression::Value(int32(0)));
        let function = program_function(ProgramType::Int32, "test", vec![], statement.clone())
            .with_composite_resource_definitions(vec![definition]);
        let mut core = ExecutionProofCore::at_entry(before, ExecutionFrontier::default());
        let mut trace = ExecutionEvidence::default();
        trace.push(CheckedExecutionEvent::Statement(Theorem::new(
            Proposition::ProgramStatementVerifies {
                state: Box::new(open.clone()),
                statement: Box::new(statement),
                outcome: StatementOutcome::Return {
                    value: int32(0).into(),
                    state: Box::new(open),
                },
            },
        )));
        let (path_facts, rewrite_facts) = if guarded {
            (&left, &right)
        } else {
            (&right, &left)
        };
        trace.push(CheckedExecutionEvent::Context(Box::new(
            path_facts.assumptions().clone(),
        )));
        core.execution_evidence = vec![trace].into();
        core.evidence_completed = true;
        // Even when both guard arms have identical memory, a rewrite checked
        // under a sibling's case cannot certify this path.
        core.record_return_resource_rewrite(&function, 0, rewrite_facts, &selected, rewrite_facts)
            .unwrap();
        let events = core.return_resource_rewrites.get(&0).unwrap().to_vec();
        let expected = if matched {
            "return fold constructor is not justified on this execution path"
        } else if guarded {
            "return fold guard is not justified on this execution path"
        } else {
            "return fold body is not justified on this execution path"
        };
        assert_eq!(
            trace_completion(&function, &events, path_facts.assumptions(), false).err(),
            Some(expected)
        );
    }
}

fn condition_event(
    state: &ExecutionState,
    condition: &ProgramExpression,
    value: bool,
) -> CheckedExecutionEvent {
    CheckedExecutionEvent::Condition(Theorem::new(Proposition::ProgramConditionEvaluates {
        state: Box::new(state.clone()),
        condition: condition.clone(),
        outcome: ConditionOutcome::Value(value),
    }))
}

#[test]
fn checked_call_event_must_name_a_call_introduced_by_its_statement() {
    let assumptions = PureFactContext::new();
    let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let range = MemoryRange::new(
        pointer,
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    );
    let before =
        ExecutionState::new().with_memory(SymbolicMemory::new().with_block("arg-memory", 4));
    let after = before
        .clone()
        .with_memory(before.memory().clone().with_call_memory_havoc(
            crate::kernel::Variable(700),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        ));
    let theorem = Theorem::new(Proposition::ProgramStatementVerifies {
        state: Box::new(before.clone()),
        statement: Box::new(ProgramStatement::Skip),
        outcome: StatementOutcome::Normal(Box::new(after)),
    });
    let views = statement_call_havoc_views(&theorem);
    let [view] = views.as_slice() else {
        panic!("expected one checked call view");
    };
    let valid = CheckedCallEvent::new(view.clone());
    assert!(
        validate_checked_event_shapes(&[
            CheckedExecutionEvent::Statement(theorem.clone()),
            CheckedExecutionEvent::Context(Box::new(PureFactContext::new())),
            CheckedExecutionEvent::Call(valid),
        ])
        .is_ok()
    );

    let unrelated = before.memory().clone().with_call_memory_havoc(
        crate::kernel::Variable(701),
        std::slice::from_ref(&range),
        &assumptions,
        None,
    );
    let unrelated = CheckedCallEvent::new(crate::kernel::intern_memory(unrelated));
    assert_eq!(
        validate_checked_event_shapes(&[
            CheckedExecutionEvent::Statement(theorem),
            CheckedExecutionEvent::Context(Box::new(PureFactContext::new())),
            CheckedExecutionEvent::Call(unrelated),
        ]),
        Err("retained checked-call event is not introduced by its preceding statement")
    );
}

#[test]
fn checked_call_authority_is_path_local_across_forks() {
    let ancestor_view = crate::kernel::intern_memory(SymbolicMemory::new());
    let sibling_view = crate::kernel::intern_memory(
        SymbolicMemory::new().with_block_without_derivation("local:sibling", 4),
    );
    let mut ancestor = CheckedCallEvents::default();
    ancestor.new_event(ancestor_view);
    let mut left_arm = ancestor.clone();
    let right_arm = ancestor;
    let left_only = left_arm.new_event(sibling_view.clone());

    assert!(left_arm.contains(&left_only));
    assert!(left_arm.contains_view(&left_only, &sibling_view));
    assert!(
        !right_arm.contains(&left_only),
        "a registry shared for indexing must not make a sibling event active",
    );
}

#[test]
fn checked_call_view_lookup_does_not_scan_unrelated_events() {
    for event_count in [1usize, 64, 1024] {
        let mut events = CheckedCallEvents::new();
        let mut selected = None;
        for index in 0..event_count {
            let view = crate::kernel::intern_memory(
                SymbolicMemory::new()
                    .with_block_without_derivation(format!("local:call-{index}"), 4),
            );
            let event = events.new_event(view.clone());
            if index + 1 == event_count {
                selected = Some((event, view));
            }
        }
        let (selected_event, selected_view) = selected.expect("the corpus is nonempty");
        CheckedCallEvents::reset_lookup_candidates_for_test();
        let found = events.events_for_view(&selected_view);
        assert_eq!(found.len(), 1);
        assert!(found[0].same_authority(&selected_event));
        assert_eq!(
            CheckedCallEvents::lookup_candidates_for_test(),
            1,
            "exact-view lookup should visit only its indexed event at size {event_count}",
        );
    }
}

#[test]
fn interface_pointer_congruence_preserves_scope_and_read_obligations() {
    let a = Address::symbolic(Variable(95_700));
    let b = Address::symbolic(Variable(95_701));
    let c = Address::symbolic(Variable(95_702));
    let equal = |a: Address, b: Address| {
        Proposition::ConditionIs(
            crate::kernel::StoredConditionTerm::address_equal(&a, &b),
            true,
        )
    };
    let parent = PureFactStore::from_ordered(&[equal(a.clone(), b.clone())]);
    let arm = parent.with_fact(equal(b, c.clone()));
    let goal = equal(a.clone(), c.clone());
    assert!(checked_interface_pointer_equality(&arm, &goal));
    assert!(!checked_interface_pointer_equality(&parent, &goal));
    assert!(!checked_interface_pointer_equality(
        &arm,
        &equal(a.offset_by_bytes(8), c.offset_by_bytes(16))
    ));
    assert!(!checked_interface_pointer_equality(
        &arm,
        &Proposition::And(Box::new(goal.clone()), Box::new(goal))
    ));
    assert!(!checked_interface_pointer_equality(
        &arm,
        &Proposition::MemoryLoadable {
            point: Default::default(),
            memory: SymbolicMemory::new(),
            base: a,
            bytes: (OldMachineTerm::constant(8)).into(),
            wide: false,
        }
    ));
}

#[test]
fn entry_interface_materialization_retains_source_and_does_not_rebind() {
    let caller = ExecutionState::new();
    let function = program_function(
        ProgramType::Int32,
        "entry_interface",
        vec![crate::kernel::program_parameter("n", ProgramType::Int32)],
        ProgramStatement::Return(crate::kernel::program_expression::variable("n")),
    );
    let arguments = [ProgramExpression::Value(int32(7))];
    let bound =
        crate::kernel::program_function_entry_state(&caller, &function, &arguments).unwrap();
    let mut core = ExecutionProofCore::at_entry(caller.clone(), ExecutionFrontier::default());
    assert!(core.materialize_function_entry().is_err());
    core.record_checked_function_entry(&function, &arguments, &bound, PureFactContext::new())
        .unwrap();
    let mut unrelated = core.clone();
    unrelated.evidence_state = Some(ExecutionState::new().with_local("different", int32(1)));
    assert!(unrelated.materialize_function_entry().is_err());
    core.materialize_function_entry().unwrap();
    assert_eq!(&*core.state, &bound);
    assert_eq!(core.reached_state(), &bound);
    assert_eq!(core.current_source(&function), Some(function.body()));
    assert_eq!(core.frontier.execution_start_state.as_ref(), Some(&caller));
    assert!(core.frontier.is_at_function_entry());
    core.materialize_function_entry().unwrap();
    assert_eq!(&*core.state, &bound);
    assert_eq!(core.reached_state(), &bound);
    assert!(core.execution_evidence.iter().all(|trace| trace.is_empty()));
}

#[test]
fn checked_entry_accepts_only_body_annotations_with_identical_entry_metadata() {
    let returned = ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void));
    let condition = ProgramExpression::Value(int32(1));
    let function = program_function(
        ProgramType::Void,
        "entry_annotations",
        Vec::new(),
        crate::kernel::api::program_while(condition.clone(), Vec::new(), returned.clone()),
    );
    let caller = ExecutionState::new();
    let state = crate::kernel::program_function_entry_state(&caller, &function, &[]).unwrap();
    let entry =
        CheckedFunctionEntry::check(&caller, &function, &[], &state, PureFactContext::new())
            .unwrap();
    let annotated = function
        .clone()
        .with_body(crate::kernel::api::program_while(
            condition.clone(),
            vec![Proposition::condition_is(
                crate::kernel::OldConditionTerm::Constant(true),
                true,
            )],
            returned.clone(),
        ));
    assert_ne!(annotated, function);
    assert_eq!(entry.trace_entry_state(&annotated, &[]), Some(&state));
    assert!(
        entry
            .trace_entry_state(&annotated, std::slice::from_ref(&condition))
            .is_none()
    );
    for changed in [
        annotated.clone().with_source_body(returned),
        annotated.clone().with_recursion_measure(vec![
            crate::kernel::RankingComponent::ProgramExpression(condition),
        ]),
        annotated.with_global_variables(vec![crate::kernel::Global::new(
            "g",
            ProgramType::Int32,
            int32(7),
        )]),
    ] {
        assert!(entry.trace_entry_state(&changed, &[]).is_none());
    }
}

#[test]
fn checked_function_entry_rebase_rejects_semantic_memory_and_population_changes() {
    let function = program_function(
        ProgramType::Void,
        "checked_entry",
        Vec::new(),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::authority_control(
        "item",
        Vec::new(),
        None,
        Vec::new(),
        Vec::new(),
    )]);
    let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let caller = ExecutionState::new()
        .with_memory(SymbolicMemory::new().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        ))
        .with_observed_population_family("item");
    let entry_state = crate::kernel::program_function_entry_state(&caller, &function, &[])
        .expect("the empty argument list should bind");
    let checked = CheckedFunctionEntry::check(
        &caller,
        &function,
        &[],
        &entry_state,
        PureFactContext::new(),
    )
    .expect("the exact kernel-computed entry should check");
    let assumptions = PureFactContext::new();

    assert_eq!(
        checked.entry_state_for(&caller, &function, &[], &assumptions),
        Some(entry_state)
    );

    let changed_memory = caller.clone().with_memory(
        SymbolicMemory::new().store(pointer, ProgramValue::Int32(OldMachineTerm::constant(2))),
    );
    assert!(
        checked
            .entry_state_for(&changed_memory, &function, &[], &assumptions)
            .is_none(),
        "a resource rebase must not authorize a changed C memory value"
    );

    let changed_population = caller.with_observed_population_family("other");
    assert!(
        checked
            .entry_state_for(&changed_population, &function, &[], &assumptions)
            .is_none(),
        "a resource rebase must not authorize a changed population observation"
    );
}

#[test]
fn checked_composite_events_reject_forged_resources_facts_memory_and_definitions() {
    let child_spec = ResourceSpec::token(
        ResourceAccessMode::Own,
        "child".to_string(),
        Vec::new(),
        Vec::new(),
    );
    let definition = CompositeResourceDefinition::new(
        "bundle",
        Vec::new(),
        None,
        false,
        vec![child_spec],
        Vec::new(),
    );
    let function = program_function(
        ProgramType::Void,
        "resource_events",
        Vec::new(),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = ResourceFact::own_composite("bundle".to_string(), Vec::new());
    let child = ResourceFact::own_token("child".to_string(), Vec::new());
    let child_view = ResourceFact::view_token("child".to_string(), Vec::new());
    let before = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = PureFactStore::default();

    let observed = before.clone().with_resource_context(
        before
            .resources()
            .clone()
            .unchecked_with_supported_facts(&selected, [child_view.clone()]),
    );
    let observation = CheckedResourceObservation::check(
        &function,
        &before,
        &facts,
        &selected,
        &observed,
        &facts,
        &PersistentOrderedSet::default(),
        &CheckedCallEvents::default(),
    )
    .expect("the exact one-layer child view should check");

    let untracked_observation = before.clone().with_resource_context(
        before
            .resources()
            .clone()
            .unchecked_with_fact(child_view.clone()),
    );
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &untracked_observation,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation evidence must retain the owned support relation"
    );

    let forged_resource = observed.clone().with_resource_context(
        observed
            .resources()
            .clone()
            .unchecked_with_fact(ResourceFact::view_token("forged".to_string(), Vec::new())),
    );
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &forged_resource,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not invent an unrelated child view"
    );
    let forged_fact = facts.with_fact(Proposition::condition_is(
        crate::kernel::OldConditionTerm::Constant(false),
        true,
    ));
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &observed,
            &forged_fact,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not invent an unrelated pure fact"
    );
    let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let changed_memory = observed.clone().with_memory(
        SymbolicMemory::new().store(pointer, ProgramValue::Int32(OldMachineTerm::constant(1))),
    );
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &changed_memory,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not change C memory"
    );

    let unfolded = before
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(child.clone()));
    CheckedResourceRewrite::check(
        &function,
        &before,
        &facts,
        &selected,
        &unfolded,
        &facts,
        &CheckedCallEvents::default(),
    )
    .expect("the exact folded-to-body representation change should check");
    let variable = OldMachineTerm::Variable(Variable(400));
    let strong = Proposition::condition_is(
        crate::kernel::OldConditionTerm::signed_greater_than(
            variable.clone(),
            OldMachineTerm::constant(0),
        ),
        true,
    );
    let weak = Proposition::condition_is(
        crate::kernel::OldConditionTerm::signed_greater_equal(
            variable,
            OldMachineTerm::constant(0),
        ),
        true,
    );
    let premise = facts.with_fact(strong);
    let derivable_delta = premise.with_fact(weak.clone());
    assert!(crate::kernel::search::ProofSearch::proves(
        premise.assumptions(),
        &weak
    ));
    assert!(!premise.assumptions().proves_exact(&weak));
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &premise,
            &selected,
            &observed,
            &derivable_delta,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not discover an unrecorded implication"
    );

    let changed_definition = program_function(
        ProgramType::Void,
        "resource_events",
        Vec::new(),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "bundle",
        Vec::new(),
        None,
        false,
        Vec::new(),
        Vec::new(),
    )]);
    assert!(
        !changed_definition
            .composite_resource_definitions()
            .contains(
                observation
                    .definition()
                    .expect("legacy body observation has a definition")
            ),
        "a retained observation must remain tied to its checked definition"
    );
}

#[test]
fn checked_join_effects_require_exact_arm_deltas_and_summarize_alternatives() {
    let before = ExecutionState::new();
    let left_pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let right_pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(4));
    let left = before.clone().with_memory(
        before
            .memory()
            .clone()
            .store(left_pointer.clone(), crate::kernel::int64(1)),
    );
    let right = before.clone().with_memory(
        before
            .memory()
            .clone()
            .store(right_pointer.clone(), int32(2)),
    );
    let left_effect = ExecutionPureFact::certified(Proposition::MemoryMutatesOnly {
        before_point: Default::default(),
        after_point: Default::default(),
        before: before.memory().clone(),
        after: left.memory().clone(),
        writes: vec![(left_pointer.clone(), crate::kernel::AccessExtent::from(8))],
    });
    let right_effect = ExecutionPureFact::certified(Proposition::MemoryMutatesOnly {
        before_point: Default::default(),
        after_point: Default::default(),
        before: before.memory().clone(),
        after: right.memory().clone(),
        writes: vec![(right_pointer.clone(), crate::kernel::AccessExtent::from(4))],
    });
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let mut left_core = parent.clone();
    left_core.state = left.clone().into();
    left_core.effect_facts.push(left_effect.clone());
    let mut right_core = parent.clone();
    right_core.state = right.clone().into();
    right_core.effect_facts.push(right_effect.clone());

    assert!(!arm_effect_deltas_are_exact(
        &parent,
        [&left_core, &right_core],
        [&[], &[]],
    ));
    let supplied = [
        std::slice::from_ref(&left_effect),
        std::slice::from_ref(&right_effect),
    ];
    assert!(arm_effect_deltas_are_exact(
        &parent,
        [&left_core, &right_core],
        supplied,
    ));

    let joined = crate::kernel::abstract_execution_state_for_interface_join_across(
        &left,
        &[&left, &right],
        0,
    )
    .expect("alternative memories should have one deterministic abstraction")
    .state;
    let facts = PureFactStore::default();
    let summaries = checked_interface_effect_facts(
        &before,
        &joined,
        [&left_core, &right_core],
        [&facts, &facts],
        supplied,
    )
    .expect("the two exact alternative stores should summarize");
    assert!(matches!(
        summaries.to_vec().as_slice(),
        [fact] if matches!(
            fact.proposition(),
            Proposition::MemoryMutatesOnly { before: effect_before, after, writes, .. }
                if effect_before == before.memory()
                    && after == joined.memory()
                    && writes
                    == &vec![
                        (left_pointer, crate::kernel::AccessExtent::from(8)),
                        (right_pointer, crate::kernel::AccessExtent::from(4)),
                    ]
        )
    ));
}

#[test]
fn checked_interface_effects_reject_uncertified_memory_effects() {
    let before = ExecutionState::new();
    let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let after = before
        .clone()
        .with_memory(before.memory().clone().store(pointer.clone(), int32(1)));
    let effect = ExecutionPureFact::new(Proposition::MemoryMutatesOnly {
        before_point: Default::default(),
        after_point: Default::default(),
        before: before.memory().clone(),
        after: after.memory().clone(),
        writes: vec![(pointer, crate::kernel::AccessExtent::from(4))],
    });
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let mut changed_core = parent.clone();
    changed_core.state = after.clone().into();
    changed_core.effect_facts.push(effect.clone());

    assert_eq!(
        checked_interface_effect_facts(
            &before,
            &after,
            [&changed_core, &parent],
            [&PureFactStore::default(), &PureFactStore::default()],
            [std::slice::from_ref(&effect), &[]],
        ),
        Err("an interface arm contains an uncertified memory effect")
    );
}

#[test]
fn checked_interface_effects_require_memory_diff_coverage() {
    let before = ExecutionState::new();
    let changed_pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(4));
    let declared_pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let after = before.clone().with_memory(
        before
            .memory()
            .clone()
            .store(changed_pointer.clone(), int32(1)),
    );
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());

    let mutation = ExecutionPureFact::certified(Proposition::MemoryMutatesOnly {
        before_point: Default::default(),
        after_point: Default::default(),
        before: before.memory().clone(),
        after: after.memory().clone(),
        writes: vec![(
            declared_pointer.clone(),
            crate::kernel::AccessExtent::from(4),
        )],
    });
    let mut mutation_core = parent.clone();
    mutation_core.state = after.clone().into();
    mutation_core.effect_facts.push(mutation.clone());
    assert_eq!(
        checked_interface_effect_facts(
            &before,
            &after,
            [&mutation_core, &parent],
            [&PureFactStore::default(), &PureFactStore::default()],
            [std::slice::from_ref(&mutation), &[]],
        ),
        Err("an interface arm memory effect does not cover its memory diff")
    );

    let summary = ExecutionPureFact::certified(Proposition::MemoryEffectSummary {
        before_point: Default::default(),
        after_point: Default::default(),
        before: before.memory().clone(),
        after: after.memory().clone(),
        mutable_ranges: vec![MemoryRange::new(
            declared_pointer.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        )],
    });
    let mut summary_core = parent.clone();
    summary_core.state = after.clone().into();
    summary_core.effect_facts.push(summary.clone());
    assert_eq!(
        checked_interface_effect_facts(
            &before,
            &after,
            [&summary_core, &parent],
            [&PureFactStore::default(), &PureFactStore::default()],
            [std::slice::from_ref(&summary), &[]],
        ),
        Err("an interface arm memory effect does not cover its memory diff")
    );

    let erased_before = ExecutionState::new()
        .with_memory(SymbolicMemory::new().store(changed_pointer.clone(), int32(1)));
    let erased_after = erased_before.clone().with_memory(
        erased_before
            .memory()
            .clone()
            .without_cell(&changed_pointer),
    );
    let erased_parent =
        ExecutionProofCore::at_entry(erased_before.clone(), ExecutionFrontier::default());
    let erased_summary = ExecutionPureFact::certified(Proposition::MemoryEffectSummary {
        before_point: Default::default(),
        after_point: Default::default(),
        before: erased_before.memory().clone(),
        after: erased_after.memory().clone(),
        mutable_ranges: vec![MemoryRange::new(
            declared_pointer.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        )],
    });
    let mut erased_core = erased_parent.clone();
    erased_core.state = erased_after.clone().into();
    erased_core.effect_facts.push(erased_summary.clone());
    assert_eq!(
        checked_interface_effect_facts(
            &erased_before,
            &erased_after,
            [&erased_core, &erased_parent],
            [&PureFactStore::default(), &PureFactStore::default()],
            [std::slice::from_ref(&erased_summary), &[]],
        ),
        Err("an interface arm memory effect does not cover its memory diff")
    );
}

#[test]
fn conditional_heap_free_is_checked_as_a_guarded_lifetime_join() {
    let allocation_base = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let before = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_heap_allocation_claim(
                allocation_base.clone(),
                crate::kernel::AllocationSize::int32(16),
            )
            .expect("the allocation claim should be fresh"),
    );
    let freed = before.clone().with_memory(
        before
            .memory()
            .clone()
            .free_heap_block(&allocation_base, &PureFactContext::new())
            .expect("the freed arm should retire the allocation"),
    );
    let retained = before.clone();
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let free_effect = ExecutionPureFact::certified(Proposition::HeapAllocationFreed {
        before_point: Default::default(),
        after_point: Default::default(),
        before: before.memory().clone(),
        after: freed.memory().clone(),
        blocks: vec![(
            allocation_base.clone(),
            crate::kernel::AllocationSize::int32(OldMachineTerm::constant(16)),
        )],
        mutable_ranges: Vec::new(),
    });
    let mut freed_core = parent.clone();
    freed_core.state = freed.clone().into();
    freed_core.effect_facts.push(free_effect.clone());
    let retained_core = parent.clone();
    let siblings = [&freed, &retained];
    let joined =
        crate::kernel::abstract_execution_state_for_interface_join_across(&freed, &siblings, 0)
            .expect("the conditional heap states should abstract")
            .state;
    let facts = PureFactStore::default();
    let summaries = checked_interface_effect_facts(
        &before,
        &joined,
        [&freed_core, &retained_core],
        [&facts, &facts],
        [std::slice::from_ref(&free_effect), &[]],
    )
    .expect("a conditional free should be checked at the branch boundary");
    assert!(summaries.is_empty());

    let function = program_function(
        ProgramType::Void,
        "conditional_heap_free",
        Vec::new(),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    );
    let free_facts = [
        Vec::new(),
        vec![ResourceFact::own_allocation(allocation_base.clone(), 16)],
    ];
    let states = [&freed, &retained];
    assert!(interface_resources_guard_heap_frees(
        &function,
        &free_facts,
        states,
        [&facts, &facts],
        &conditional_heap_frees([std::slice::from_ref(&free_effect), &[],]),
    ));
    assert!(!interface_resources_guard_heap_frees(
        &function,
        &[Vec::new(), Vec::new()],
        states,
        [&facts, &facts],
        &conditional_heap_frees([std::slice::from_ref(&free_effect), &[],]),
    ));
}

#[test]
fn checked_condition_evidence_preserves_the_tail_for_empty_if_arms() {
    let state = ExecutionState::new();
    let condition = ProgramExpression::Variable(("x".to_string()).into());
    let branch = ProgramStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(ProgramStatement::Skip),
        else_branch: Box::new(ProgramStatement::Skip),
    };
    let tail = ProgramStatement::Return(ProgramExpression::Variable(("x".to_string()).into()));
    let source = prepend_checked_evidence_statement(branch, Some(tail.clone()));

    for value in [true, false] {
        let progress = check_evidence_events(
            &[condition_event(&state, &condition, value)],
            state.clone(),
            Some(source.clone()),
        )
        .expect("a checked empty arm should advance directly to the shared tail");
        assert_eq!(progress.state, state);
        assert_eq!(progress.remaining, Some(tail.clone()));
        assert!(progress.completed.is_none());
    }
}

#[test]
fn checked_condition_evidence_rejects_a_different_source_condition() {
    let state = ExecutionState::new();
    let source_condition = ProgramExpression::Variable(("x".to_string()).into());
    let theorem_condition = ProgramExpression::Variable(("y".to_string()).into());
    let source = ProgramStatement::If {
        condition: source_condition,
        then_branch: Box::new(ProgramStatement::Skip),
        else_branch: Box::new(ProgramStatement::Skip),
    };
    assert!(
        check_evidence_events(
            &[condition_event(&state, &theorem_condition, true)],
            state,
            Some(source),
        )
        .is_none()
    );
}

#[test]
fn a_summarized_loop_matches_only_a_less_annotated_source_loop() {
    fn loop_statement(invariant: Vec<Proposition>, body: ProgramStatement) -> ProgramStatement {
        ProgramStatement::Loop {
            test: crate::kernel::LoopTestRegion::expression(
                ProgramExpression::Variable(("c".to_string()).into()),
                crate::kernel::LoopTestPosition::BeforeBody,
            ),
            update: None,
            invariant,
            invariant_checks: Vec::new(),
            effect_checks: Vec::new(),
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            backedge_target: None,
            natural_exit_target: None,
            body: Box::new(body),
        }
    }
    let clause = Proposition::condition_is(
        crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::GreaterEqual,
            left: Box::new(OldMachineTerm::constant(0)),
            right: Box::new(OldMachineTerm::constant(0)),
        },
        true,
    );
    let body = ProgramStatement::Skip;
    let bare = loop_statement(Vec::new(), body.clone());
    let annotated = loop_statement(vec![clause], body.clone());

    // The `loop { ... }` tactic's own clauses may be added to a source
    // loop that carries none: the C program is the same and the theorem
    // discharged more.
    assert!(checked_source_statement_matches(&annotated, &bare));
    assert!(checked_source_statement_matches(&bare, &bare));
    assert!(checked_source_statement_matches(&annotated, &annotated));
    // The reverse would drop an obligation the source asked for.
    assert!(!checked_source_statement_matches(&bare, &annotated));
    // The C itself is still exact.
    assert!(!checked_source_statement_matches(
        &loop_statement(Vec::new(), ProgramStatement::Break),
        &bare
    ));
    let mut other_condition = bare.clone();
    if let ProgramStatement::Loop {
        test: loop_test, ..
    } = &mut other_condition
    {
        *loop_test = crate::kernel::LoopTestRegion::expression(
            ProgramExpression::Variable(("d".to_string()).into()),
            loop_test.position,
        );
    }
    assert!(!checked_source_statement_matches(&other_condition, &bare));
    let mut do_while = bare.clone();
    if let ProgramStatement::Loop {
        test: loop_test, ..
    } = &mut do_while
    {
        loop_test.position = crate::kernel::LoopTestPosition::AfterBody;
    }
    assert!(!checked_source_statement_matches(&do_while, &bare));
    // Only loops have proof clauses; nothing else relaxes.
    assert!(!checked_source_statement_matches(
        &ProgramStatement::Skip,
        &ProgramStatement::Break
    ));
}

#[test]
fn checked_branch_join_accepts_empty_arms_only_at_the_artifact_tail() {
    let function = program_function(
        ProgramType::Void,
        "branch",
        Vec::new(),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    );
    let state = ExecutionState::new();
    let condition = ProgramExpression::Variable(("x".to_string()).into());
    let branch_statement = ProgramStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(ProgramStatement::Skip),
        else_branch: Box::new(ProgramStatement::Skip),
    };
    let continuation = Some(ProgramStatement::Return(ProgramExpression::Variable(
        ("x".to_string()).into(),
    )));
    let then_theorem = match condition_event(&state, &condition, true) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let else_theorem = match condition_event(&state, &condition, false) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let root_facts = PureFactStore::default();
    let split = CheckedBranchSplit {
        state: state.clone(),
        branch_statement,
        continuation,
        condition,
        root_facts: root_facts.clone(),
        paths: vec![
            CheckedBranchPath {
                outcome: ConditionOutcome::Value(true),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: then_theorem.clone(),
            },
            CheckedBranchPath {
                outcome: ConditionOutcome::Value(false),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: else_theorem.clone(),
            },
        ],
    };
    let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    let at_branch = FrontierPosition::StatementEntry {
        remaining: Arc::new(crate::kernel::program_seq(
            split.branch_statement.clone(),
            split.continuation.clone().expect("a continuation"),
        )),
    };
    let mut then_arm = parent.clone();
    then_arm.frontier.position = at_branch.clone();
    then_arm
        .record_condition_transition(
            &function,
            &[],
            then_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the then condition decides the frontier's `if`");
    then_arm.frontier.region = ExecutionRegionKind::BranchArm;
    then_arm.frontier.position = FrontierPosition::RegionBoundary;
    let mut else_arm = parent.clone();
    else_arm.frontier.position = at_branch;
    else_arm
        .record_condition_transition(
            &function,
            &[],
            else_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the else condition decides the frontier's `if`");
    else_arm.frontier.region = ExecutionRegionKind::BranchArm;
    else_arm.frontier.position = FrontierPosition::RegionBoundary;

    let checked = CheckedExecutionBranch::check(
        split.clone(),
        &root_facts,
        [&then_theorem, &else_theorem],
        [&root_facts, &root_facts],
        &parent,
        [&then_arm, &else_arm],
        &function,
        &[],
        [&[], &[]],
    )
    .expect("the exact empty arms should join at the retained continuation");
    assert_eq!(checked.joined_state(), &state);
    // Each empty arm records its condition theorem and the context it
    // was proved under.
    assert_eq!(checked.arm_events(0).len(), 2);
    assert_eq!(checked.arm_events(1).len(), 2);

    assert!(
        CheckedExecutionBranch::check(
            split,
            &root_facts,
            [&else_theorem, &then_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &function,
            &[],
            [&[], &[]],
        )
        .is_err(),
        "swapped arm evidence must not certify the source partition"
    );
}

#[test]
fn branch_split_obligations_require_evidence_on_each_named_arm() {
    use crate::kernel::{OldConditionTerm, ProofObligation};
    let state = ExecutionState::new();
    let condition = ProgramExpression::Value(int32(1));
    let x = OldMachineTerm::Variable(Variable(930_000));
    let strong = Proposition::condition_is(
        OldConditionTerm::signed_greater_than(x.clone(), OldMachineTerm::constant(0)),
        true,
    );
    let required = Proposition::condition_is(
        OldConditionTerm::signed_greater_equal(x, OldMachineTerm::constant(0)),
        true,
    );
    let root = PureFactStore::default().with_fact(strong);
    let theorems = [true, false].map(|value| match condition_event(&state, &condition, value) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    });
    let split = CheckedBranchSplit {
        state: state.clone(),
        branch_statement: ProgramStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(ProgramStatement::Skip),
            else_branch: Box::new(ProgramStatement::Skip),
        },
        continuation: None,
        condition: condition.clone(),
        root_facts: root.clone(),
        paths: [true, false]
            .into_iter()
            .enumerate()
            .map(|(index, value)| CheckedBranchPath {
                outcome: ConditionOutcome::Value(value),
                facts: Vec::new().into(),
                obligations: vec![ProofObligation::new(required.clone())],
                theorem: theorems[index].clone(),
            })
            .collect(),
    };
    let exact = root.with_fact(required);
    let validate = |arms| {
        split.validates_exhaustive_join(
            &state,
            &condition,
            &root,
            [Some(&theorems[0]), Some(&theorems[1])],
            arms,
        )
    };
    assert!(
        !validate([Some(&root), Some(&root)]),
        "general derivability is not retained evidence"
    );
    assert!(
        !validate([Some(&exact), Some(&root)]),
        "then evidence cannot discharge the else obligation"
    );
    assert!(
        !validate([Some(&root), Some(&exact)]),
        "else evidence cannot discharge the then obligation"
    );
    assert!(validate([Some(&exact), Some(&exact)]));
    assert!(
        !validate([Some(&exact), None]),
        "an omitted arm is not exhaustive"
    );
    let unrelated = PureFactStore::default().with_fact(Proposition::condition_is(
        OldConditionTerm::Constant(true),
        true,
    ));
    assert!(
        !validate([Some(&exact), Some(&unrelated)]),
        "evidence must descend from this split root"
    );
}

#[test]
fn interface_logical_read_does_not_establish_validity() {
    use crate::kernel::{Pointer, SpecPoint};
    let state = ExecutionState::new();
    let pointer = Address::new("interface_cell".into(), AddressOffset::constant(0));
    let load = SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(Pointer::new(
            pointer,
            ProgramType::Int32Pointer,
        )))),
        value_type: ProgramType::Int32,
        exact: false,
    };
    let spec = SpecProposition::Comparison {
        left: load.clone(),
        operator: ComparisonOperator::Equal,
        right: load.clone(),
    };
    let path = interface_spec_paths(&spec, &state, &state, &PureFactContext::new())
        .unwrap()
        .remove(0);
    assert!(path.facts.is_empty());
    assert!(path.obligations.is_empty());
    let mut facts = PureFactStore::default().with_fact(path.proposition.clone());
    for fact in &path.facts {
        facts = facts.with_fact(fact.proposition().clone());
    }
    assert!(
        CheckedInterfaceLowering::check(
            &SpecProposition::Defined(load),
            &state,
            &state,
            &facts,
            &InterfaceReadPremises::default(),
        )
        .is_none(),
        "logical reflexivity grants no read validity"
    );
    for obligation in &path.obligations {
        facts = facts.with_fact(obligation.proposition().clone());
    }
    let checked = CheckedInterfaceLowering::check(
        &spec,
        &state,
        &state,
        &facts,
        &InterfaceReadPremises::default(),
    )
    .unwrap();
    assert_eq!(checked.path.as_ref(), &path);
    assert!(checked.has_complete_proof());
    assert_eq!(
        checked.proofs.len(),
        1 + path.facts.len() + path.obligations.len()
    );
    assert!(checked.facts.shares_premises_with(&facts));
    assert_eq!(checked.retained_state, state);
    assert_eq!(checked.reference, state);
    assert_eq!(checked.spec.as_ref(), &spec);
    let copy = checked.clone();
    assert!(Arc::ptr_eq(&copy.path, &checked.path));
    assert!(Arc::ptr_eq(&copy.spec, &checked.spec));
    assert!(Arc::ptr_eq(&copy.proofs, &checked.proofs));
    let mut incomplete = checked.clone();
    incomplete.proofs = Arc::new(checked.proofs[..checked.proofs.len() - 1].to_vec());
    assert!(!incomplete.has_complete_proof());
}

#[test]
fn interface_assertion_requires_an_available_proof_not_derivability() {
    use crate::kernel::OldConditionTerm;
    let term = OldMachineTerm::Variable(Variable(949_000));
    let state = ExecutionState::new().with_local("x", ProgramValue::Int32(term.clone()));
    let spec = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into())),
        operator: ComparisonOperator::GreaterEqual,
        right: SpecExpression::Value(int32(0)),
    };
    let goal = Proposition::condition_is(
        OldConditionTerm::signed_greater_equal(term.clone(), OldMachineTerm::constant(0)),
        true,
    );
    let facts = PureFactStore::default().with_fact(Proposition::condition_is(
        OldConditionTerm::signed_greater_than(term, OldMachineTerm::constant(0)),
        true,
    ));
    assert!(
        crate::kernel::search::ProofSearch::proves(facts.assumptions(), &goal),
        "the removed contextual checker could derive this consequence"
    );
    assert!(
        CheckedInterfaceLowering::check(
            &spec,
            &state,
            &state,
            &facts,
            &InterfaceReadPremises::default()
        )
        .is_none()
    );
    let established = facts.with_fact(goal);
    assert!(
        CheckedInterfaceLowering::check(
            &spec,
            &state,
            &state,
            &established,
            &InterfaceReadPremises::default()
        )
        .unwrap()
        .has_complete_proof()
    );
}

#[test]
fn interface_load_definition_rejects_wrong_variable_address_and_state() {
    use crate::kernel::{Address, OldConditionTerm, SymbolicMemory};
    let memory = crate::kernel::intern_memory(SymbolicMemory::new());
    let pointer = Address::new("interface_definition".into(), AddressOffset::constant(0));
    let variable = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Int32,
    );
    let equation = |variable, memory, pointer| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(variable)),
                right: Box::new(OldMachineTerm::read_named(
                    memory,
                    Box::new(pointer),
                    crate::kernel::LoadKind::Int32,
                )),
            },
            true,
        )
    };
    let correct = equation(
        variable,
        crate::kernel::ProgramPoint::at(&memory),
        pointer.clone(),
    );
    let definition = CheckedInterfaceLoadDefinition::check(&correct).unwrap();
    assert!(definition.matches_goal_exactly(&correct));
    let wrong_variable = equation(
        Variable(17),
        crate::kernel::ProgramPoint::at(&memory),
        pointer.clone(),
    );
    let wrong_address = equation(
        variable,
        crate::kernel::ProgramPoint::at(&memory),
        Address::new("other".into(), AddressOffset::constant(0)),
    );
    let wrong_state = equation(
        variable,
        crate::kernel::ProgramPoint::at(
            &(crate::kernel::intern_memory(SymbolicMemory::new().with_block("different", 4))),
        ),
        pointer,
    );
    for wrong in [wrong_variable, wrong_address, wrong_state] {
        assert!(CheckedInterfaceLoadDefinition::check(&wrong).is_none());
        assert!(!definition.matches_goal_exactly(&wrong));
    }
}

#[test]
fn interface_successor_fact_checks_pay_for_exported_resources_once() {
    use crate::instrumentation::{VerificationEvent, collect, measure_deterministic_work};

    let arm = PureFactStore::default();
    let written = std::collections::BTreeSet::new();
    let assumptions = PureFactContext::new();
    let memory = SymbolicMemory::new();
    for size in [4usize, 16, 64] {
        let ranges = (0..size)
            .map(|index| {
                MemoryRange::new(
                    Address::new(
                        crate::kernel::AddressBase::ExternalArgument,
                        AddressOffset::constant(index as i64 * 8),
                    ),
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(1),
                )
            })
            .collect::<Vec<_>>();
        let intrinsic = ranges
            .iter()
            .map(|range| range.loadable_fact(&memory, Default::default()))
            .collect::<Vec<_>>();
        let exported = ranges
            .into_iter()
            .map(ResourceFact::own_memory)
            .collect::<Vec<_>>();
        let check = |introduced: &[Proposition]| {
            let ((result, work), events) = collect(|| {
                measure_deterministic_work(|| {
                    check_interface_successor_facts(
                        introduced,
                        [&arm, &arm],
                        &written,
                        &exported,
                        &intrinsic,
                        &assumptions,
                    )
                })
            });
            let assemblies = events
                .iter()
                .filter(|event| {
                    matches!(
                        event,
                        VerificationEvent::OperationFinished { name, .. }
                            if name == "branch interface exported composition"
                    )
                })
                .count();
            (result, work, assemblies)
        };
        let (result, intrinsic_work, assemblies) = check(&intrinsic);
        assert!(result.is_ok());
        assert_eq!(assemblies, 0);
        assert!(
            intrinsic_work <= 8 * size,
            "{size} facts used {intrinsic_work} work"
        );

        let resources = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_facts(exported.iter().cloned());
        let mut introduced = intrinsic.clone();
        introduced.extend(resources.observable_facts_assuming_valid(&assumptions));
        assert_eq!(introduced.len(), size + 1);
        let (result, _, assemblies) = check(&introduced);
        assert!(result.is_ok());
        assert_eq!(assemblies, 1);

        let with_unexported = resources
            .unchecked_with_fact(ResourceFact::own_token("unexported".to_owned(), Vec::new()));
        introduced.extend(with_unexported.observable_facts_assuming_valid(&assumptions));
        let (result, _, assemblies) = check(&introduced);
        assert_eq!(
            result,
            Err("the interface successor contains an unchecked new fact")
        );
        assert_eq!(assemblies, 1);
    }
}

#[test]
fn interface_branch_constructs_resources_and_rejects_unproved_facts() {
    let function = program_function(
        ProgramType::Void,
        "interface",
        Vec::new(),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    );
    let state = ExecutionState::new()
        .with_local("x", int32(7))
        .with_local("flag", int32(0));
    let condition = ProgramExpression::Variable(("flag".to_string()).into());
    let branch_statement = ProgramStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(ProgramStatement::Skip),
        else_branch: Box::new(ProgramStatement::Skip),
    };
    let continuation = Some(ProgramStatement::Return(ProgramExpression::Variable(
        ("x".to_string()).into(),
    )));
    let then_theorem = match condition_event(&state, &condition, true) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let else_theorem = match condition_event(&state, &condition, false) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let root_facts = PureFactStore::default();
    let split = CheckedBranchSplit {
        state: state.clone(),
        branch_statement,
        continuation,
        condition,
        root_facts: root_facts.clone(),
        paths: vec![
            CheckedBranchPath {
                outcome: ConditionOutcome::Value(true),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: then_theorem.clone(),
            },
            CheckedBranchPath {
                outcome: ConditionOutcome::Value(false),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: else_theorem.clone(),
            },
        ],
    };
    let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    let at_branch = FrontierPosition::StatementEntry {
        remaining: Arc::new(crate::kernel::program_seq(
            split.branch_statement.clone(),
            split.continuation.clone().expect("a continuation"),
        )),
    };
    let mut then_arm = parent.clone();
    then_arm.frontier.position = at_branch.clone();
    then_arm
        .record_condition_transition(
            &function,
            &[],
            then_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the then condition decides the frontier's `if`");
    then_arm.frontier.region = ExecutionRegionKind::BranchArm;
    then_arm.frontier.position = FrontierPosition::RegionBoundary;
    let mut else_arm = parent.clone();
    else_arm.frontier.position = at_branch;
    else_arm
        .record_condition_transition(
            &function,
            &[],
            else_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the else condition decides the frontier's `if`");
    else_arm.frontier.region = ExecutionRegionKind::BranchArm;
    else_arm.frontier.position = FrontierPosition::RegionBoundary;
    let spec = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(ProgramExpression::Variable(
            ("x".to_string()).into(),
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(ProgramExpression::Variable(
            ("x".to_string()).into(),
        )),
    };
    let checked_fact = interface_spec_paths(&spec, &state, &state, &PureFactContext::new())
        .expect("the simple interface should lower")
        .remove(0)
        .proposition;
    let successor_facts = root_facts.with_fact(checked_fact.clone());

    let checked = CheckedExecutionBranch::construct_interface(
        split.clone(),
        &root_facts,
        [&then_theorem, &else_theorem],
        [&root_facts, &root_facts],
        &parent,
        [&then_arm, &else_arm],
        &function,
        &[],
        std::slice::from_ref(&spec),
        &[],
        [&[], &[]],
        &state,
        &successor_facts,
        None,
    )
    .expect("the exact fact-only abstraction should check");
    assert_eq!(checked.interface_lowerings.len(), 1);
    let retained = &checked.interface_lowerings[0];
    assert!(retained[0].facts.shares_premises_with(&root_facts));
    assert!(retained[1].facts.shares_premises_with(&root_facts));
    assert!(retained[2].facts.shares_premises_with(&successor_facts));
    assert!(
        retained
            .iter()
            .all(|lowering| lowering.path.proposition == checked_fact)
    );
    assert!(checked.matches_interface_resource_definitions(&function));
    let mut stale = checked.clone();
    stale.interface_successor_facts = Some(successor_facts.with_fact(Proposition::Predicate {
        name: "stale".into(),
        arguments: Vec::new(),
    }));
    assert!(!stale.matches_interface_resource_definitions(&function));
    assert_eq!(
        checked
            .interface_execution_facts()
            .iter()
            .map(ExecutionPureFact::proposition)
            .collect::<Vec<_>>(),
        vec![&checked_fact],
        "only the validated successor delta gains execution-fact authority"
    );

    let forged_fact = Proposition::condition_is(
        crate::kernel::OldConditionTerm::signed_less_than(
            OldMachineTerm::constant(1),
            OldMachineTerm::constant(0),
        ),
        true,
    );
    assert!(
        CheckedExecutionBranch::construct_interface(
            split.clone(),
            &root_facts,
            [&then_theorem, &else_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &function,
            &[],
            std::slice::from_ref(&spec),
            &[],
            [&[], &[]],
            &state,
            &successor_facts.with_fact(forged_fact),
            None,
        )
        .is_err(),
        "an unrelated successor fact must not gain interface authority"
    );

    let forged_resource = ResourceFact::own_token("missing".to_string(), Vec::new());
    let forged_state = state
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(forged_resource));
    let constructed = CheckedExecutionBranch::construct_interface(
        split,
        &root_facts,
        [&then_theorem, &else_theorem],
        [&root_facts, &root_facts],
        &parent,
        [&then_arm, &else_arm],
        &function,
        &[],
        std::slice::from_ref(&spec),
        &[],
        [&[], &[]],
        &forged_state,
        &successor_facts,
        None,
    )
    .expect("ownership is derived from the arms, not the proposed state");
    assert!(
        constructed.joined_state.resources().is_empty(),
        "a resource absent from both arms must not gain interface authority"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/tests.rs");
}

#[test]
fn named_pointer_cell_requires_its_complete_read_and_provenance() {
    use crate::kernel::{Address, LoadKind, SymbolicMemory, VerificationSession};
    let _session = VerificationSession::enter();
    let address = Address::symbolic(Variable(986_101));
    let memory = SymbolicMemory::new();
    let name = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory(memory.clone()),
        address.clone(),
        LoadKind::Int32,
    );
    let value = crate::kernel::cell_run_value(ProgramType::Int32Pointer, name.clone());
    assert!(super::cell_value_is_exactly_load(&value, &name));
    let ProgramValue::Pointer(pointer) = value else {
        panic!("pointer cell")
    };
    for wrong in [
        ProgramValue::typed_pointer(
            pointer.address().offset_by_bytes(4),
            ProgramType::Int32Pointer,
        ),
        ProgramValue::typed_pointer(address.clone(), ProgramType::Int32Pointer),
        ProgramValue::Pointer(pointer.clone().with_provenance(address.clone())),
    ] {
        assert!(!super::cell_value_is_exactly_load(&wrong, &name));
    }
    let changed = memory.store(address.offset_by_bytes(4), ProgramValue::Int32(7.into()));
    let next = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory(changed),
        address,
        LoadKind::Int32,
    );
    // Even where the scalar prefix is unchanged, a pointer covers eight bytes.
    let later = crate::kernel::cell_run_value(ProgramType::Int32Pointer, next);
    assert!(!super::cell_value_is_exactly_load(&later, &name));
}

#[test]
fn opened_contract_entry_selects_premises_before_body_execution() {
    use crate::kernel::proof::PropositionSource;
    let state = ExecutionState::new();
    let function = crate::kernel::program_function(
        crate::kernel::ProgramType::Int32,
        "entry_owner",
        vec![],
        crate::kernel::program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Predicate {
            name: "entry_requirement".into(),
            arguments: vec![],
            resource_state_dependent: false,
        }],
        vec![],
        vec![],
        vec![],
        true,
    );
    let environment = crate::kernel::ExecutionEnvironment::new();
    let foreign = Proposition::Predicate {
        name: "not_a_requirement".into(),
        arguments: vec![],
    };
    let contract = crate::kernel::program_function_contract_entry(&state, &function, &[]).unwrap();
    let requirement = contract
        .facts()
        .iter()
        .find(|fact| {
            matches!(
                fact.origin(),
                crate::kernel::ContractEntryFactOrigin::Requirement(0)
            )
        })
        .expect("the declared requirement is an entry fact")
        .proposition()
        .clone();
    let opened = OpenedContractEntry::open(
        &state,
        &function,
        &[],
        &vec![foreign.clone(), requirement.clone(), requirement.clone()],
        &environment,
    )
    .unwrap();
    assert!(opened.facts().contains(&requirement));
    let admitted = opened.facts().propositions().zip(opened.source_origins());
    assert_eq!(
        admitted
            .filter(|(fact, _)| **fact == requirement)
            .map(|(_, origin)| *origin)
            .collect::<Vec<_>>(),
        vec![Some(OpenedEntryFactSource::SourceFact(1))]
    );
    assert!(!opened.facts().contains(&foreign));
    assert!(opened.facts().contains(&environment.byte_order_fact()));
    assert_eq!(
        opened.facts().propositions().count(),
        opened.source_origins().len()
    );
    let entry = opened.entry.clone();
    let facts = opened.facts.clone();
    let core = opened.into_execution_core();
    assert!(Arc::ptr_eq(core.function_entry.as_ref().unwrap(), &entry));
    assert_eq!(&*core.state, &state);
    assert!(
        core.entry_facts_at_entry()
            .unwrap()
            .contains(&environment.byte_order_fact())
    );
    assert_eq!(
        facts.assumptions(),
        core.function_entry.as_ref().unwrap().assumptions()
    );
    assert!(
        OpenedContractEntry::open(
            &state,
            &function,
            &[crate::kernel::program_expression::variable(
                "not_a_bound_argument"
            )],
            &Vec::<Proposition>::new(),
            &environment,
        )
        .is_err(),
        "invalid argument binding fails before a body proof exists"
    );
}

#[test]
fn branch_interface_comparisons_retain_exact_shared_source_authority() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{
        KernelTermExport, KernelTermImport, MachineBinaryOp, MachineOperandView, OldConditionTerm,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |id| OldMachineTerm::Variable(Variable(id));
        let expression = OldMachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: Box::new(variable(919001)),
            right: Box::new(variable(919002)),
        };
        let root = KernelTermImport::default()
            .machine_arithmetic(format, &expression)
            .unwrap();
        let right = variable(919003);
        let observed = |relation| {
            condition_for_operand_views(
                format,
                relation,
                [
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Old(&right),
                ],
            )
        };
        for relation in [
            CompareRelation::Equal,
            CompareRelation::LessThan,
            CompareRelation::GreaterEqual,
        ] {
            for truth in [false, true] {
                let source = Proposition::condition_is(
                    OldConditionTerm::machine_compare(
                        format,
                        relation,
                        expression.clone(),
                        right.clone(),
                    ),
                    truth,
                );
                let goal = Proposition::condition_is(observed(relation), truth);
                let empty = PureFactStore::default();
                let facts = empty.with_fact(source.clone());
                let exports = KernelTermExport::machine_export_count();
                assert!(checked_branch_fact_is_available(&facts, &goal));
                assert!(!checked_branch_fact_is_available(&empty, &goal));
                assert!(!checked_branch_fact_is_available(
                    &facts,
                    &Proposition::condition_is(observed(relation), !truth)
                ));
                assert!(facts.contains(&source));
                assert!(!facts.contains(&goal));
                if relation == CompareRelation::LessThan && truth {
                    assert!(!checked_branch_fact_is_available(
                        &facts,
                        &Proposition::condition_is(observed(CompareRelation::LessEqual), true)
                    ));
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }
}

#[test]
fn common_arm_effects_read_only_the_two_deltas() {
    use crate::kernel::execution_facts::take_fact_reads;

    let fact = |number| Proposition::Predicate {
        name: format!("arm_effect_{number}"),
        arguments: vec![],
    };
    let retained = ExecutionPureFact::certified(fact(0));
    for size in [4, 16, 64, 256] {
        let left: ExecutionFacts = std::iter::once(retained.clone())
            .chain((1..=size).map(|number| ExecutionPureFact::certified(fact(number))))
            .collect();
        let right: ExecutionFacts = (1..=size)
            .map(|number| ExecutionPureFact::new(fact(number)))
            .chain(std::iter::once(retained.clone()))
            .collect();
        take_fact_reads();
        let (common, work) = crate::instrumentation::measure_deterministic_work(|| {
            common_non_memory_effect_facts([&left, &right])
        });
        let reads = take_fact_reads();
        assert_eq!(common.to_vec(), vec![retained.clone()]);
        assert_eq!(work, size + 1);
        assert!(
            reads <= 2 * (size + 1),
            "read {reads} facts for {size} effects"
        );
    }
}

#[test]
fn retained_condition_theorem_preserves_the_standalone_premises() {
    let ambient = PureFactContext::new()
        .assume_condition(crate::kernel::OldConditionTerm::Constant(true), true)
        .assume_proposition(Proposition::Predicate {
            name: "ambient".into(),
            arguments: vec![],
        });
    let state = ExecutionState::new();
    let condition = ProgramExpression::Value(crate::kernel::int32(1));
    let evaluation = crate::kernel::prove_symbolic_program_condition_evaluation(
        state.clone(),
        condition.clone(),
        ambient.clone(),
    );
    let [path] = evaluation.paths() else {
        panic!("constant condition must have one path");
    };
    let conclusion = Proposition::ProgramConditionEvaluates {
        state: Box::new(state),
        condition,
        outcome: ConditionOutcome::Value(true),
    };
    assert_eq!(path.theorem().execution_conclusion(), &conclusion);
    let premises = crate::kernel::reasoning::path_facts::wrap_proof_facts(
        conclusion,
        &ambient,
        path.facts(),
        path.obligations(),
    );
    let standalone = Theorem::new(premises.clone());
    assert_eq!(path.theorem().proposition(), &premises);
    assert_eq!(path.theorem(), &standalone);
    assert_eq!(path.theorem().cmp(&standalone), std::cmp::Ordering::Equal);
}

#[test]
fn resource_cell_naming_checks_the_recorded_integer_version_after_forgetting_a_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address::new(
        crate::kernel::AddressBase::ExternalArgument,
        AddressOffset::constant(0),
    );
    let start = ExecutionState::new().with_memory(SymbolicMemory::new().with_block("other", 4));
    let without_name = || {
        let stored = start.clone().with_memory(
            start
                .memory()
                .clone()
                .store(slot.clone(), ProgramValue::Int32(7u32.into())),
        );
        let forgotten =
            stored
                .memory()
                .without_possible_aliasing_cells(&slot, 4, &PureFactContext::new());
        stored.with_memory(forgotten)
    };
    let before = without_name();
    assert!(before.memory().known_value(&slot).is_none());
    let point = before.program_point();
    let version = point
        .indexed_integer_version(&slot, LoadKind::Int32)
        .unwrap();
    let named =
        before
            .memory()
            .clone()
            .materialize_cell_at(slot.clone(), ProgramType::Int32, &point);
    assert_eq!(
        named.known_value(&slot),
        Some(ProgramValue::Int32(OldMachineTerm::read_named(
            version,
            Box::new(slot.clone()),
            LoadKind::Int32,
        ))),
    );
    assert!(super::memory_only_adds_named_cells(&before, &named).is_ok());
    let other = without_name();
    assert_eq!(before.memory(), other.memory());
    assert!(super::memory_only_adds_named_cells(&other, &named).is_err());
}

#[test]
fn resource_pointer_cell_keeps_the_complete_read_from_its_recorded_store() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address::new(
        crate::kernel::AddressBase::ExternalArgument,
        AddressOffset::constant(0),
    );
    let ty = ProgramType::Int32Pointer;
    let bytes = ty.byte_width();
    let initial = ExecutionState::new().with_memory(SymbolicMemory::new().with_block("other", 4));
    let without_name = || {
        let stored = initial.clone().with_memory(initial.memory().clone().store(
            slot.clone(),
            ProgramValue::typed_pointer(Address::symbolic(Variable(986_220)), ty),
        ));
        let forgotten =
            stored
                .memory()
                .without_possible_aliasing_cells(&slot, bytes, &PureFactContext::new());
        stored.with_memory(forgotten)
    };
    let before = without_name();
    assert!(before.memory().known_value(&slot).is_none());
    let source = before.program_point();
    let version = source.indexed_typed_version(&slot, ty).unwrap();
    let pointer = crate::kernel::Pointer::from_point_read(version, ty, &slot);
    let expected = ProgramValue::Pointer(pointer.clone());
    let named = before
        .memory()
        .clone()
        .materialize_cell_at(slot.clone(), ty, &source);
    assert_eq!(named.known_value(&slot), Some(expected.clone()));
    assert!(super::memory_only_adds_named_cells(&before, &named).is_ok());

    let work = [1, 8, 64, 256].map(|count| {
        let run = before
            .memory()
            .clone()
            .with_named_cell_run(slot.clone(), bytes, ty, 0, count, source.clone())
            .unwrap();
        let ((value, checked), work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                run.known_value(&slot),
                super::memory_only_adds_named_cells(&before, &run),
            )
        });
        assert_eq!(value, Some(expected.clone()));
        assert!(checked.is_ok());
        work
    });
    assert!(work.iter().all(|units| *units <= work[0] + 8), "{work:?}");

    let forged = before.memory().clone().materialize_named_cell(
        slot.clone(),
        ProgramValue::Pointer(pointer.with_provenance(Address::null())),
    );
    assert!(super::memory_only_adds_named_cells(&before, &forged).is_err());
    let other = without_name();
    assert_eq!(before.memory(), other.memory());
    assert!(super::memory_only_adds_named_cells(&other, &named).is_err());
}

#[test]
fn resource_float_cell_naming_distinguishes_equal_memory_source_points() {
    use crate::kernel::KernelFloatType;
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address::new(
        crate::kernel::AddressBase::ExternalArgument,
        AddressOffset::constant(0),
    );
    let before = ExecutionState::new().begin_function_entry_memory();
    let other = before.clone().begin_function_entry_memory();
    assert_eq!(before.memory(), other.memory());
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let point = before.program_point();
        let named = before.memory().clone().materialize_cell_at(
            slot.clone(),
            format.program_type(),
            &point,
        );
        assert_eq!(
            named.known_value(&slot),
            Some(format.value(OldMachineTerm::read_named(
                point.for_exact_read(),
                Box::new(slot.clone()),
                format.load_kind(),
            ))),
        );
        assert!(super::memory_only_adds_named_cells(&before, &named).is_ok());
        assert!(super::memory_only_adds_named_cells(&other, &named).is_err());
    }
}

#[test]
fn resource_cell_naming_checks_the_entry_point_without_a_store() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address::new(
        crate::kernel::AddressBase::ExternalArgument,
        AddressOffset::constant(0),
    );
    let before = ExecutionState::new().begin_function_entry_memory();
    let source = before.program_point();
    assert!(
        source
            .indexed_integer_version(&slot, LoadKind::Int32)
            .is_none()
    );
    let version = source
        .entry_integer_version(&slot, LoadKind::Int32)
        .unwrap();
    let named = before
        .memory()
        .clone()
        .materialize_entry_integer_cell_at(slot.clone(), &source);
    assert_eq!(
        named.known_value(&slot),
        Some(ProgramValue::Int32(OldMachineTerm::read_named(
            version,
            Box::new(slot),
            LoadKind::Int32,
        ))),
    );
    assert!(super::memory_only_adds_named_cells(&before, &named).is_ok());
    let other = ExecutionState::new().begin_function_entry_memory();
    assert_eq!(before.memory(), other.memory());
    assert!(super::memory_only_adds_named_cells(&other, &named).is_err());
}

#[test]
fn resource_run_naming_checks_the_source_without_expanding_slots() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address::new(
        crate::kernel::AddressBase::ExternalArgument,
        AddressOffset::constant(0),
    );
    let before = ExecutionState::new().begin_function_entry_memory();
    let point = before.program_point();
    let check = |count| {
        let named = before
            .memory()
            .clone()
            .with_named_cell_run(slot.clone(), 4, ProgramType::Int32, 0, count, point.clone())
            .unwrap();
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::memory_only_adds_named_cells(&before, &named)
        });
        checked.unwrap();
        let run = named.cells.runs().next().unwrap();
        assert!(point.names_exact_read(run.source_point()));
        work
    };

    let small = check(4);
    let large = check(1024);
    assert!(large <= small + 4, "run check work: {small} vs {large}");

    let named = before
        .memory()
        .clone()
        .with_named_cell_run(slot.clone(), 4, ProgramType::Int32, 0, 4, point)
        .unwrap();
    let other = ExecutionState::new().begin_function_entry_memory();
    assert_eq!(before.memory(), other.memory());
    assert!(super::memory_only_adds_named_cells(&other, &named).is_err());
    let overwritten = named.store(slot, ProgramValue::Int32(OldMachineTerm::constant(7)));
    assert!(super::memory_only_adds_named_cells(&before, &overwritten).is_err());
}
