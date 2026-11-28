use crate::kernel::binary_node;
#[cfg(not(feature = "fast-gate"))]
use crate::surface::planning::solve::{SolveEvidence, plan_solve_certificate};
// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::proof::quantified_equivalence_index_key;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{IntegerRangeFoldIndex, IntegerTerm, LoweringIntroduction, SharedIntegerTerm};

// These tests measure local proof updates rather than fixture setup.
// A 64-fold fact increase still rejects linear copies through the existing
// allocation ceilings or exact index-sharing assertions.
const LOCAL_PROOF_FACT_SIZES: [u32; 4] = [16, 64, 256, 1024];

// Local-update fixtures keep five samples and 128-fold growth where the
// original allocation guard needs more headroom to reject a linear index copy.
const STRUCTURAL_PROOF_FACT_SIZES: [u32; 5] = [16, 64, 256, 1024, 2048];

#[test]
fn unfinished_callback_error_does_not_execute_the_next_statement() {
    let click_file =
        crate::surface::parse("void invoke(struct callbacks* cb) { ensures 0 == 0; }").unwrap();
    let parsed = syntax::parse_functions_for_source(
        "struct callbacks { void (*call)(int32 x); }; void invoke(struct callbacks* cb) { cb->call(0); }",
        "callback.c",
    ).unwrap().remove(0);
    assert!(!parsed.callback_statement_sources().is_empty());
    let function = parsed.to_kernel_function();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let environment = ExecutionEnvironment::new();
    let root = Proof::for_execution_frontier(
        "unfinished callback",
        0,
        ExecutionProofState::at_entry(
            ExecutionState::new(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![],
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed.body()),
            ..ExecutionProofConstants::default()
        },
        &click_file.function_blocks()[0],
        &function,
        &parsed,
        &[],
        &environment,
        &resources,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    // The next statement cannot run without a callback value/contract. Error
    // reporting must describe the current frontier without attempting that call.
    let report = root
        .unfinished_callback_script_error()
        .unwrap()
        .concise_report();
    assert!(
        report.contains("the proof stops before function exit"),
        "{report}"
    );
    assert!(
        !report.contains("continuing its checked operations"),
        "{report}"
    );
    assert!(root.certificate().steps().is_empty());
}

#[test]
fn implicit_tail_budget_errors_check_boundaries_without_exploring_paths() {
    let click_file = crate::surface::parse("void bounded() { ensures 0 == 0; }").unwrap();
    let parsed = syntax::parse_functions_for_source("void bounded() {}", "bounded.c")
        .unwrap()
        .remove(0);
    let function = parsed.to_kernel_function();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let environment = ExecutionEnvironment::new();
    let root = Proof::for_execution_frontier(
        "bounded implicit tail",
        0,
        ExecutionProofState::at_entry(
            ExecutionState::new(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![],
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed.body()),
            ..ExecutionProofConstants::default()
        },
        &click_file.function_blocks()[0],
        &function,
        &parsed,
        &[],
        &environment,
        &resources,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    let split_limit = super::super::cursor_execution::BOUNDED_EXECUTE_SPLIT_LIMIT;
    let step_limit = super::super::cursor_execution::BOUNDED_EXECUTE_STEP_LIMIT;
    let mut steps = step_limit - 1;
    root.charge_execute_step(&mut steps, split_limit)
        .expect("both limits permit the last allowed step");
    assert_eq!(steps, step_limit);
    let step_error = root
        .charge_execute_step(&mut steps, split_limit)
        .unwrap_err();
    let message = step_error.message();
    assert!(
        message.contains(&format!("execution exhausted its {step_limit}-step budget")),
        "{message}"
    );
    assert!(message.contains("branch ensuring"), "{message}");
    assert_eq!(steps, step_limit, "refusal must not charge another step");

    let mut steps = 0;
    let split_error = root
        .charge_execute_step(&mut steps, split_limit + 1)
        .unwrap_err();
    let message = split_error.message();
    assert!(
        message.contains(&format!("split at more than {split_limit} C branches")),
        "{message}"
    );
    assert!(message.contains("at region(0)"), "{message}");
    assert!(message.contains("branch ensuring"), "{message}");
    assert!(
        message.contains("proof `if <condition> ensuring"),
        "{message}"
    );
    assert_eq!(steps, 0, "refusal must not charge a step");
    assert!(root.certificate().steps().is_empty());
}

fn indexed_fact(index: u32) -> Proposition {
    Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(OldMachineTerm::Variable(Variable(0))),
            right: Box::new(OldMachineTerm::constant(index)),
        },
        true,
    )
}

/// Count ordinary operations and their explicit arguments/premises, rejecting
/// certificates and unexpanded search throughout the proof. Allocation curves
/// grow with this explicit input/output and logarithmically with ambient facts.
fn ordinary_arithmetic_work_size(steps: &[ProofStep]) -> Option<usize> {
    let mut pending = steps.iter().collect::<Vec<_>>();
    let mut count = 0;
    while let Some(step) = pending.pop() {
        count += 1;
        match step {
            ProofStep::Have { proof, .. } | ProofStep::IntroBlock { body: proof, .. } => {
                pending.extend(proof.steps());
            }
            ProofStep::Both {
                left_proof,
                right_proof,
                ..
            } => {
                pending.extend(left_proof.steps());
                pending.extend(right_proof.steps());
            }
            ProofStep::If {
                then_proof,
                else_proof,
                ..
            } => {
                pending.extend(then_proof.steps());
                pending.extend(else_proof.steps());
            }
            ProofStep::CloseBounds(premises) => count += premises.len(),
            ProofStep::ApplyTheorem(application) => count += application.arguments.len(),
            ProofStep::ApplyTheoremUsing {
                application,
                premises,
            }
            | ProofStep::ApplyPlannedTheorem {
                application,
                premises,
            } => count += application.arguments.len() + premises.len(),
            ProofStep::Known
            | ProofStep::Rewrite(_)
            | ProofStep::Intro
            | ProofStep::CloseUnreachable => {}
            _ => {
                eprintln!("nonordinary arithmetic step: {step:?}");
                return None;
            }
        }
    }
    Some(count)
}

/// Build a raw arithmetic goal for checker-allocation fixtures while retaining,
/// rather than assuming, its evaluation requirements. The solver's input facts
/// remain the explicitly selected original premises; source replay tests check
/// the generated operation-domain proofs as well.
fn lower_arithmetic_fixture_goal(
    proposition: &SyntaxProposition,
    assumptions: &PureFactContext,
    binding: ParameterBinding<'_>,
    frame: FixedStateFrame<'_>,
    definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let mut names = BTreeSet::new();
    crate::surface::lowering::collect_click_proposition_referenced_names(proposition, &mut names);
    let (values, arrays) =
        crate::surface::lowering::contract_environment_for_names(binding, &names, frame.state)
            .map_err(|error| error.message)?;
    crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
        proposition,
        assumptions,
        ContractEnvironment::new(&values, &arrays),
        frame,
        definitions,
        Default::default(),
    )
    .map(|(goal, _, _, _)| goal)
}

/// Typed solve cites only premises it can spell as Click source, and a bare
/// kernel value prints as no source name. The typed-rule fixtures therefore
/// state their int32 premises over named parameters `x0`, `x1`, ..., bound
/// to the kernel `terms` in order; any other term stays a literal value.
fn named_int32(terms: &[OldMachineTerm], term: &OldMachineTerm) -> SyntaxTerm {
    match terms.iter().position(|named| named == term) {
        Some(index) => {
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(format!("x{index}").into()))
        }
        None => SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            term.clone(),
        ))),
    }
}

/// A C function whose int32 parameters are [`named_int32`]'s names, and the
/// arguments that bind them to `terms`.
fn named_int32_function(
    terms: &[OldMachineTerm],
) -> (
    crate::languages::interface::ImportedFunction,
    Vec<ProgramExpression>,
) {
    let parameters = (0..terms.len())
        .map(|index| format!("int32 x{index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let function = syntax::parse_function(&format!("void noop({parameters}) {{}}"))
        .expect("test C function should parse");
    let arguments = terms
        .iter()
        .map(|term| ProgramExpression::Value(ProgramValue::Int32(term.clone())))
        .collect();
    (function, arguments)
}

/// [`named_int32`]'s names as a pure theorem's values.
fn named_int32_values(terms: &[OldMachineTerm]) -> ProgramValueBindings {
    terms
        .iter()
        .enumerate()
        .map(|(index, term)| (format!("x{index}"), ProgramValue::Int32(term.clone())))
        .collect()
}

#[test]
fn fixed_state_failure_names_kernel_values_held_in_live_locals() {
    // Loop-closure subproofs have a fixed-state context, not an execution
    // branch. Their failed goals use the source local holding a copied value,
    // even when a generated temporary with the same value sorts before it.
    let len = OldMachineTerm::Variable(Variable(70));
    let size = OldMachineTerm::Variable(Variable(94));
    let state = ExecutionState::new()
        .with_local("len", ProgramValue::UInt64(len.clone()))
        .with_local("chunk_size", ProgramValue::UInt64(size.clone()))
        .with_local("__rust_mir_94", ProgramValue::UInt64(size.clone()));
    let remainder = OldMachineTerm::uint64_remainder(len, size.clone());
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(remainder.clone()),
            right: Box::new(OldMachineTerm::uint64_constant(0)),
        },
        true,
    );
    let facts = [Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(size),
            right: Box::new(OldMachineTerm::uint64_constant(22208)),
        },
        true,
    )];
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(
            remainder,
        ))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(
            OldMachineTerm::uint64_constant(0),
        ))),
    };
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let root = Proof::for_fixed_state_surface_goal(
        "remainder",
        0,
        &facts,
        goal,
        surface,
        ParameterBinding::default(),
        &state,
        &state,
        &retained_states,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
    );
    let error = root
        .driver()
        .try_authoritative_linear_script(&[ProofTactic::Known])
        .err()
        .expect("the available chunk size does not prove a zero remainder");
    let text = error.message();
    assert!(text.contains("goal: len % chunk_size == 0u64"), "{text}");
    assert!(text.contains("chunk_size == 22208u64"), "{text}");
    assert!(!text.contains("__rust_"), "{text}");
    assert!(!text.contains("no exact Click spelling"), "{text}");
}

#[test]
fn missing_known_side_uses_recorded_names_in_fixed_state_errors() {
    let before = OldMachineTerm::Variable(Variable(70));
    let after = OldMachineTerm::Variable(Variable(71));
    let entry = ExecutionState::new().with_local("remaining", ProgramValue::UInt64(before.clone()));
    let state = ExecutionState::new().with_local("remaining", ProgramValue::UInt64(after.clone()));
    let side = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: Box::new(before.clone()),
            right: Box::new(after.clone()),
        },
        true,
    );
    let goal = Proposition::And(Box::new(side.clone()), Box::new(side));
    let written = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(before))),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(after))),
    };
    let surface = SyntaxProposition::And(Box::new(written.clone()), Box::new(written));
    let mut retained_states = RecordedStates::new();
    retained_states.insert(
        ProgramPointSelector::Mark("iteration".into()),
        entry.clone(),
    );
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let root = Proof::for_fixed_state_surface_goal(
        "state_error",
        0,
        &[],
        goal,
        surface,
        ParameterBinding::default(),
        &entry,
        &state,
        &retained_states,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
    );
    for traced in [false, true] {
        let render = || {
            root.driver()
                .try_authoritative_linear_script(&[ProofTactic::Known])
                .err()
                .expect("neither conjunct is available")
                .to_string()
        };
        let error = if traced {
            crate::surface::with_proof_trace("state_error", render)
        } else {
            render()
        };
        assert!(
            error.contains("missing exact fact: at(iteration, remaining) < remaining"),
            "{error}"
        );
        assert!(
            error.contains("goal: at(iteration, remaining) < remaining"),
            "{error}"
        );
        assert!(!error.contains("<unnamed"), "{error}");
    }
}

#[test]
fn return_publication_shares_effect_prefixes_and_suppresses_duplicates() {
    for size in [4, 64, 1024] {
        let memory = ExecutionState::new().memory().clone();
        let source: ExecutionFacts = (0..size)
            .map(|index| {
                ExecutionPureFact::new(Proposition::MemoryMutatesOnly {
                    before_point: Default::default(),
                    after_point: Default::default(),
                    before: memory.clone(),
                    after: memory.clone(),
                    writes: vec![(
                        Address::new(
                            crate::kernel::AddressBase::ExternalArgument,
                            AddressOffset::constant(index as i64 * 4),
                        ),
                        crate::kernel::AccessExtent::from(4),
                    )],
                })
            })
            .collect();
        let mut repeated = source.clone();
        repeated.extend_shared(&source.selected(&[0]));
        let mut forks = Vec::new();
        for arm in 0..4 {
            let mut facts: ExecutionFacts =
                [ExecutionPureFact::new(indexed_fact(10_000 + arm))].into();
            crate::surface::proof::cursor_execution::append_execution_effect_facts(
                &mut facts, &repeated,
            );
            assert_eq!(facts.len(), size as usize + 1);
            for (original, retained) in source.iter().zip(facts.iter().skip(1)) {
                assert_eq!(original, retained);
                assert!(std::ptr::eq(original, retained));
            }
            forks.push(facts);
        }
        let objects = forks
            .iter()
            .flat_map(|facts| facts.iter().skip(1))
            .map(|fact| fact as *const ExecutionPureFact as usize)
            .collect::<BTreeSet<_>>();
        assert_eq!(objects.len(), size as usize);
        drop(source);
        drop(repeated);
        assert_eq!(forks[0].len(), size as usize + 1);
    }
}

fn fact_node_allocations() -> usize {
    persistent_node_allocations()
}

fn opposite_atomic_fact(fact: &Proposition) -> Proposition {
    match fact {
        Proposition::ConditionIs(condition, value) => {
            Proposition::condition_is(condition.clone(), !value)
        }
        Proposition::Not(body) => *body.clone(),
        other => Proposition::Not(Box::new(other.clone())),
    }
}

fn pure_identity_fixture() -> PureTheoremContext {
    PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    }
}

fn invariant_bundle_leaf_fixture() -> (Proposition, Proposition) {
    let pointer = Address::new("sum".into(), AddressOffset::constant(0));
    let loadable = crate::kernel::quantifiers::test_forall(
        Default::default(),
        Variable(30),
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(OldMachineTerm::constant(0)),
                        right: Box::new(OldMachineTerm::Variable(Variable(30))),
                    },
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(OldMachineTerm::Variable(Variable(30))),
                        right: Box::new(OldMachineTerm::constant(16)),
                    },
                    true,
                )),
            )),
            Box::new(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: SymbolicMemory::new().with_block("sum", 16),
                base: pointer,
                bytes: (OldMachineTerm::Variable(Variable(30))).into(),
                wide: false,
            }),
        ),
    );
    let fold = IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Integer {
            start: SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
            end: SharedIntegerTerm::from(IntegerTerm::Variable(Variable(40))),
        },
        IntegerTerm::constant_i64(0),
        Variable(41),
        Variable(42),
        IntegerTerm::Add(
            SharedIntegerTerm::from(IntegerTerm::Variable(Variable(41))),
            SharedIntegerTerm::from(IntegerTerm::Variable(Variable(42))),
        ),
    );
    let fold_equality = Proposition::condition_is(
        OldConditionTerm::IntegerEqual(
            SharedIntegerTerm::from(fold),
            SharedIntegerTerm::from(IntegerTerm::Variable(Variable(43))),
        ),
        true,
    );
    (loadable, fold_equality)
}

#[test]
fn atomic_conjunct_extraction_returns_when_an_early_step_completes_the_goal() {
    let x = OldMachineTerm::Variable(Variable(101));
    let y = OldMachineTerm::Variable(Variable(102));
    let two = OldMachineTerm::constant(2);
    let comparison = |left: OldMachineTerm, right: OldMachineTerm| {
        (
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                true,
            ),
            SyntaxProposition::Comparison {
                left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                    left,
                ))),
                operator: ComparisonOperator::LessEqual,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(right),
                )),
            },
        )
    };
    let pairs = vec![comparison(x.clone(), y.clone()), comparison(y, two.clone())];
    let (goal, _) = comparison(x, two);
    let assumptions = PureFactContext::new()
        .assume_proposition(pairs[0].0.clone())
        .assume_proposition(pairs[1].0.clone());
    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .unwrap();
    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises().len(), 2);
    // An alternate derivation selects two premises, but the goal is also an
    // available conjunct. Extracting either premise completes the goal.
    let facts = vec![Proposition::And(
        Box::new(goal.clone()),
        Box::new(Proposition::And(
            Box::new(pairs[0].0.clone()),
            Box::new(pairs[1].0.clone()),
        )),
    )];
    let context = pure_identity_fixture();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "early extraction completion",
        &facts,
        goal.clone(),
        &context,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    let closed = crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
        &(root),
        &derivation,
        &pairs,
    )
    .expect("the checked extraction should succeed")
    .expect("the first extraction should complete the proof");
    assert!(closed.is_complete());
    assert_eq!(closed.completed_proposition().unwrap().proposition(), &goal);
    assert!(matches!(
        closed.certificate().steps(),
        [ProofStep::Have { proposition, .. }, ProofStep::Known] if proposition == &pairs[0].1
    ));
    assert!(root.certificate().steps().is_empty());
    let rechecked = root
        .driver()
        .try_authoritative_linear_script(&closed.certificate().to_proof_tactics())
        .unwrap()
        .unwrap();
    assert!(rechecked.is_complete());
}

#[test]
fn atomic_conjunct_extraction_requires_exact_selected_premise_on_small_stack() {
    std::thread::Builder::new()
        .name("atomic-extract-progress-small-stack".into())
        .stack_size(1792 * 1024)
        .spawn(|| {
            let parsed_function = syntax::parse_function("int32 read(int32 p[1]) { return 0; }")
                .expect("test pointer function should parse");
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let theorems = TheoremEnvironment::new(&[]);
            let pointer = Address::new("atomic-extract-cell".into(), AddressOffset::constant(0));
            let old_memory = SymbolicMemory::new().with_block("atomic-extract-cell", 4).store(
                pointer.clone(),
                ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_100))),
            );
            let current_memory = old_memory.clone().store(
                pointer.clone(),
                ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_101))),
            );
            let old_state = ExecutionState::new().with_memory(old_memory);
            let current_state = ExecutionState::new().with_memory(current_memory);
            let arguments = vec![ProgramExpression::Value(ProgramValue::pointer(pointer))];
            let surface = SyntaxProposition::Comparison {
                left: SyntaxTerm::Index(
                    Box::new(SyntaxTerm::ProgramExpression(
                        ProgramExpression::Variable(("p".to_string()).into()),
                    )),
                    Box::new(SyntaxTerm::IntegerLiteral("0".to_string())),
                ),
                operator: ComparisonOperator::LessEqual,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(9))),
            };
            let retained_states = RecordedStates::new();
            let lower_at = |state: &ExecutionState| {
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    &PureFactContext::new(),
                    ParameterBinding::new(parsed_function.parameters(), &arguments),
                    FixedStateFrame::new(&old_state, state, None, &retained_states),
                    SpecDefinitions::new(&predicates, &functions),
                )
                .expect("the selected load bound should lower")
            };
            let old_leaf = lower_at(&old_state);
            let current_leaf = lower_at(&current_state);
            assert_ne!(old_leaf, current_leaf);

            let old_sibling = indexed_fact(8_000_102);
            let current_sibling = indexed_fact(8_000_103);
            let facts = vec![
                Proposition::And(Box::new(old_leaf.clone()), Box::new(old_sibling)),
                Proposition::And(Box::new(current_leaf), Box::new(current_sibling)),
            ];
            let mut stale_surfaces = SurfacePropositionMap::default();
            stale_surfaces
                .record_lowering(&surface, &old_leaf)
                .expect("the resource body should retain its old lowering");
            let stale = Proof::for_fixed_state_goal(
                "stale atomic conjunct extraction",
                0,
                &facts,
                old_leaf.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &old_state,
                &current_state,
                &retained_states,
                &stale_surfaces,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
                &[],
            );
            let (_, stale_derivation, _) =
                crate::kernel::search::ProofSearch::selected_solve_derivation(&(stale), false)
                    .expect("the old resource leaf should be selected from its conjunction");
            let selected_pairs = vec![(old_leaf.clone(), surface.clone())];
            assert!(
                crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
                    &(stale),
                    &stale_derivation,
                    &selected_pairs
                )
                .is_err(),
                "extracting the current spelling must not count as producing the selected old leaf"
            );
            assert!(
                crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
                    &(stale),
                    &stale_derivation,
                    &selected_pairs
                )
                .is_err(),
                "a retry must remain a prompt miss rather than accumulating extraction steps"
            );
            // The unanchored current spelling cannot stand for the old leaf,
            // but the old leaf is this fixed-state proof's entry-state fact,
            // and anchoring the written form at function entry lowers to it
            // exactly. That is the one checked extraction the closure may make:
            // a single step, never a recursive retry of the stale spelling.
            let anchored_surface = surface_at_program_point(
                &surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                },
            )
            .expect("the selected surface anchors at function entry");
            let anchored =
                crate::kernel::search::ProofSearch::try_typed_atomic_solve_closure(&(stale))
                    .expect("the entry-anchored spelling of the old leaf should extract it");
            assert!(anchored.is_complete());
            assert!(matches!(anchored.certificate().steps(),
                [ProofStep::Have { proposition, .. }, ProofStep::Known] if proposition == &anchored_surface
            ), "only the entry-anchored premise may be retained");
            let rechecked = stale
                .driver()
                .try_authoritative_linear_script(&anchored.certificate().to_proof_tactics())
                .unwrap()
                .unwrap();
            assert!(rechecked.is_complete());
            assert!(stale.certificate().steps().is_empty());

            let mut exact_surfaces = SurfacePropositionMap::default();
            exact_surfaces
                .record_lowering(&surface, &old_leaf)
                .expect("the exact resource leaf should retain its source spelling");
            let exact = Proof::for_fixed_state_goal(
                "exact atomic conjunct extraction",
                0,
                std::slice::from_ref(&facts[0]),
                old_leaf.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &old_state,
                &old_state,
                &retained_states,
                &exact_surfaces,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
                &[],
            );
            let sibling = exact.clone();
            let closed =
                crate::kernel::search::ProofSearch::try_typed_atomic_solve_closure(&(exact))
                    .expect("the exact selected leaf should extract and close the goal");
            assert!(closed.is_complete());
            assert!(matches!(closed.certificate().steps(),
                [ProofStep::Have { proposition, .. }, ProofStep::Known] if proposition == &surface
            ));
            assert!(sibling.certificate().steps().is_empty());
        })
        .expect("the atomic extraction small-stack test should start")
        .join()
        .expect("atomic extraction must not overflow the small stack");
}

#[test]
fn invariant_bundle_closure_descends_surface_free_both_and_intro_and_rechecks() {
    let (loadable, fold_equality) = invariant_bundle_leaf_fixture();
    let goal = Proposition::And(
        Box::new(loadable.clone()),
        Box::new(Proposition::Implies(
            Box::new(loadable.clone()),
            Box::new(Proposition::Implies(
                Box::new(loadable.clone()),
                Box::new(fold_equality.clone()),
            )),
        )),
    );
    let context = pure_identity_fixture();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "surface-free invariant bundle",
        &[loadable, fold_equality],
        goal,
        &context,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    assert!(root.surface_goal().is_none());
    let checked = root
        .driver()
        .plan_invariant_bundle_closure()
        .expect("bundle planning should remain a checked operation")
        .expect("explicit leaf facts should close the generated bundle");
    assert!(checked.is_complete());
    let certificate = checked.certificate();
    let [
        ProofStep::Both {
            left_proof,
            right_proof,
            ..
        },
    ] = certificate.steps()
    else {
        panic!("expected a split bundle: {certificate:?}");
    };
    assert_eq!(left_proof.steps(), [ProofStep::Known]);
    let [ProofStep::IntroBlock { binder: None, body }] = right_proof.steps() else {
        panic!("expected a scoped guard introduction: {right_proof:?}");
    };
    assert!(matches!(
        body.steps(),
        [ProofStep::IntroBlock { binder: None, body }] if body.steps() == [ProofStep::Known]
    ));
    let rechecked = root
        .driver()
        .try_authoritative_linear_script(&certificate.to_proof_tactics())
        .expect("the generated structural certificate should recheck")
        .expect("rechecking the generated certificate should close");
    assert_eq!(rechecked.certificate(), certificate);
}

#[test]
fn invariant_bundle_closure_rejects_surface_free_bundle_without_fold_equality() {
    let (loadable, fold_equality) = invariant_bundle_leaf_fixture();
    let goal = Proposition::And(
        Box::new(loadable.clone()),
        Box::new(Proposition::Implies(
            Box::new(loadable.clone()),
            Box::new(Proposition::Implies(
                Box::new(loadable.clone()),
                Box::new(fold_equality),
            )),
        )),
    );
    let context = pure_identity_fixture();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "missing invariant bundle leaf",
        &[loadable],
        goal,
        &context,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    assert!(
        root.driver()
            .plan_invariant_bundle_closure()
            .expect("missing leaf should be a bounded rejection")
            .is_none()
    );
}

#[test]
fn invariant_bundle_budget_refusal_retains_selected_obligation() {
    let (_, fold_equality) = invariant_bundle_leaf_fixture();
    let context = pure_identity_fixture();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "selected invariant bundle leaf",
        &[],
        fold_equality,
        &context,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    let expected = root.bundle_member_spelling().unwrap();
    let _ = execution_statements::take_unclosed_bundle_member();
    let error = crate::instrumentation::with_run_work_limit(0, || {
        root.driver().plan_invariant_bundle_closure()
    })
    .err()
    .expect("exhaustion must refuse the selected obligation");
    assert!(error.message().contains("budget"), "{error:?}");
    // The source driver adds the checked goal's diagnostic to a deadline
    // refusal. Exercise the same formatting path: concise reports read its
    // reason rather than the error's legacy summary.
    let error = root.step_error(error.raw_summary());
    let reported = execution_statements::describe_invariant_closure_error(error);
    for report in [reported.message().to_owned(), reported.concise_report()] {
        assert!(
            report.contains("unresolved obligation") && report.contains(&expected),
            "{report}"
        );
        assert!(report.contains("budget"), "{report}");
    }
    assert!(execution_statements::take_unclosed_bundle_member().is_none());
    let unknown =
        execution_statements::describe_invariant_closure_error(ClickError::new("search stopped"));
    assert!(
        unknown
            .concise_report()
            .contains("without retaining an individual obligation")
    );
    assert!(root.certificate().steps().is_empty());
    let direct = crate::instrumentation::with_run_work_limit(0, || {
        crate::kernel::search::ProofSearch::try_direct_structural_closure_with_quantified(
            &(root),
            &mut |_| Ok(None),
        )
    })
    .err()
    .expect("the direct strategy must also refuse exhaustion");
    assert_eq!(
        direct.kind(),
        crate::surface::ClickErrorKind::WorkLimitReached
    );
    assert_eq!(direct.diagnostic().unwrap().kernel_goal(), root.goal());
    let direct = execution_statements::describe_invariant_closure_error(direct);
    assert!(direct.concise_report().contains("unresolved obligation"));
}

#[test]
fn attempt_discards_failed_continuation_and_shares_the_checked_prefix() {
    let fact = indexed_fact(7);
    let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
    let theorem_context = pure_identity_fixture();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "attempt",
        &[],
        goal,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );

    // A locally successful prefix whose continuation fails is one
    // discarded candidate: the ancestor is unchanged and no partial
    // expansion is published.
    let mut budget = attempt::AttemptBudget::unbounded();
    let missed = attempt::attempt(&root, &mut budget, |candidate| {
        let prefix = attempt::candidate_outcome(candidate.driver().apply_step(ProofStep::Intro))?
            .expect("intro is locally valid on the implication goal");
        // The continuation demands a step the prefix cannot support.
        attempt::candidate_outcome(prefix.driver().apply_step(ProofStep::Enumerate))
    })
    .expect("a rejected continuation is a miss, not a tooling failure");
    assert!(missed.is_none());
    assert!(root.certificate().steps().is_empty());
    assert!(!root.is_complete());

    // N candidate suffixes over one shared checked prefix cost N suffix
    // checks: every attempt starts from the same prefix state, which was
    // produced by exactly one accepted `Intro`.
    let prefix = root
        .driver()
        .apply_step(ProofStep::Intro)
        .expect("intro should refine the implication goal");
    let mut attempts = 0usize;
    let mut budget = attempt::AttemptBudget::unbounded();
    let selected = attempt::first_success(
        &prefix,
        &mut budget,
        [
            ProofStep::Enumerate,
            ProofStep::Enumerate,
            ProofStep::Enumerate,
            ProofStep::Known,
        ],
        |shared, step| {
            attempts += 1;
            assert!(shared.state.shares_state_with(&prefix.state));
            attempt::candidate_outcome(shared.driver().apply_step(step))
        },
    )
    .expect("candidate misses must not abort the search")
    .expect("the known suffix should close the goal");
    assert_eq!(attempts, 4);
    assert!(selected.is_complete());
    assert_eq!(
        selected.certificate().steps(),
        &[ProofStep::Intro, ProofStep::Known],
        "the retained certificate contains only the accepted path"
    );

    // An exhausted deterministic budget is a prompt bounded miss.
    let mut attempts = 0usize;
    let mut budget = attempt::AttemptBudget::new(1);
    let bounded = attempt::first_success(
        &prefix,
        &mut budget,
        [ProofStep::Enumerate, ProofStep::Known, ProofStep::Enumerate],
        |shared, step| {
            attempts += 1;
            attempt::candidate_outcome(shared.driver().apply_step(step))
        },
    )
    .expect("budget exhaustion is a miss, not an error");
    assert!(bounded.is_none());
    assert_eq!(attempts, 1, "only the admitted candidate may be attempted");

    // An all-or-nothing sequence discards its partial descendant.
    let mut budget = attempt::AttemptBudget::unbounded();
    let sequence = attempt::try_sequence(
        &root,
        &mut budget,
        &[ProofStep::Intro, ProofStep::Enumerate],
    )
    .expect("a rejected sequence tail is a miss");
    assert!(sequence.is_none());
    let mut budget = attempt::AttemptBudget::unbounded();
    let sequence = attempt::try_sequence(&root, &mut budget, &[ProofStep::Intro, ProofStep::Known])
        .expect("an accepted sequence is not an error")
        .expect("the checked sequence should close the goal");
    assert_eq!(
        sequence.certificate().steps(),
        &[ProofStep::Intro, ProofStep::Known]
    );
}

#[test]
fn both_and_preserves_exact_binders_and_saved_states() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let pointer = Address::new("cell".into(), AddressOffset::constant(0));
    let memory = SymbolicMemory::new().with_block("cell", 4).store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(11))),
    );
    let conjunct = |binder| {
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(binder),
            Sort::ProgramInt32,
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(OldMachineTerm::read_named(
                        crate::kernel::ProgramPoint::of_memory(&memory),
                        Box::new(pointer.clone()),
                        crate::kernel::LoadKind::Int32,
                    )),
                    right: Box::new(OldMachineTerm::Variable(Variable(binder))),
                },
                true,
            ),
        )
    };
    // The same saved value is bound in the left goal but free in the right.
    // Opening child scopes must preserve this distinction without re-lowering.
    let left = conjunct(11);
    let right = conjunct(22);
    let root = Proof::for_pure_goal(
        "both states",
        &[],
        Proposition::And(Box::new(left.clone()), Box::new(right.clone())),
        &context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let (split, _, ids) = root.split_focused_both().unwrap();
    assert_eq!(split.focus_branch(ids[0]).unwrap().goal(), Some(&left));
    assert_eq!(split.focus_branch(ids[1]).unwrap().goal(), Some(&right));
}

#[test]
fn both_surface_conjunction_is_positional_even_for_duplicate_or_reversed_children() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let equality = |value| SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_pure_theorem_proposition(
            "positional both presentation",
            surface,
            ContractEnvironment::new(&context.values, &context.array_refs),
            &context.point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("constant equality should lower")
    };
    let first = equality(1);
    let second = equality(2);
    let duplicate_surface =
        SyntaxProposition::And(Box::new(first.clone()), Box::new(first.clone()));
    let duplicate_kernel = Proposition::And(Box::new(lower(&first)), Box::new(lower(&first)));
    let duplicate = Proof::for_pure_surface_goal(
        "duplicate both presentation",
        &[],
        duplicate_kernel,
        duplicate_surface.clone(),
        &context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let (split, _, ids) = duplicate
        .split_focused_both()
        .expect("duplicate written conjuncts retain their positional spellings");
    assert_eq!(
        split.focus_branch(ids[0]).unwrap().surface_goal(),
        Some(&first)
    );
    assert_eq!(
        split.focus_branch(ids[1]).unwrap().surface_goal(),
        Some(&first)
    );

    let reversed_surface =
        SyntaxProposition::And(Box::new(second.clone()), Box::new(first.clone()));
    let reversed = Proof::for_pure_surface_goal(
        "reversed both presentation",
        &[],
        Proposition::And(Box::new(lower(&first)), Box::new(lower(&second))),
        reversed_surface,
        &context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let error = match reversed.split_focused_both() {
        Ok(_) => panic!("reversed written children must not be remapped by a set-like match"),
        Err(error) => error,
    };
    assert!(
        error.message().contains("child order does not match"),
        "{error:?}"
    );
}

#[test]
fn both_preserves_written_body_across_an_inserted_guard_and_reverifies_cold() {
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test function should parse");
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let guard = Proposition::condition_is(OldConditionTerm::Constant(false), false);
    let body_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(2))),
    };
    let body = lower_fixed_state_proposition_with_assumptions(
        &body_surface,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &[]),
        FixedStateFrame::new(&state, &state, None, &retained_states),
        SpecDefinitions::new(&predicates, &functions),
    )
    .expect("body should lower");
    let kernel = Proposition::And(Box::new(guard.clone()), Box::new(body));
    let root = Proof::for_fixed_state_surface_goal(
        "guarded both presentation",
        0,
        &[],
        kernel,
        body_surface.clone(),
        ParameterBinding::new(parsed_function.parameters(), &[]),
        &state,
        &state,
        &retained_states,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
    );
    let (split, split_id, ids) = root
        .split_focused_both()
        .expect("checked body correspondence should cross the inserted guard");
    assert!(split.focus_branch(ids[0]).unwrap().surface_goal().is_none());
    assert_eq!(
        split.focus_branch(ids[1]).unwrap().surface_goal(),
        Some(&body_surface)
    );
    let marker = split.conjunction_checkpoint(ids).unwrap();
    let left = split
        .focus_branch(ids[0])
        .unwrap()
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the required guard remains a checked obligation");
    let joined = left
        .focus_branch(ids[1])
        .unwrap()
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the written body should retain its Surface spelling")
        .join_focused_both(&marker, split_id, ids)
        .expect("both checked children should join");
    assert!(joined.is_complete());
    let certificate = joined.certificate();
    let cold = root
        .driver()
        .try_authoritative_linear_script(&certificate.to_proof_tactics())
        .expect("the rendered guarded split should be accepted cold")
        .expect("the rendered guarded split should close");
    assert_eq!(cold.certificate(), certificate);
    let missing_guard = ProofCertificate::from_steps(vec![ProofStep::Both {
        conjuncts: [None, None],
        left_proof: Box::new(ProofCertificate::from_steps(Vec::new()).unwrap()),
        right_proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
    }])
    .unwrap();
    assert!(
        root.driver()
            .try_authoritative_linear_script(&missing_guard.to_proof_tactics())
            .expect("deleting a required guard proof should be a bounded rejection")
            .is_none(),
        "the guard child cannot be silently omitted"
    );
    let smart = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
        .expect("hidden-guard simplification should remain bounded")
        .expect("both normalized children should close");
    assert!(smart.is_complete());
}

#[test]
fn both_rejects_an_unsupported_written_child_correspondence_boundedly() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let guard = Proposition::condition_is(OldConditionTerm::Constant(false), false);
    let body = Proposition::condition_is(OldConditionTerm::Constant(true), true);
    let unsupported = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(2))),
    };
    let root = Proof::for_pure_surface_goal(
        "unsupported both presentation",
        &[],
        Proposition::And(Box::new(guard), Box::new(body)),
        unsupported,
        &context,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    let retained = root.clone();
    let error = match root.split_focused_both() {
        Ok(_) => panic!("an unrelated written proposition must not attach to a child"),
        Err(error) => error,
    };
    assert!(
        error.message().contains("cannot preserve its written goal"),
        "{error:?}"
    );
    assert!(root.state.shares_state_with(&retained.state));
    assert!(Arc::ptr_eq(&root.node, &retained.node));
    assert!(root.certificate().steps().is_empty());
}

#[test]
fn both_rejects_unlowerable_child_without_exact_parent_metadata() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let kernel = Proposition::And(
        Box::new(Proposition::condition_is(
            OldConditionTerm::Constant(true),
            true,
        )),
        Box::new(Proposition::condition_is(
            OldConditionTerm::Constant(false),
            false,
        )),
    );
    let root = Proof::for_pure_surface_goal(
        "unlowerable both presentation",
        &[],
        kernel,
        SyntaxProposition::PredicateCall {
            name: "missing".to_string(),
            arguments: Vec::new(),
        },
        &context,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    let error = match root.split_focused_both() {
        Ok(_) => panic!("an unlowerable child must not receive a guessed spelling"),
        Err(error) => error,
    };
    assert!(
        error.message().contains("candidate did not lower"),
        "{error:?}"
    );
}

#[test]
fn focused_case_split_partitions_by_attribution_and_rejects_foreign_joins() {
    let equality = |value| SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value))),
    };
    let disjunction = SyntaxProposition::Or(Box::new(equality(0)), Box::new(equality(1)));
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let theorem_context = pure_identity_fixture();
    let kernel_disjunction = lower_pure_theorem_proposition(
        "focused cases",
        &disjunction,
        ContractEnvironment::new(&theorem_context.values, &theorem_context.array_refs),
        &theorem_context.point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("constant disjunction should lower");
    let root = Proof::for_pure_goal(
        "focused cases",
        std::slice::from_ref(&kernel_disjunction),
        kernel_disjunction.clone(),
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );

    // The split retires the parent id and opens both sibling goals in
    // one state, each carrying its own disjunct in its own context.
    let root_goal = root.sole_branch_id().expect("the root owns its goal");
    let (split_proof, split, ids) = root
        .split_focused_cases(disjunction.clone())
        .expect("the exact disjunction splits in-proof");
    assert_eq!(split_proof.branches().collect::<Vec<_>>(), ids);
    assert!(split_proof.state.open_branches().get(root_goal).is_none());
    let marker = split_proof.checkpoint();

    // Arms are proven by focusing each recorded id on one lineage; the
    // interleaved steps carry their goal attribution.
    let left_closed = split_proof
        .focus_branch(ids[0])
        .expect("the left sibling is open")
        .begin_execution_match()
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the shared disjunction fact closes the left claim");
    assert!(left_closed.state.open_branches().get(ids[1]).is_some());
    let both_closed = left_closed
        .focus_branch(ids[1])
        .expect("the right sibling is still open")
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the shared disjunction fact closes the right claim");
    assert!(both_closed.is_complete());

    // An unjoined arm's own certificate follows its lineage: the sibling's
    // interleaved step and nested match marker are attributed elsewhere,
    // while the whole chain still lists both checked steps.
    assert_eq!(left_closed.path_certificate().unwrap().steps().len(), 1);
    assert_eq!(both_closed.path_certificate().unwrap().steps().len(), 1);
    assert_eq!(both_closed.certificate().steps().len(), 2);

    // A foreign marker from a second split of the same root is rejected.
    let (foreign_proof, foreign_split, foreign_ids) = root
        .split_focused_cases(disjunction.clone())
        .expect("the same disjunction splits again");
    assert_eq!(foreign_ids, ids, "divergent splits collide numerically");
    let foreign_marker = foreign_proof.checkpoint();
    assert!(
        both_closed
            .join_focused_cases(
                &foreign_marker,
                foreign_split,
                foreign_ids,
                disjunction.clone()
            )
            .is_err(),
        "a derivation cannot join through another split's marker"
    );

    // The legitimate join partitions by recorded attribution and retains
    // one structured step whose parent is the pre-split lineage.
    let joined = both_closed
        .join_focused_cases(&marker, split, ids, disjunction.clone())
        .expect("both recorded arms are discharged");
    assert!(joined.is_complete());
    assert!(matches!(
        joined.certificate().steps(),
        [ProofStep::Cases {
            left_proof,
            right_proof,
            ..
        }] if left_proof.steps() == [ProofStep::Known]
            && right_proof.steps() == [ProofStep::Known]
    ));
    assert!(root.certificate().steps().is_empty());
    assert_eq!(root.sole_branch_id(), Some(root_goal));

    // An incomplete sibling refuses the join transactionally.
    assert!(
        left_closed
            .join_focused_cases(&marker, split, ids, disjunction)
            .is_err(),
        "an open sibling goal must refuse the join"
    );

    // A rejected arm candidate leaves the split state untouched.
    let focused_branch = split_proof
        .focus_branch(ids[0])
        .expect("the left sibling is open");
    let error = match focused_branch.driver().apply_step(ProofStep::Intro) {
        Ok(_) => panic!("an atomic claim rejects `intro`"),
        Err(error) => error,
    };
    assert!(error.report().contains("error kind: tactic error"));
    assert!(error.report().contains("tactic: intro()"));
    assert_eq!(split_proof.branches().collect::<Vec<_>>(), ids);
    assert!(
        split_proof
            .certificate_since(&marker)
            .is_ok_and(|certificate| { certificate.steps().is_empty() })
    );
}

#[test]
fn attempt_reports_deadline_failure_instead_of_a_rejection() {
    let goal = indexed_fact(7);
    let theorem_context = pure_identity_fixture();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "deadline",
        &[],
        goal,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );

    // Without a deadline the unprovable candidate is an ordinary miss.
    let mut budget = attempt::AttemptBudget::unbounded();
    let missed = attempt::try_steps(&root, &mut budget, [ProofStep::Known])
        .expect("a rejected candidate is a miss");
    assert!(missed.is_none());

    // With the deadline exceeded, the same rejection is a tooling
    // failure: the search aborts loudly instead of reading the error as
    // one more rejected candidate and continuing.
    let aborted = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        let mut budget = attempt::AttemptBudget::unbounded();
        attempt::try_steps(&root, &mut budget, [ProofStep::Known])
    });
    assert!(
        aborted.is_err(),
        "an exceeded deadline must abort the search, not read as a miss"
    );
    let aborted = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(root))
    });
    assert!(
        aborted.is_err(),
        "the shared closure search must propagate an exceeded deadline"
    );
}

#[test]
fn proof_failure_preserves_ancestor_and_selected_lineage() {
    let goal = indexed_fact(7);
    let theorem_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: vec![goal.clone()],
        surface_requirements: SurfacePropositionMap::default(),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "transactional",
        &theorem_context.requires,
        goal,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let fork = root.clone();
    assert!(root.state.shares_state_with(&fork.state));
    assert!(Arc::ptr_eq(&root.node, &fork.node));

    assert!(
        fork.driver()
            .apply_step(ProofStep::CloseBounds(Vec::new()))
            .is_err(),
        "the cited bounds do not establish the comparison"
    );
    assert!(!root.is_complete());
    assert!(root.certificate().steps().is_empty());

    let complete = root
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the exact root fact should close the goal");
    assert!(complete.is_complete());
    assert_eq!(complete.certificate().steps(), &[ProofStep::Known]);
    assert!(!root.is_complete());
    assert!(root.certificate().steps().is_empty());
}

#[test]
fn branch_identity_is_stable_across_fork_refinement_and_closure() {
    let fact = indexed_fact(7);
    let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
    let theorem_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "identity",
        &[],
        goal,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );

    // Forking preserves every open goal's identity and allocates nothing.
    let root_id = root
        .sole_branch_id()
        .expect("a fresh proof owns its root goal");
    let fork = root.clone();
    assert_eq!(fork.sole_branch_id(), Some(root_id));

    // A goal-preserving refinement rule changes the obligation's content
    // but keeps its id and allocates no new identifier. The persistent
    // scaling of antecedent insertion is covered separately by the multi-size
    // proof-fact fork regression below.
    let introduced = root
        .driver()
        .apply_step(ProofStep::Intro)
        .expect("intro should refine the implication goal");
    assert_eq!(introduced.sole_branch_id(), Some(root_id));
    assert_eq!(introduced.branches_next_id(), root.branches_next_id());
    // Lineage records which goal each step advanced: certificate
    // extraction partitions interleaved multi-goal derivations by this
    // attribution rather than inferring ownership from final states.
    assert_eq!(introduced.node.focused_branch, root_id);
    assert_eq!(introduced.focused_branch_id(), root_id);

    // Discharge retires the id: the collection is empty and the allocator
    // never reuses the retired identifier.
    let complete = introduced
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the introduced fact should close the consequent");
    assert!(complete.is_complete());
    assert_eq!(complete.sole_branch_id(), None);
    assert_eq!(complete.branches_next_id(), introduced.branches_next_id());

    // Retiring the goal in one descendant leaves the forked sibling's
    // obligation open under the same identity.
    assert_eq!(fork.sole_branch_id(), Some(root_id));
    assert!(!fork.is_complete());
    assert!(!introduced.is_complete());
}

#[test]
fn certificate_suffix_requires_an_exact_shared_ancestor() {
    let fact = indexed_fact(7);
    let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
    let theorem_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_pure_goal(
        "suffix",
        &[],
        goal.clone(),
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let root_checkpoint = root.checkpoint();
    let introduced = root
        .driver()
        .apply_step(ProofStep::Intro)
        .expect("intro should create the exact antecedent fact");
    let introduced_checkpoint = introduced.checkpoint();
    let complete = introduced
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the introduced fact should close the consequent");

    assert_eq!(
        complete
            .certificate_since(&root_checkpoint)
            .expect("root is an ancestor")
            .steps(),
        &[ProofStep::Intro, ProofStep::Known]
    );
    assert_eq!(
        complete
            .certificate_since(&introduced_checkpoint)
            .expect("introduced proof is an ancestor")
            .steps(),
        &[ProofStep::Known]
    );
    assert!(
        root.certificate_since(&introduced_checkpoint).is_err(),
        "a descendant cannot be used as an ancestor checkpoint"
    );

    let unrelated = Proof::for_pure_goal(
        "suffix",
        &[],
        goal,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    assert!(
        complete.certificate_since(&unrelated.checkpoint()).is_err(),
        "a structurally identical but separately rooted proof cannot be spliced"
    );
}

#[test]
fn have_scope_publishes_only_a_completed_checked_body() {
    let proposition = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let theorem_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let kernel = lower_pure_theorem_proposition(
        "have",
        &proposition,
        ContractEnvironment::new(&theorem_context.values, &theorem_context.array_refs),
        &theorem_context.point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("constant equality should lower");
    let root = Proof::for_pure_goal(
        "have",
        &[],
        kernel,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let scope = root
        .driver()
        .open_have(proposition.clone())
        .expect("have should open a nested proposition proof");
    assert!(scope.clone().join().is_err());
    assert!(scope.driver().apply_step(ProofStep::Intro).is_err());
    assert!(scope.body().certificate().steps().is_empty());

    let scope = scope
        .driver()
        .apply_step(ProofStep::Known)
        .expect("constant equality should normalize inside the body");
    let enclosing = scope.join().expect("completed body should close the scope");
    assert!(!enclosing.is_complete());
    assert_eq!(enclosing.added_facts().len(), 1);
    let complete = enclosing
        .driver()
        .apply_step(ProofStep::Known)
        .expect("published have fact should close the enclosing goal");
    assert_eq!(
        complete.certificate().steps(),
        &[
            ProofStep::Have {
                proposition: proposition.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
            },
            ProofStep::Known,
        ]
    );
    assert!(!root.is_complete());
    assert!(root.certificate().steps().is_empty());
    assert!(
        root.driver()
            .apply_step(ProofStep::Have {
                proposition: proposition.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Intro]).unwrap()),
            })
            .is_err(),
        "an invalid explicit Have body must be rejected"
    );
    assert!(
        root.certificate().steps().is_empty(),
        "a rejected explicit Have body must leave its immutable root untouched"
    );

    let checked_have = root
        .driver()
        .apply_step(ProofStep::Have {
            proposition: proposition.clone(),
            proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
        })
        .expect("an explicit Have step should use the owned checked scope");
    let complete = checked_have
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the checked Have step should publish its proposition");
    assert_eq!(
        complete.certificate().steps(),
        &[
            ProofStep::Have {
                proposition,
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
            },
            ProofStep::Known,
        ]
    );
}

fn pure_have_presentation_root(surface: SyntaxProposition) -> Proof<'static> {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let theorem_context = Box::leak(Box::new(PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    }));
    let kernel = lower_pure_theorem_proposition(
        "reported have",
        &surface,
        ContractEnvironment::new(&theorem_context.values, &theorem_context.array_refs),
        &theorem_context.point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("test proposition should lower");
    // The environments and context are intentionally leaked for this small
    // presentation-only test so the returned Proof can retain its borrowed
    // construction inputs without introducing a second fixture harness.
    let predicate_environment = Box::leak(Box::new(predicate_environment));
    let click_function_environment = Box::leak(Box::new(click_function_environment));
    let theorem_environment = Box::leak(Box::new(theorem_environment));
    Proof::for_pure_goal(
        "reported have",
        &[],
        kernel,
        theorem_context,
        SpecDefinitions::new(predicate_environment, click_function_environment),
        theorem_environment,
    )
}

#[test]
fn have_scope_accepts_matching_reported_goal_and_records_introductions() {
    let binder = "written".to_string();
    let surface = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: binder.clone().into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                (binder.clone()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                (binder.clone()).into(),
            )),
        }),
    };
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).expect("have should open");
    let reported = scope
        .body()
        .goal()
        .expect("have body should have a lowered goal")
        .clone();
    let introductions = vec![LoweringIntroduction::WrittenUniversal {
        name: binder.into(),
        variable: Variable(7_654_321),
        pointer: false,
        integer: false,
    }];
    let adapted = scope
        .with_reported_goal_introductions(&reported, Some(introductions))
        .expect("matching reported goal should be accepted");
    let actual_variable = match &reported {
        Proposition::ForAll { var, .. } => *var,
        other => panic!("expected a universal reported goal, got {other:?}"),
    };
    assert!(matches!(
        adapted
            .body()
            .proposition_obligation()
            .expect("body proposition")
            .introductions
            .head(),
        Some(LoweringIntroduction::WrittenUniversal {
            name,
            variable,
            pointer: false,
            integer: false,
        }) if name.is_named("written") && *variable == *actual_variable
    ));
    assert!(adapted.body().certificate().steps().is_empty());
    assert_eq!(
        scope.body().state.locals().values,
        adapted.body().state.locals().values
    );
    assert_eq!(
        scope.body().state.locals().integer_values,
        adapted.body().state.locals().integer_values
    );
    assert_eq!(
        scope.body().state.locals().next_choice_variable,
        adapted.body().state.locals().next_choice_variable
    );
    assert_eq!(
        scope.body().state.added_facts(),
        adapted.body().state.added_facts()
    );
    assert_eq!(
        scope.body().state.checked_facts(),
        adapted.body().state.checked_facts()
    );
    assert_eq!(scope.body().goal(), adapted.body().goal());
    assert!(Arc::ptr_eq(&scope.body().node, &adapted.body().node));

    // The recorded binder id above is deliberately foreign. The adapter
    // rebounded it to the actual goal binder, and the checked
    // intro must use the kernel's already-lowered binder, then the ordinary
    // normalizer and join must recheck the resulting certificate.
    let introduced = adapted
        .driver()
        .apply_step(ProofStep::Intro)
        .expect("recorded universal should consume through checked intro");
    let completed = introduced
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the renamed universal body should normalize");
    let enclosing = completed
        .join()
        .expect("the checked intro certificate should join")
        .driver()
        .apply_step(ProofStep::Known)
        .expect("the joined have fact should close the enclosing goal");
    assert!(enclosing.is_complete());
}

#[test]
fn have_scope_does_not_expose_the_binder_of_a_negated_universal() {
    let surface = SyntaxProposition::Not(Box::new(SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "k".into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("k".into())),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        }),
    }));
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).unwrap();
    let reported = scope.body().goal().unwrap().clone();
    let adapted = scope
        .with_reported_goal_introductions(&reported, Some(vec![]))
        .expect("the lowered negated universal has no introductions");
    assert!(adapted.driver().apply_step(ProofStep::Intro).is_err());
    assert!(
        scope
            .with_reported_goal_introductions(
                &reported,
                Some(vec![LoweringIntroduction::WrittenNegation])
            )
            .is_err()
    );
    assert!(
        scope
            .with_reported_goal_introductions(
                &reported,
                Some(vec![
                    LoweringIntroduction::WrittenNegation,
                    LoweringIntroduction::WrittenUniversal {
                        name: "k".into(),
                        variable: Variable(1),
                        pointer: false,
                        integer: false,
                    },
                ])
            )
            .is_err()
    );
}

#[test]
fn have_scope_rejects_mismatched_reported_goal_transactionally() {
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).expect("have should open");
    let before = scope.body().clone();
    let wrong = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::constant(0)),
            right: Box::new(OldMachineTerm::constant(1)),
        },
        true,
    );
    let error = match scope.with_reported_goal_introductions(&wrong, Some(Vec::new())) {
        Ok(_) => panic!("a mismatched reported goal must be rejected"),
        Err(error) => error,
    };
    assert!(
        error
            .raw_summary()
            .contains("does not match its reported requirement")
    );
    assert!(scope.body().certificate().steps().is_empty());
    assert!(before.state.shares_state_with(&scope.body().state));
    assert!(Arc::ptr_eq(&before.node, &scope.body().node));
}

#[test]
fn have_scope_rejects_inconsistent_universal_binder_flags() {
    let binder = "written".to_string();
    let surface = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: binder.clone().into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                (binder.clone()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable((binder).into())),
        }),
    };
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).expect("have should open");
    let reported = scope.body().goal().expect("lowered goal").clone();
    let error = match scope.with_reported_goal_introductions(
        &reported,
        Some(vec![LoweringIntroduction::WrittenUniversal {
            name: "written".to_string().into(),
            variable: Variable(9_876_543),
            pointer: true,
            integer: false,
        }]),
    ) {
        Ok(_) => panic!("a pointer binder flag must not apply to an int32 goal"),
        Err(error) => error,
    };
    assert!(
        error
            .raw_summary()
            .contains("inconsistent `have` binder flags")
    );
}

#[test]
fn have_scope_matches_renamed_existential_display_name_and_binder() {
    let surface = SyntaxProposition::Exists {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "chosen".to_string().into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                ("chosen".to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
        }),
    };
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).expect("have should open");
    let reported = crate::kernel::quantifiers::test_exists(
        "different_display_name".to_string(),
        Variable(8_765_432),
        Sort::ProgramInt32,
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(8_765_432))),
                right: Box::new(OldMachineTerm::constant(7)),
            },
            true,
        ),
    );
    scope
        .with_reported_goal_introductions(&reported, None)
        .expect("alpha-renamed existential should match");
}

#[test]
fn have_scope_rejects_unreachable_universal_introduction() {
    let quantified = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "branch_local".to_string().into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                ("branch_local".to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                ("branch_local".to_string()).into(),
            )),
        }),
    };
    let surface = SyntaxProposition::Or(
        Box::new(quantified),
        Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        }),
    );
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).expect("have should open");
    let reported = scope.body().goal().expect("lowered goal").clone();
    let error = match scope.with_reported_goal_introductions(
        &reported,
        Some(vec![LoweringIntroduction::WrittenUniversal {
            name: "branch_local".to_string().into(),
            variable: Variable(9_876_543),
            pointer: false,
            integer: false,
        }]),
    ) {
        Ok(_) => panic!("an unreachable branch binder must not be selected"),
        Err(error) => error,
    };
    assert!(
        error
            .raw_summary()
            .contains("do not match the nested `have` binders")
    );
}

#[test]
fn have_scope_with_no_reported_introductions_is_presentation_noop() {
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
    };
    let root = pure_have_presentation_root(surface.clone());
    let scope = root.driver().open_have(surface).expect("have should open");
    let reported = scope.body().goal().expect("lowered goal").clone();
    let adapted = scope
        .with_reported_goal_introductions(&reported, None)
        .expect("matching goal without metadata should be accepted");
    assert!(scope.body().state.shares_state_with(&adapted.body().state));
    assert!(Arc::ptr_eq(&scope.body().node, &adapted.body().node));
    assert!(adapted.body().proposition_obligation().is_some());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn smart_have_scope_and_explicit_step_scale_with_local_output() {
    let proposition = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let point = crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new());
    let kernel = lower_pure_theorem_proposition(
        "smart have scaling",
        &proposition,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("constant equality should lower");
    let smart_body = [ProofTactic::Solve];
    let missing_body = [
        ProofTactic::ApplyTheorem(TheoremApplication {
            name: "missing".to_string(),
            arguments: Vec::new(),
        }),
        ProofTactic::Solve,
    ];

    for size in LOCAL_PROOF_FACT_SIZES {
        let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: point.clone(),
            values: ProgramValueBindings::new(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let root = Proof::for_pure_goal(
            "smart have scaling",
            &requires,
            kernel.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let scope = root
            .driver()
            .open_have(proposition.clone())
            .expect("have should open a nested proof");
        let error = scope
            .driver()
            .try_authoritative_linear_script(&missing_body)
            .err()
            .expect("an unknown named theorem must report the source operation's error");
        assert!(error.message().contains("unknown theorem `missing`"));
        assert!(scope.body().certificate().steps().is_empty());

        let before = fact_node_allocations();
        let selected = scope
            .driver()
            .try_authoritative_linear_script(&smart_body)
            .expect("nested smart search should not fail")
            .expect("solve should close the constant equality");
        let enclosing = selected
            .join()
            .expect("the completed nested proof should join");
        let complete = enclosing
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the published have fact should close the outer goal");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} smart scope allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            complete.certificate().steps(),
            &[
                ProofStep::Have {
                    proposition: proposition.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
                },
                ProofStep::Known,
            ]
        );

        let before = fact_node_allocations();
        let complete = root
            .driver()
            .apply_step(ProofStep::Have {
                proposition: proposition.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
            })
            .expect("the explicit Have should check through its owned scope")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the explicit Have should publish its proposition");
        let allocations = fact_node_allocations() - before;
        assert!(
            allocations <= allocation_bound,
            "size {size} explicit Have allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            complete.certificate().steps(),
            &[
                ProofStep::Have {
                    proposition: proposition.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
                },
                ProofStep::Known,
            ]
        );
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn execution_have_indexes_only_its_delta_and_scales_with_history() {
    let click_file = crate::surface::parse(
        "int32 idle() { ensures reflexive: result == result by { close(); } }",
    )
    .expect("test contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function =
        syntax::parse_function("int32 idle() { return 0; }").expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let make_root = |size: u32| {
        Proof::for_execution_frontier(
            "execution have scaling",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &[],
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        )
    };
    let reflexive = |value: u32| SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value))),
    };
    let explicit = [ProofTactic::Known];
    let mut prefix_baseline = None;
    for size in [8_u32, 16, 32, 64] {
        let root = make_root(size);
        let sibling = root.clone();
        let proposition = reflexive(1000);
        crate::kernel::proof::take_fact_entry_counts();
        take_checked_have_operations();
        let joined = root
            .driver()
            .open_have(proposition.clone())
            .expect("execution have should open")
            .driver()
            .try_authoritative_linear_script(&explicit)
            .expect("explicit body should check")
            .expect("normalization should close the nested goal")
            .join()
            .expect("completed have should join");
        let entries = crate::kernel::proof::take_fact_entry_counts();
        let operations = take_checked_have_operations();
        assert_eq!(entries.1, 0, "size {size} materialized ambient facts");
        assert_eq!(
            (entries, operations),
            *prefix_baseline.get_or_insert((entries, operations)),
            "size {size} changed have work with unrelated prefix facts"
        );
        assert_eq!(joined.certificate().steps().len(), 1);
        assert!(sibling.certificate().steps().is_empty());
        assert_eq!(sibling.facts().fact_count(), size as usize);
    }

    for count in [8_usize, 16, 32, 64] {
        let mut proof = make_root(8);
        crate::kernel::proof::take_fact_entry_counts();
        take_checked_have_operations();
        for value in 0..count {
            proof = proof
                .driver()
                .open_have(reflexive(value as u32 + 2000))
                .expect("next have should open")
                .driver()
                .try_authoritative_linear_script(&explicit)
                .expect("next explicit body should check")
                .expect("next normalization should close")
                .join()
                .expect("next have should join");
        }
        let (indexed, materialized) = crate::kernel::proof::take_fact_entry_counts();
        let operations = take_checked_have_operations();
        assert_eq!(materialized, 0, "{count} haves materialized history");
        assert!(indexed <= count, "{count} haves indexed {indexed} entries");
        assert!(
            operations <= 3 * count,
            "{count} haves checked {operations} operations"
        );
        assert_eq!(proof.certificate().steps().len(), count);
    }

    let root = make_root(8);
    let outer = root
        .driver()
        .open_have(reflexive(3000))
        .expect("outer have opens");
    let inner = outer
        .driver()
        .open_have(reflexive(3001))
        .expect("nested have opens");
    let inner = inner
        .driver()
        .try_authoritative_linear_script(&explicit)
        .expect("nested body checks")
        .expect("nested body closes");
    let outer = outer
        .join_nested(inner)
        .expect("nested have joins its parent");
    let outer = outer
        .driver()
        .apply_step(ProofStep::Known)
        .expect("outer goal still closes independently");
    let joined = outer.join().expect("outer have joins execution");
    assert!(
        matches!(joined.certificate().steps(), [ProofStep::Have { proof, .. }]
        if matches!(proof.steps(), [ProofStep::Have { .. }, ProofStep::Known]))
    );
    assert!(root.certificate().steps().is_empty());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn persistent_fact_lookup_scales_logarithmically() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    for size in [16_u32, 64, 256, 1024, 4096] {
        let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let goal = indexed_fact(size - 1);
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
            values: ProgramValueBindings::new(),
            array_refs: BTreeMap::new(),
            requires,
            surface_requirements: SurfacePropositionMap::default(),
        };
        let proof = Proof::for_pure_goal(
            "scaling",
            &theorem_context.requires,
            goal.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let shared = proof.clone();
        assert!(proof.state.shares_state_with(&shared.state));
        assert!(Arc::ptr_eq(&proof.node, &shared.node));

        let comparisons = proof.fact_lookup_comparisons(&goal);
        let logarithmic_bound = 2 * (u32::BITS - size.leading_zeros()) as usize + 2;
        assert!(
            comparisons <= logarithmic_bound,
            "size {size} lookup took {comparisons} comparisons (bound {logarithmic_bound})"
        );

        let complete = shared
            .driver()
            .apply_step(ProofStep::Known)
            .expect("fixed local step should succeed");
        assert!(complete.is_complete());
        assert!(Arc::ptr_eq(
            complete
                .node
                .parent
                .as_ref()
                .expect("successor has a parent"),
            &proof.node
        ));
        assert!(proof.certificate().steps().is_empty());
        assert_eq!(complete.certificate().steps().len(), 1);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s in the parallel gate"]
fn introduced_since_recovers_only_the_appended_delta() {
    for size in [16_u32, 64, 256, 1024, 4096] {
        let ancestor_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let ancestor = PureFactStore::from_ordered(&ancestor_facts);

        // A fork that adds two ordinary facts reports exactly those, in
        // insertion order, regardless of the shared ancestor's size.
        let first = indexed_fact(size + 1);
        let second = indexed_fact(size + 2);
        let fork = ancestor
            .with_kernel_checked_fact(first.clone())
            .with_kernel_checked_fact(second.clone());
        assert_eq!(
            fork.introduced_since(&ancestor),
            Some(vec![first.clone(), second.clone()])
        );

        // A limit below the delta stops the walk; one at it does not.
        assert_eq!(fork.introduced_since_within(&ancestor, 1), None);
        assert_eq!(
            fork.introduced_since_within(&ancestor, 2),
            Some(vec![first.clone(), second.clone()])
        );

        // A duplicate insertion introduces nothing.
        let unchanged = ancestor.with_kernel_checked_fact(indexed_fact(0));
        assert_eq!(unchanged.introduced_since(&ancestor), Some(Vec::new()));

        // The ancestor itself is a trivial delta, and identity — not
        // structure — proves the shared history: an equal-content
        // context built independently is not an ancestor.
        assert_eq!(ancestor.introduced_since(&ancestor), Some(Vec::new()));
        let rebuilt = PureFactStore::from_ordered(&ancestor_facts);
        assert_eq!(fork.introduced_since(&rebuilt), None);

        // Divergent forks are not each other's ancestors.
        let sibling = ancestor.with_kernel_checked_fact(indexed_fact(size + 3));
        assert_eq!(sibling.introduced_since(&fork), None);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn proof_fact_forks_share_context_and_local_insertions_are_logarithmic() {
    let mut allocation_samples = Vec::new();
    for size in LOCAL_PROOF_FACT_SIZES {
        let initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&initial);
        let fork = facts.clone();
        assert!(facts.shares_exact_index_with(&fork));
        assert!(facts.shares_assumptions_with(&fork));

        let added = indexed_fact(size + 1);
        let before = fact_node_allocations();
        let successor = fork.with_kernel_checked_fact(added.clone());
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        allocation_samples.push((size, logarithmic_height, allocations));
        assert!(!facts.contains(&added));
        assert!(successor.contains(&added));
        assert!(crate::kernel::search::ProofSearch::proves(
            successor.assumptions(),
            &added
        ));
    }
    let (_, base_height, base_allocations) = allocation_samples[0];
    for (size, height, allocations) in allocation_samples {
        // Compare growth with index height, independent of the number of
        // maintained indexes (now including condition congruence). A scan or
        // copy of ambient facts grows with size and violates this bound.
        let allocation_bound = base_allocations * height / base_height;
        assert!(
            allocations <= allocation_bound,
            "size {size} local insertion allocated {allocations} fact nodes (logarithmic bound {allocation_bound})"
        );
    }
}

#[test]
fn statement_fact_prefix_preserves_successor_order_without_copying_ambient_history() {
    let first = indexed_fact(1);
    let promoted = indexed_fact(2);
    let added = indexed_fact(3);
    let facts = PureFactStore::from_ordered(&[first.clone(), promoted.clone()]);
    let successor = facts.with_statement_facts(vec![promoted.clone(), added.clone()]);

    assert!(successor.shares_ordered_tail_with(&facts));
    assert_eq!(successor.to_vec(), vec![promoted, added, first]);
}

#[test]
fn check_availability_probes_equivalent_condition_polarities_by_exact_index() {
    let left = OldMachineTerm::Variable(Variable(80_000));
    let right = OldMachineTerm::Variable(Variable(80_001));
    let available = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        true,
    );
    let facts = PureFactStore::from_ordered(&[available]);
    for required in [
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            },
            false,
        ),
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(right.clone()),
                right: Box::new(left.clone()),
            },
            false,
        ),
        Proposition::Not(Box::new(Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: Box::new(right.clone()),
                right: Box::new(left.clone()),
            },
            false,
        ))),
    ] {
        assert!(facts.available_across_effects(&required, &[]));
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn proof_fact_predicate_index_ignores_unrelated_context() {
    let name = "selected".to_string();
    let predicate = Proposition::Predicate {
        name: name.clone(),
        arguments: Vec::new(),
    };
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
        initial.push(predicate.clone());
        let facts = PureFactStore::from_ordered(&initial);
        let fork = facts.clone();

        assert!(facts.shares_ordered_tail_with(&fork));
        assert!(facts.shares_exact_index_with(&fork));
        assert!(facts.shares_predicate_index_with(&fork));
        assert_eq!(facts.to_vec(), initial);
        assert_eq!(
            facts.mentioning_predicate(&name).collect::<Vec<_>>(),
            vec![&predicate]
        );
    }
}

#[test]
fn outcome_fact_deltas_share_ambient_universal_facts() {
    let universal = |index| {
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(index),
            Sort::ProgramInt32,
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(OldMachineTerm::Variable(Variable(index))),
                    // Each universal differs in content: facts that differ
                    // only in their binder are one fact.
                    right: Box::new(OldMachineTerm::constant(index as u32)),
                },
                true,
            ),
        )
    };
    for size in [8_u64, 16, 32, 64] {
        let ambient = (0..size)
            .map(|index| universal(10_000_000 + index))
            .collect::<Vec<_>>();
        let unfolded = universal(9_000_000);
        let original =
            PureFactStore::from_ordered(&ambient).with_kernel_checked_fact(unfolded.clone());
        for operations in [1_u64, 4, 16] {
            crate::kernel::proof::take_fact_entry_counts();
            let mut successor = original.clone();
            for index in 0..operations {
                successor = successor.with_kernel_checked_fact(universal(11_000_000 + index));
            }
            let (indexed, materialized) = crate::kernel::proof::take_fact_entry_counts();
            assert_eq!(
                indexed, operations as usize,
                "ambient {size}, operations {operations}"
            );
            assert_eq!(
                materialized, 0,
                "ambient facts must never be materialized by a delta"
            );
            assert!(successor.contains(&unfolded));
            assert!(!original.contains(&universal(11_000_000)));
            assert!(successor.contains(&ambient[(size - 1) as usize]));
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn proposition_unfold_uses_indexed_facts_and_persistent_local_state() {
    let click_file = crate::surface::parse(
        r#"
            predicate selected(x: int32) { x == x }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test predicate should parse");
    let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let predicate_surface = SyntaxProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            int32(7),
        ))],
    };
    // Unfolding preserves the declared int32 parameter conversion in source.
    let converted_argument = SyntaxTerm::CUnary {
        operand: Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            int32(7),
        ))),
        lowered: ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(int32(7))),
            target_type: ProgramType::Int32,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: converted_argument.clone(),
        operator: ComparisonOperator::Equal,
        right: converted_argument,
    };
    let base_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_pure_theorem_proposition(
            "persistent proposition unfold",
            surface,
            ContractEnvironment::new(&base_context.values, &base_context.array_refs),
            &base_context.point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("test proposition should lower")
    };
    let predicate = lower(&predicate_surface);
    let goal = lower(&goal_surface);

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(predicate.clone());
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            requires: requires.clone(),
            ..base_context.clone()
        };
        let root = Proof::for_pure_surface_goal(
            "persistent proposition unfold",
            &requires,
            predicate.clone(),
            predicate_surface.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        assert_eq!(
            root.facts()
                .mentioning_predicate(&"selected".to_string())
                .collect::<Vec<_>>(),
            vec![&predicate],
            "unrelated facts must not enter the selected predicate bucket"
        );
        assert!(
            root.driver()
                .apply_step(ProofStep::UnfoldProposition(
                    SyntaxProposition::PredicateCall {
                        name: "missing".into(),
                        arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                            int32(7)
                        ))]
                    }
                ))
                .is_err(),
            "an unknown predicate must reject transactionally"
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let unfold = ProofStep::UnfoldProposition(SyntaxProposition::PredicateCall {
            name: "selected".into(),
            arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(7),
            ))],
        });
        let before = fact_node_allocations();
        let unfolded = root
            .driver()
            .apply_step(unfold.clone())
            .expect("the selected predicate fact and goal should unfold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 40 * logarithmic_height + 160;
        assert!(
            allocations <= allocation_bound,
            "size {size} proposition unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(unfolded.facts().contains(&goal));
        assert_eq!(unfolded.goal(), Some(&goal));
        assert_eq!(unfolded.surface_goal(), Some(&goal_surface));

        let complete = unfolded
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the unfolded predicate fact should close the unfolded goal");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[unfold.clone(), ProofStep::Known]
        );

        let certificate =
            ProofCertificate::from_steps(vec![unfold.clone(), ProofStep::Known]).unwrap();
        let checked = root
            .driver()
            .try_authoritative_linear_script(&certificate.to_proof_tactics())
            .expect("the explicit proposition unfold script should apply through Proof")
            .expect("the explicit proposition unfold script should close");
        assert!(checked.is_complete());
        assert_eq!(checked.certificate(), certificate);
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_proposition_unfold_checks_the_same_retained_step() {
    let click_file = crate::surface::parse(
        r#"
            predicate selected(x: int32) { x == x }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test predicate should parse");
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let state = ExecutionState::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let parameter_binding = ParameterBinding::new(parsed_function.parameters(), &arguments);
    let recorded_states = RecordedStates::new();
    let predicate_surface = SyntaxProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            int32(7),
        ))],
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parameter_binding,
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("fixed-state proposition should lower")
    };
    let predicate = lower(&predicate_surface);
    let goal = lower(&goal_surface);
    let surface_propositions = SurfacePropositionMap::default();
    let root = Proof::for_fixed_state_goal(
        "fixed-state proposition unfold",
        0,
        std::slice::from_ref(&predicate),
        goal.clone(),
        parameter_binding,
        &state,
        &state,
        &recorded_states,
        &surface_propositions,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
        &[],
    );
    let certificate = ProofCertificate::from_steps(vec![
        ProofStep::UnfoldProposition(SyntaxProposition::PredicateCall {
            name: "selected".into(),
            arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(7),
            ))],
        }),
        ProofStep::Known,
    ])
    .unwrap();
    let checked = root
        .driver()
        .try_authoritative_linear_script(&certificate.to_proof_tactics())
        .expect("fixed-state unfold should use the shared Proof script driver")
        .expect("fixed-state unfold should close through the shared predicate transition");
    assert!(checked.is_complete());
    assert_eq!(checked.certificate(), certificate);
    assert!(root.certificate().steps().is_empty());

    let result = int32(7);
    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(predicate.clone());
        let root = Proof::for_fixed_state_frontier(
            "result-aware fixed-state unfold",
            0,
            &facts,
            parameter_binding,
            FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        assert!(
            root.driver()
                .apply_step(ProofStep::UnfoldProposition(
                    SyntaxProposition::PredicateCall {
                        name: "missing".into(),
                        arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                            int32(7)
                        ))]
                    }
                ))
                .is_err()
        );
        assert!(root.state.shares_state_with(&retained_root.state));

        let step = ProofStep::UnfoldProposition(SyntaxProposition::PredicateCall {
            name: "selected".into(),
            arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(7),
            ))],
        });
        let before = fact_node_allocations();
        let unfolded = root
            .driver()
            .apply_step(step.clone())
            .expect("a fixed-state proof context should accept a facts-only predicate unfold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 40 * logarithmic_height + 160;
        assert!(
            allocations <= allocation_bound,
            "size {size} result-aware frontier unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(unfolded.certificate().steps(), &[step]);
        assert_eq!(unfolded.added_facts().len(), 2);
        assert!(unfolded.added_facts().contains(&goal));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn result_aware_fixed_state_goal_focus_shares_facts_and_checks_known() {
    let state = ExecutionState::new();
    let result = int32(0);
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let goal = indexed_fact(9_000_000);
    let missing = indexed_fact(9_000_001);

    // Exact index identity rejects copying at every nonempty size.
    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(goal.clone());
        let root = Proof::for_fixed_state_frontier(
            "result-aware fixed-state goal focus",
            0,
            &facts,
            ParameterBinding::default(),
            FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let before = fact_node_allocations();
        let focused_branch = root
            .focus_fixed_state_goal(goal.clone())
            .expect("an initial fixed-state proof context should focus one ensure goal");
        // The one permitted node stores the focused branch root goal in the
        // fresh proof's goal collection; every fact index stays shared.
        assert!(
            fact_node_allocations() - before <= 1,
            "focusing a goal must share every persistent fact index"
        );
        assert!(root.facts().shares_exact_index_with(focused_branch.facts()));
        let retained_focused = focused_branch.clone();
        assert!(
            root.focus_fixed_state_goal(missing.clone())
                .expect("focusing does not prove the selected goal")
                .driver()
                .apply_step(ProofStep::Known)
                .is_err()
        );
        assert!(
            focused_branch
                .state
                .shares_state_with(&retained_focused.state)
        );

        let complete = focused_branch
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the focused exact goal should close through Proof");
        assert!(complete.is_complete());
        assert_eq!(complete.certificate().steps(), &[ProofStep::Known]);
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn fixed_state_context_have_publishes_checked_fact_for_later_scope() {
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let state = ExecutionState::new();
    let result = int32(0);
    let arguments = vec![ProgramExpression::Value(result.clone())];
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let proposition = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };

    for size in LOCAL_PROOF_FACT_SIZES {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_fixed_state_frontier(
            "fixed-state proof context have",
            0,
            &facts,
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        // An entry scope selects the producer's goal without rebuilding the
        // ambient facts. Terminal completion retains the full guarded judgment.
        let entry_kernel = root
            .driver()
            .open_have(proposition.clone())
            .unwrap()
            .goal()
            .unwrap()
            .clone();
        let entry_obligation = crate::kernel::ProofObligation::new(Proposition::Implies(
            Box::new(indexed_fact(size - 1)),
            Box::new(entry_kernel.clone()),
        ));
        let entry_before = fact_node_allocations();
        let scope = root
            .begin_loop_entry_goal(proposition.clone(), &entry_obligation)
            .unwrap();
        assert_eq!(scope.goal(), Some(&entry_kernel));
        assert!(Arc::ptr_eq(&root.context, &scope.body.context));
        assert!(
            scope.clone().join().is_err(),
            "an unfinished entry cannot publish its guard"
        );
        let checked_scope = scope.driver().apply_step(ProofStep::Known).unwrap();
        let completion = checked_scope.completed_loop_entry_goal().unwrap();
        assert!(
            completion
                .root_assumptions()
                .shares_assumptions_with(root.facts())
        );
        let phase = checked_scope.join().unwrap();
        assert_eq!(phase.certificate().steps().len(), 1);
        assert_eq!(completion.proposition(), entry_obligation.proposition());
        assert!(phase.facts().contains(entry_obligation.proposition()));
        assert!(phase.facts().contains(&entry_kernel));
        assert!(!root.facts().contains(entry_obligation.proposition()));
        let allocations = fact_node_allocations() - entry_before;
        let height = (u32::BITS - size.leading_zeros()) as usize;
        assert!(
            allocations <= 40 * height + 160,
            "entry scope at size {size} allocated {allocations} fact nodes"
        );

        // Later declarations name the original guarded judgment, not only
        // its proved body. Several successive scopes must discharge those
        // producer guards without consuming a source-level introduction.
        let mut phase = phase;
        let mut previous = entry_obligation.proposition().clone();
        for _ in 0..4 {
            let obligation = crate::kernel::ProofObligation::new(Proposition::Implies(
                Box::new(previous),
                Box::new(entry_kernel.clone()),
            ));
            let scope = phase
                .begin_loop_entry_goal(proposition.clone(), &obligation)
                .unwrap();
            assert_eq!(scope.goal(), Some(&entry_kernel));
            phase = scope
                .driver()
                .apply_step(ProofStep::Known)
                .unwrap()
                .join()
                .unwrap();
            assert!(phase.facts().contains(obligation.proposition()));
            previous = obligation.proposition().clone();
        }

        let retained_root = root.clone();
        let before = fact_node_allocations();
        let first = root
            .driver()
            .open_have(proposition.clone())
            .expect("a fixed-state proof context should open a checked have scope")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the first scope should prove the concrete equality")
            .join()
            .expect("a completed fixed-state scope should publish its fact");
        let second = first
            .driver()
            .open_have(proposition.clone())
            .expect("the checked successor should open a dependent scope")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the later scope should see the first checked fact")
            .join()
            .expect("the dependent scope should publish its retained proof");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 40 * logarithmic_height + 160;
        assert!(
            allocations <= allocation_bound,
            "size {size} two-scope fixed-state proof allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(matches!(
            second.certificate().steps(),
            [
                ProofStep::Have { proof: first, .. },
                ProofStep::Have { proof: second, .. }
            ] if first.steps() == [ProofStep::Known]
                && second.steps() == [ProofStep::Known]
        ));
        let completed = second
            .driver()
            .complete_fixed_state_obligations(std::slice::from_ref(&proposition))
            .expect("the accumulated frontier should close its external obligation");
        assert!(matches!(
            completed.steps(),
            [
                ProofStep::Have { .. },
                ProofStep::Have { .. },
                ProofStep::Known
            ]
        ));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn fixed_state_context_have_goal_does_not_reuse_an_older_surface_lowering() {
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let state = ExecutionState::new();
    let result = int32(1);
    let arguments = vec![ProgramExpression::Value(result.clone())];
    let recorded_states = RecordedStates::new();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let older = indexed_fact(9_200_000);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&surface, &older)
        .expect("the older form should be recorded");
    let root = Proof::for_fixed_state_frontier(
        "fixed-state have current goal",
        0,
        std::slice::from_ref(&older),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
        &surface_propositions,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
        &[],
    );
    let scope = root
        .driver()
        .open_have(surface)
        .expect("the current fixed-state goal should lower independently");
    assert!(
        scope.driver().apply_step(ProofStep::Known).is_err(),
        "an older fact with the same surface form must not close the current goal"
    );
    assert!(root.certificate().steps().is_empty());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn proof_if_fork_and_join_work_is_logarithmic_in_unrelated_facts() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let condition = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
    };
    let surface_goal = SyntaxProposition::Or(
        Box::new(condition.clone()),
        Box::new(SyntaxProposition::Not(Box::new(condition.clone()))),
    );

    for size in LOCAL_PROOF_FACT_SIZES {
        let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
            values: ProgramValueBindings::new(),
            array_refs: BTreeMap::new(),
            requires,
            surface_requirements: SurfacePropositionMap::default(),
        };
        let goal = lower_pure_theorem_proposition(
            "branch scaling",
            &surface_goal,
            ContractEnvironment::new(&theorem_context.values, &theorem_context.array_refs),
            &theorem_context.point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("excluded-middle goal should lower");
        let root = Proof::for_pure_goal(
            "branch scaling",
            &theorem_context.requires,
            goal,
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let before = fact_node_allocations();
        let (split_proof, split, ids) = root
            .split_focused_if(condition.clone())
            .expect("proof if should open both sibling case goals");
        let branch_allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 8 * logarithmic_height + 16;
        assert!(
            branch_allocations <= allocation_bound,
            "size {size} branch fork allocated {branch_allocations} fact nodes (bound {allocation_bound})"
        );

        let marker = split_proof.checkpoint();
        let joined = split_proof
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the condition closes the then arm")
            .focus_branch(ids[1])
            .expect("the else sibling remains open")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the exact negation closes the else arm")
            .join_focused_if(&marker, split, ids, condition.clone())
            .expect("both discharged siblings should join");
        assert!(joined.is_complete());
        assert_eq!(joined.certificate().steps().len(), 1);
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::If { then_proof, else_proof, .. }]
                if then_proof.steps() == [ProofStep::Known]
                    && else_proof.steps() == [ProofStep::Known]
        ));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn execution_frontier_rejects_proposition_closers_transactionally() {
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_fixed_state_frontier(
        "frontier",
        0,
        &[],
        ParameterBinding::default(),
        FixedStateFrame::new(&state, &state, None, &recorded_states),
        &surface_propositions,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
        &[],
    );
    let fork = root.clone();
    assert!(root.goal().is_none());
    assert!(root.state.shares_state_with(&fork.state));
    assert!(Arc::ptr_eq(&root.node, &fork.node));
    for closer in [ProofStep::Known, ProofStep::CloseBounds(Vec::new())] {
        let error = fork
            .driver()
            .apply_step(closer)
            .err()
            .expect("a proposition closer cannot close an execution frontier");
        assert!(error.message().contains("proposition goal"), "{error:?}");
    }
    assert!(!root.is_complete());
    assert!(root.added_facts().is_empty());
    assert!(root.certificate().steps().is_empty());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_witness_refines_existential_transactionally_with_constant_local_work() {
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let variable = Variable(9_000_000);
    let expected = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
            right: Box::new(OldMachineTerm::constant(7)),
        },
        true,
    );
    let goal = crate::kernel::quantifiers::test_exists(
        "chosen".to_string(),
        variable,
        Sort::ProgramInt32,
        expected,
    );
    let witness = ProofWitness::single(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
        int32(7),
    )));
    let expected_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            ("chosen".to_string()).into(),
        )),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
    };
    let surface_goal = SyntaxProposition::Exists {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "chosen".to_string().into(),
        written_name: None,
        body: Box::new(expected_surface),
    };
    let instantiated_surface = SyntaxProposition::Comparison {
        left: witness.value().clone(),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
    };

    let mut work_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_fixed_state_surface_goal(
            "persistent witness",
            0,
            &facts,
            goal.clone(),
            surface_goal.clone(),
            ParameterBinding::default(),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let wrong_type = ProofStep::Witness(ProofWitness::single(SyntaxTerm::ProgramExpression(
            ProgramExpression::Value(ProgramValue::UInt64(OldMachineTerm::constant(7))),
        )));
        let error = root
            .driver()
            .apply_step(wrong_type)
            .err()
            .expect("an ill-typed witness must reject the candidate");
        assert!(error.message().contains("wrong type"), "{error:?}");
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        // The global persistent-node counter also counts certificate and
        // temporary-state nodes. Check the actual fact-store roots instead,
        // and measure work as the unrelated fact context grows.
        let (refined, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.driver()
                .apply_step(ProofStep::Witness(witness.clone()))
        });
        let refined = refined.expect("the positional int32 witness should refine the existential");
        work_samples.push(work);
        assert!(refined.facts().shares_exact_index_with(root.facts()));
        assert!(refined.facts().shares_assumptions_with(root.facts()));
        assert!(refined.facts().shares_ordered_tail_with(root.facts()));
        assert!(refined.facts().shares_predicate_index_with(root.facts()));
        assert_eq!(
            refined.certificate().steps(),
            &[ProofStep::Witness(witness.clone())]
        );
        assert_eq!(refined.surface_goal(), Some(&instantiated_surface));
        assert!(refined.added_facts().is_empty());
        assert!(!refined.is_complete());
        let completed = refined
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the instantiated constant equality should normalize");
        assert!(completed.is_complete());
        assert_eq!(
            completed.certificate().steps(),
            &[ProofStep::Witness(witness.clone()), ProofStep::Known,]
        );
        assert!(root.certificate().steps().is_empty());
    }
    assert!(
        work_samples.iter().all(|work| *work <= work_samples[0] * 2),
        "witness work must stay bounded as unrelated facts grow: {work_samples:?}"
    );
}

#[test]
fn universal_intro_binding_is_local_to_its_focused_sibling_branch() {
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test function should parse");
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let binder = "k".to_string();
    let binder_expression =
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable((binder.clone()).into()));
    let constant = |value| SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value)));
    let surface_goal = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: binder.clone().into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: binder_expression.clone(),
            operator: ComparisonOperator::Equal,
            right: binder_expression,
        }),
    };
    let disjunction = SyntaxProposition::Or(
        Box::new(SyntaxProposition::Comparison {
            left: constant(0),
            operator: ComparisonOperator::Equal,
            right: constant(0),
        }),
        Box::new(SyntaxProposition::Comparison {
            left: constant(1),
            operator: ComparisonOperator::Equal,
            right: constant(1),
        }),
    );
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &[]),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("test proposition should lower")
    };
    let kernel_goal = lower(&surface_goal);
    let kernel_disjunction = lower(&disjunction);
    let available = [kernel_disjunction];
    let root = Proof::for_fixed_state_surface_goal(
        "goal-local forall binder",
        0,
        &available,
        kernel_goal,
        surface_goal,
        ParameterBinding::new(parsed_function.parameters(), &[]),
        &state,
        &state,
        &recorded_states,
        &surface_propositions,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
        &[],
    );
    let (split, _, ids) = root
        .split_focused_cases(disjunction)
        .expect("the exact disjunction should open sibling goals");
    let introduced = split
        .focus_branch(ids[0])
        .expect("the first sibling should be focusable")
        .driver()
        .apply_step(ProofStep::Intro)
        .expect("the universal binder should refine the first sibling");

    let binding_count = |id| match introduced.state.open_branches().obligation(id) {
        Some(Obligation::Proposition(goal)) => goal.surface_bindings.len(),
        _ => panic!("the split should retain proposition siblings"),
    };
    assert_eq!(binding_count(ids[0]), 1);
    assert_eq!(binding_count(ids[1]), 0);
    assert!(root.state.locals().values.is_empty());
    assert!(introduced.state.locals().values.is_empty());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_choose_uses_indexed_requirement_and_persistent_local_bindings() {
    let click_file = crate::surface::parse(
        r#"
            int32 choose_source(int32 x) {
                requires exists (k: int32) { k == x };
                ensures result == x by { close(); }
            }
        "#,
    )
    .expect("existential requirement should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function("int32 choose_source(int32 x) { return x; }")
        .expect("test function should parse");
    let state = ExecutionState::new().with_local("x", int32(7));
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let source_variable = Variable(9_200_000);
    let source_fact = crate::kernel::quantifiers::test_exists(
        "source_value".to_string(),
        source_variable,
        Sort::ProgramInt32,
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(source_variable)),
                right: Box::new(OldMachineTerm::constant(7)),
            },
            true,
        ),
    );
    let goal_variable = Variable(9_200_001);
    let goal = crate::kernel::quantifiers::test_exists(
        "witness".to_string(),
        goal_variable,
        Sort::ProgramInt32,
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(goal_variable)),
                right: Box::new(OldMachineTerm::constant(7)),
            },
            true,
        ),
    );

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = vec![source_fact.clone()];
        facts.extend((0..size).map(indexed_fact));
        let root = Proof::for_fixed_state_goal_with_requirements(
            "persistent choose",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            None,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
            function_block.requires(),
        );
        let retained_root = root.clone();
        let missing = root
            .driver()
            .apply_step(ProofStep::Choose(ProofChoice {
                name: "candidate".to_string(),
                source: ProofFactSource::Requirement(1),
            }))
            .err()
            .expect("an out-of-range requirement must reject the candidate");
        assert!(missing.message().contains("is out of range"));
        assert!(root.state.shares_state_with(&retained_root.state));

        let choice = ProofChoice {
            name: "candidate".to_string(),
            source: ProofFactSource::Requirement(0),
        };
        let before = fact_node_allocations();
        let chosen = root
            .driver()
            .apply_step(ProofStep::Choose(choice.clone()))
            .expect("the indexed existential requirement should introduce one local");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 48 * logarithmic_height + 64;
        assert!(
            allocations <= allocation_bound,
            "size {size} choose allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            chosen.certificate().steps(),
            &[ProofStep::Choose(choice.clone())]
        );
        assert_eq!(chosen.state.locals().values.len(), 1);
        assert!(root.state.locals().values.is_empty());

        let duplicate = chosen
            .driver()
            .apply_step(ProofStep::Choose(choice.clone()))
            .err()
            .expect("a duplicate local name must reject transactionally");
        assert!(duplicate.message().contains("already in scope"));
        assert_eq!(chosen.certificate().steps(), &[ProofStep::Choose(choice)]);

        let completed = chosen
            .driver()
            .apply_step(ProofStep::Witness(ProofWitness::single(
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    ("candidate".to_string()).into(),
                )),
            )))
            .expect("witness should resolve the one referenced proof local")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the chosen existential fact should close the refined goal");
        assert!(completed.is_complete());
        assert!(matches!(
            completed.certificate().steps(),
            [
                ProofStep::Choose(_),
                ProofStep::Witness(_),
                ProofStep::Known
            ]
        ));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn composite_body_and_explicit_definedness_requirement_share_the_entry_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let file = crate::surface::parse(
        r#"
        resource initialized_cell(p: int32*) {
            owns p[0..2];
            fact defined(*p);
        }
        int32 read(int32* p) {
            owns initialized_cell(p);
            requires defined(p[1]);
            ensures true;
        }
        "#,
    )
    .unwrap();
    let function = &file.function_blocks()[0];
    let parsed = syntax::parse_function("int32 read(int32* p) { return *p; }").unwrap();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(file.resource_definitions());
    let owner = CallerSourceOwnerId::ordinary("read.c", "read");
    let context = initial_claim_context_with_caller_owner(
        function,
        &parsed,
        &resources,
        SpecDefinitions::new(&predicates, &functions),
        "definedness at function entry",
        Some(&owner),
    )
    .unwrap();
    let entry_point = context.state.observation_point_id().unwrap();
    let mut body_fact = false;
    let mut requirement_fact = false;
    for (fact, origin) in context.pure_facts.iter().zip(&context.entry_fact_origins) {
        let Proposition::MemoryReadDefined { at, .. } = fact else {
            continue;
        };
        match origin {
            EntryFactOrigin::Derived => body_fact = true,
            EntryFactOrigin::Requirement {
                source_id,
                role: RequirementFactRole::Principal { .. },
            } if source_id.outer_ordinal == 1 => requirement_fact = true,
            _ => continue,
        }
        assert_eq!(*at, Some(entry_point), "{origin:?}");
    }
    assert!(body_fact, "missing the composite body's definedness fact");
    assert!(
        requirement_fact,
        "missing the explicit definedness requirement"
    );
}

#[test]
fn initial_entry_origins_keep_nonzero_requirement_identity_after_derived_insertions() {
    let click_file = crate::surface::parse(
        r#"
            predicate selected(x: int32) {
                x == x
            }

            int32 source_identity(int32 x) {
                requires 100 / (x + 1) >= 0;
                requires selected(x);
                requires x >= 0;
                ensures result == x by { close(); }
            }
        "#,
    )
    .expect("source-identity contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function("int32 source_identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let owner = CallerSourceOwnerId::ordinary("canonical/source.c", "source_identity");

    let context = initial_claim_context_with_caller_owner(
        function_block,
        &parsed_function,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        "source identity",
        Some(&owner),
    )
    .expect("entry context should retain exact requirement origins");

    assert_eq!(context.pure_facts.len(), context.entry_fact_origins.len());
    let selected = context
        .entry_fact_origins
        .iter()
        .enumerate()
        .filter_map(|(fact_index, origin)| match origin {
            EntryFactOrigin::Requirement {
                source_id,
                role: RequirementFactRole::Principal { .. },
            } if source_id.outer_ordinal == 1 => Some((fact_index, source_id)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].1.owner, owner);
    assert_ne!(
        selected[0].0, 1,
        "derived definedness facts should demonstrate that source ordinals are not fact indices"
    );
    assert!(
        context.entry_fact_origins[..selected[0].0]
            .iter()
            .any(|origin| matches!(origin, EntryFactOrigin::Derived))
    );

    let index = CallerRequirementIndex::from_entry_facts(
        owner.clone(),
        function_block,
        parsed_function.parameters(),
        &context.pure_facts,
        &context.entry_fact_origins,
        crate::kernel::MemoryStateIdentity::of(context.state.memory()),
    );
    let source_arguments = vec![SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
        ("x".to_string()).into(),
    ))];
    let indexed = index
        .lookup_unique_caller_requirement(
            &owner,
            "selected",
            0,
            0,
            &source_arguments,
            crate::kernel::MemoryStateIdentity::of(context.state.memory()),
        )
        .expect("the real entry pipeline should preserve the selected caller requirement");
    assert_eq!(indexed.source_id.outer_ordinal, 1);
    assert_eq!(indexed.principal_fact_index, selected[0].0);
    assert_ne!(
        indexed.source_id.outer_ordinal, indexed.principal_fact_index,
        "source ordinals and lowered fact positions are distinct identities"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn pure_rewrite_uses_indexed_equality_availability_without_changing_facts() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let equality = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("y".to_string()).into())),
    };
    let unavailable = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("z".to_string()).into())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("w".to_string()).into())),
    };
    let values = ProgramValueBindings::from([
        (
            "x".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_100_000))),
        ),
        ("y".to_string(), int32(1)),
        (
            "z".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_100_001))),
        ),
        ("w".to_string(), int32(3)),
    ]);
    let base_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values,
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let kernel_equality = lower_pure_theorem_proposition(
        "persistent rewrite",
        &equality,
        ContractEnvironment::new(&base_context.values, &base_context.array_refs),
        &base_context.point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("constant equality should lower");
    let mut allocation_baseline = None;
    // Exact index identity rejects copying at every nonempty size.
    for size in LOCAL_PROOF_FACT_SIZES {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(kernel_equality.clone());
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            requires: requires.clone(),
            ..base_context.clone()
        };
        let root = Proof::for_pure_surface_goal(
            "persistent rewrite",
            &requires,
            kernel_equality.clone(),
            equality.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let error = root
            .driver()
            .apply_step(ProofStep::Rewrite(unavailable.clone()))
            .err()
            .expect("an unavailable equality must reject the candidate");
        assert!(
            error.message().contains("exact available fact"),
            "{error:?}"
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let step = ProofStep::Rewrite(equality.clone());
        let before = fact_node_allocations();
        let rewritten = root
            .driver()
            .apply_step(step.clone())
            .expect("the exact available equality should rewrite the goal");
        let allocations = fact_node_allocations() - before;
        // Count the goal update and selected-expression binding maps together.
        // Their allocation cost must stay constant as unrelated facts grow.
        assert_eq!(
            allocations,
            *allocation_baseline.get_or_insert(allocations),
            "size {size} rewrite should not rebuild the persistent fact index"
        );
        assert!(rewritten.facts().shares_exact_index_with(root.facts()));
        assert!(rewritten.facts().shares_assumptions_with(root.facts()));
        assert_eq!(rewritten.certificate().steps(), std::slice::from_ref(&step));
        let surface = rewritten
            .surface_goal()
            .expect("the canonical successor retains its matching surface goal");
        let lowered = lower_pure_theorem_proposition(
            "persistent rewrite",
            surface,
            ContractEnvironment::new(&base_context.values, &base_context.array_refs),
            &base_context.point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the retained rewrite goal must lower");
        assert_eq!(rewritten.goal(), Some(&lowered));
        assert!(rewritten.added_facts().is_empty());
        assert!(!rewritten.is_complete());
        let complete = rewritten
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the rewritten constant equality should normalize");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[step.clone(), ProofStep::Known]
        );
        let alternative = root
            .driver()
            .apply_step(step)
            .expect("the ancestor should remain usable for another descendant");
        assert_eq!(alternative.certificate(), rewritten.certificate());
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn surface_rewrite_retains_structural_successor_and_scales() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let variable = |name: &str| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name.to_string()).into()))
    };
    let zero = SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0)));
    let comparison = |left: SyntaxTerm, operator: ComparisonOperator, right: SyntaxTerm| {
        SyntaxProposition::Comparison {
            left,
            operator,
            right,
        }
    };
    let equality = comparison(variable("x"), ComparisonOperator::Equal, variable("y"));
    let y_zero = comparison(variable("y"), ComparisonOperator::Equal, zero.clone());
    let z_zero = comparison(variable("z"), ComparisonOperator::Equal, zero.clone());
    let goal_surface = SyntaxProposition::And(
        Box::new(comparison(
            variable("x"),
            ComparisonOperator::LessEqual,
            zero.clone(),
        )),
        Box::new(comparison(
            variable("z"),
            ComparisonOperator::LessEqual,
            zero.clone(),
        )),
    );
    let rewritten_surface = SyntaxProposition::And(
        Box::new(comparison(
            variable("y"),
            ComparisonOperator::LessEqual,
            zero.clone(),
        )),
        Box::new(comparison(
            variable("z"),
            ComparisonOperator::LessEqual,
            zero,
        )),
    );
    let values = ProgramValueBindings::from([
        (
            "x".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_101_000))),
        ),
        (
            "y".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_101_001))),
        ),
        (
            "z".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_101_002))),
        ),
    ]);
    let base_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values,
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_pure_theorem_proposition(
            "persistent structural rewrite",
            surface,
            ContractEnvironment::new(&base_context.values, &base_context.array_refs),
            &base_context.point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("test proposition should lower")
    };
    let kernel_equality = lower(&equality);
    let kernel_y_zero = lower(&y_zero);
    let kernel_z_zero = lower(&z_zero);
    let kernel_goal = lower(&goal_surface);
    let rewritten_kernel_goal = lower(&rewritten_surface);
    let mut surface_requirements = SurfacePropositionMap::default();
    for (surface, kernel) in [
        (&equality, &kernel_equality),
        (&y_zero, &kernel_y_zero),
        (&z_zero, &kernel_z_zero),
    ] {
        surface_requirements
            .record_lowering(surface, kernel)
            .expect("selected rewrite premise should have an exact form");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.extend([
            kernel_equality.clone(),
            kernel_y_zero.clone(),
            kernel_z_zero.clone(),
        ]);
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            requires: requires.clone(),
            surface_requirements: surface_requirements.clone(),
            ..base_context.clone()
        };
        let root = Proof::for_pure_surface_goal(
            "persistent structural rewrite",
            &requires,
            kernel_goal.clone(),
            goal_surface.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let rewritten = root
            .driver()
            .apply_step(ProofStep::Rewrite(equality.clone()))
            .expect("the exact equality should produce a checked rewrite successor");
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(rewritten))
            .expect("smart search must not exceed its deadline")
            .expect("the rewritten Surface conjunction should retain both child proofs");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} structural rewrite allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(rewritten.goal(), Some(&rewritten_kernel_goal));
        assert_eq!(rewritten.surface_goal(), Some(&rewritten_surface));
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                ProofStep::Rewrite(root_equality),
                ProofStep::Both { left_proof: left, right_proof: right, .. },
            ] if root_equality == &equality
                && matches!(left.steps(), [ProofStep::Rewrite(_), ProofStep::Known])
                && matches!(right.steps(), [ProofStep::Rewrite(_), ProofStep::Known])
        ));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn apply_fact_uses_selected_implication_and_alpha_equivalent_antecedent() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let target_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
    };
    let theorem_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::from([(
            "x".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_000))),
        )]),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let target = lower_pure_theorem_proposition(
        "indexed implication application",
        &target_surface,
        ContractEnvironment::new(&theorem_context.values, &theorem_context.array_refs),
        &theorem_context.point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("target should lower");
    let antecedent_surface = SyntaxProposition::ForAll {
        name: "k".into(),
        written_name: None,
        click_type: ClickType::Program(InterfaceType::Int32),
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("k".into())),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("k".into())),
        }),
    };
    let implication_surface = SyntaxProposition::Implies(
        Box::new(antecedent_surface.clone()),
        Box::new(target_surface.clone()),
    );
    let required_antecedent = lower_pure_theorem_proposition(
        "selected implication antecedent",
        &antecedent_surface,
        ContractEnvironment::new(&theorem_context.values, &theorem_context.array_refs),
        &theorem_context.point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("antecedent should lower in the current comparison representation");
    let Proposition::ForAll {
        var, sort, body, ..
    } = &required_antecedent
    else {
        panic!("a universal antecedent must remain quantified");
    };
    let available_variable = Variable(8_200_000);
    let available_antecedent = crate::kernel::quantifiers::test_forall(
        Default::default(),
        available_variable,
        sort.clone(),
        substitute_int32_variable_in_proposition(
            body,
            **var,
            OldMachineTerm::Variable(available_variable),
        ),
    );
    let selected_implication = Proposition::Implies(
        Box::new(required_antecedent.clone()),
        Box::new(target.clone()),
    );
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::Implies(
                    Box::new(indexed_fact(100_000 + index)),
                    Box::new(indexed_fact(200_000 + index)),
                )
            })
            .collect::<Vec<_>>();
        facts.push(available_antecedent.clone());
        facts.push(selected_implication.clone());
        let root = Proof::for_pure_goal(
            "indexed implication application",
            &facts,
            target.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let target_key = memory_erased_proposition_key(&target);
        assert_eq!(
            root.facts()
                .implication_bucket_len(&target_key)
                .expect("selected consequent should be indexed"),
            1,
            "unrelated implications must not enter the selected bucket"
        );
        let quantified_key = quantified_equivalence_index_key(&required_antecedent)
            .expect("a universal has an alpha-invariant key");
        assert_eq!(
            root.facts()
                .quantified_bucket_len(&quantified_key)
                .expect("alpha-equivalent antecedent should be indexed"),
            1
        );

        let step = ProofStep::ApplyFactUsing {
            fact: implication_surface.clone(),
            premises: vec![antecedent_surface.clone()],
        };
        let before = fact_node_allocations();
        let extracted = root
            .driver()
            .apply_step(step.clone())
            .expect("the alpha-equivalent antecedent should discharge the implication");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 48 * logarithmic_height + 192;
        assert!(
            allocations <= allocation_bound,
            "size {size} implication application allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        assert_eq!(extracted.certificate().steps(), &[step]);
        assert!(extracted.facts().contains(&target));
        assert!(!extracted.is_complete());
        assert!(
            extracted
                .driver()
                .apply_step(ProofStep::Known)
                .unwrap()
                .is_complete()
        );

        let missing_antecedent = Proof::for_pure_goal(
            "missing implication antecedent",
            std::slice::from_ref(&selected_implication),
            target.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        assert!(
            missing_antecedent
                .driver()
                .apply_step(ProofStep::ApplyFactUsing {
                    fact: implication_surface.clone(),
                    premises: vec![antecedent_surface.clone()]
                })
                .is_err(),
            "an indexed consequent does not bypass its antecedent"
        );
        assert!(missing_antecedent.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn fixed_state_instantiate_uses_indexed_universal_and_only_named_guards() {
    let parsed_function = syntax::parse_function("int32 selected(int32 x) { return x; }")
        .expect("test function should parse");
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let x_value = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_700_000)));
    let arguments = vec![ProgramExpression::Value(x_value)];
    let value = |constant| SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(constant)));
    let variable = |name: &str| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name.to_string()).into()))
    };
    let premise = SyntaxProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::LessEqual,
        right: value(7),
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: value(7),
        operator: ComparisonOperator::Equal,
        right: variable("x"),
    };
    let quantified_surface = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "k".to_string().into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Implies(
            Box::new(SyntaxProposition::Comparison {
                left: variable("x"),
                operator: ComparisonOperator::LessEqual,
                right: variable("k"),
            }),
            Box::new(SyntaxProposition::Comparison {
                left: variable("k"),
                operator: ComparisonOperator::Equal,
                right: variable("x"),
            }),
        )),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("test proposition should lower")
    };
    let kernel_premise = lower(&premise);
    let kernel_goal = lower(&goal_surface);
    let kernel_quantified = lower(&quantified_surface);

    let quantified_prefixes = [2, 4].map(|arity| {
        let mut surface = quantified_surface.clone();
        for index in 1..arity {
            surface = SyntaxProposition::ForAll {
                click_type: ClickType::Program(InterfaceType::Int32),
                name: format!("prefix_{index}").into(),
                written_name: None,
                body: Box::new(surface),
            };
        }
        (arity, lower(&surface), surface)
    });

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut available = (0..size)
            .flat_map(|index| {
                [
                    indexed_fact(index),
                    crate::kernel::quantifiers::test_forall(
                        Default::default(),
                        Variable(9_000_000 + u64::from(index)),
                        Sort::ProgramInt32,
                        indexed_fact(100_000 + index),
                    ),
                ]
            })
            .collect::<Vec<_>>();
        available.push(kernel_premise.clone());
        available.push(kernel_quantified.clone());
        available.extend(
            quantified_prefixes
                .iter()
                .map(|(_, kernel, _)| kernel.clone()),
        );
        let root = Proof::for_fixed_state_goal(
            "indexed instantiate",
            0,
            &available,
            kernel_goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        if size == 16 {
            let premise_pairs = vec![
                (kernel_quantified.clone(), quantified_surface.clone()),
                (kernel_premise.clone(), premise.clone()),
            ];
            let selected = crate::kernel::search::ProofSearch::try_selected_forall_instantiation(
                &(root),
                &kernel_goal,
                &premise_pairs,
            );
            let selected =
                selected.expect("the selected universal candidate should close through Proof");
            assert!(selected.is_complete());
            // Propagation exposes the guarded consequence; known closes it.
            assert!(matches!(
                selected.certificate().steps(),
                [ProofStep::Instantiate { .. }, ProofStep::Known]
            ));
            let stronger = SyntaxProposition::Comparison {
                left: variable("x"),
                operator: ComparisonOperator::LessThan,
                right: value(7),
            };
            let stronger_kernel = lower(&stronger);
            let stronger_available = [kernel_quantified.clone(), stronger_kernel.clone()];
            let stronger_root = Proof::for_fixed_state_goal(
                "derived instantiate guard",
                0,
                &stronger_available,
                kernel_goal.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &state,
                &state,
                &recorded_states,
                &surface_propositions,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
                &[],
            );
            let pairs = vec![
                (kernel_quantified.clone(), quantified_surface.clone()),
                (stronger_kernel, stronger),
            ];
            let planned = crate::kernel::search::ProofSearch::try_selected_forall_instantiation(
                &stronger_root,
                &kernel_goal,
                &pairs,
            )
            .expect("a derived guard must become an ordinary have proof");
            assert!(matches!(
                planned.certificate().steps(),
                [
                    ProofStep::Have { .. },
                    ProofStep::Instantiate { .. },
                    ProofStep::Known
                ]
            ));
        }
        let retained_root = root.clone();
        let key = quantified_equivalence_index_key(&kernel_quantified)
            .expect("the selected universal should have an alpha key");
        assert_eq!(
            root.facts()
                .quantified_bucket_len(&key)
                .expect("the selected universal should be indexed"),
            1,
            "unrelated facts must not enter the selected universal bucket"
        );
        let before = fact_node_allocations();
        let selected = crate::kernel::search::ProofSearch::try_indexed_forall_instantiation(&root)
            .expect(
                "the ordinary universal should be available to search without an unfold marker",
            );
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} indexed specialization allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(selected.is_complete());
        assert!(matches!(
            selected.certificate().steps(),
            [ProofStep::Instantiate { .. }, ProofStep::Known]
        ));

        let step = ProofStep::Instantiate {
            quantified: quantified_surface.clone(),
            arguments: vec![value(7)],
        };
        let unavailable = ProofStep::Instantiate {
            quantified: SyntaxProposition::Comparison {
                left: value(0),
                operator: ComparisonOperator::Equal,
                right: value(1),
            },
            arguments: vec![value(7)],
        };
        assert!(
            root.driver().apply_step(unavailable).is_err(),
            "the selected universal must be available"
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let before = fact_node_allocations();
        let instantiated = root
            .driver()
            .apply_step(step.clone())
            .expect("the indexed universal and named guard should instantiate");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 48 * logarithmic_height + 192;
        assert!(
            allocations <= allocation_bound,
            "size {size} instantiate allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(!instantiated.is_complete());
        assert!(
            instantiated
                .driver()
                .apply_step(ProofStep::Known)
                .unwrap()
                .is_complete()
        );
        assert_eq!(
            instantiated.certificate().steps(),
            std::slice::from_ref(&step)
        );
        for (arity, _, surface) in &quantified_prefixes {
            let step = ProofStep::Instantiate {
                quantified: surface.clone(),
                arguments: vec![value(7); *arity],
            };
            let before = fact_node_allocations();
            let instantiated = root.driver().apply_step(step.clone()).unwrap();
            let allocations = fact_node_allocations() - before;
            assert!(
                allocations <= arity * allocation_bound,
                "size {size}, arity {arity}: {allocations} persistent nodes",
            );
            assert_eq!(
                instantiated.certificate().steps(),
                std::slice::from_ref(&step)
            );
            assert!(
                instantiated
                    .driver()
                    .apply_step(ProofStep::Known)
                    .unwrap()
                    .is_complete()
            );
        }
        assert!(root.certificate().steps().is_empty());
    }
}

/// A one-premise `int32` order theorem the fixtures declare themselves, so
/// theorem search and application do not depend on a library lemma.
const LESS_THAN_IMPLIES_LESS_EQUAL: &str = "theorem less_than_implies_less_equal(left: int32, right: int32) { requires left < right; ensures left <= right; }";

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn execution_apply_uses_only_named_evidence_and_forks_persistently() {
    let click_file = crate::surface::parse(
        r#"
            theorem less_than_implies_less_equal(left: int32, right: int32) { requires left < right; ensures left <= right; }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test theorem and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = ExecutionState::new();
    let left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_000)));
    let right = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_001)));
    let arguments = vec![ProgramExpression::Value(left.clone())];
    let premise = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let conclusion = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let kernel_premise = lower_fixed_state_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact premise should lower");
    let kernel_conclusion = lower_fixed_state_proposition_with_assumptions(
        &conclusion,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the theorem conclusion should lower");
    let application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(left)),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel_premise.clone());
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&premise, &kernel_premise)
            .expect("the selected premise form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent theorem application",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        assert!(
            apply_using(&root, &missing_application, vec![premise.clone()]).is_none(),
            "an unavailable execution theorem premise must not manufacture a descendant"
        );
        let selected = ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: vec![premise.clone()],
        };
        let omitted = root
            .driver()
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: Vec::new(),
            })
            .err()
            .expect("ambient facts must not discharge an omitted named premise");
        assert!(
            omitted.message().contains("required exact fact"),
            "{omitted:?}"
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let step = selected;
        let before = fact_node_allocations();
        let applied = root
            .driver()
            .apply_step(step.clone())
            .expect("the exact named premise should certify the application");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 32 * logarithmic_height + 128;
        assert!(
            allocations <= allocation_bound,
            "size {size} theorem application allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(applied.certificate().steps(), std::slice::from_ref(&step));
        assert_eq!(
            applied.added_facts(),
            std::slice::from_ref(&kernel_conclusion)
        );
        let root_execution = root.execution().expect("root execution state");
        let applied_execution = applied
            .execution()
            .expect("application successor execution state");
        assert!(
            root_execution
                .core
                .state
                .shares_storage_with(&applied_execution.core.state),
            "theorem application does not alter the C state"
        );
        let alternative = root
            .driver()
            .apply_step(step)
            .expect("the retained ancestor should support another checked descendant");
        assert_eq!(alternative.certificate(), applied.certificate());
        assert!(root.certificate().steps().is_empty());
        assert!(applied.facts().contains(&kernel_conclusion));
    }
}

#[test]
fn smart_retry_retains_checked_have_and_exact_step_after_injected_refusal() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures result == 0;
            }
        "#,
    )
    .expect("test function should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let parsed_function =
        syntax::parse_function("int32 identity(int32 x) { int32 y = x; return y; }")
            .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(&[]);
    let arguments = [ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::constant(7),
    ))];
    let state = ExecutionState::new();
    let true_fact = Proposition::condition_is(OldConditionTerm::Constant(true), true);
    let requirement = Proposition::Or(Box::new(true_fact.clone()), Box::new(true_fact.clone()));
    let root = Proof::for_execution_frontier(
        "smart retry",
        0,
        ExecutionProofState::at_entry(
            state.clone(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![requirement.clone()],
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let Some((until, _)) = crate::kernel::search::ProofSearch::try_execute_until_descendant(
        &(root),
        &ExecutionPoint::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(1),
            kind: ProgramPointKind::Entry,
        }),
    )
    .expect("execute_until should use the checked smart step route") else {
        panic!("execute_until should advance to its target");
    };
    assert!(matches!(until.certificate().steps(), [ProofStep::Step]));
    let refusal = ClickError::new("injected unresolved requirement")
        .with_unresolved_requirement(&ProofObligation::verification_condition(requirement));
    let mut retried = BTreeSet::new();
    let retried = crate::kernel::search::ProofSearch::retry_statement_after_refusal(
        &(root),
        ProofStep::Step,
        &mut retried,
        Err(refusal),
    )
    .expect("the checked have should discharge the injected requirement");
    let certificate = retried.certificate();
    let steps = certificate.steps();
    assert_eq!(steps.len(), 2);
    assert!(matches!(steps[0], ProofStep::Have { .. }));
    assert_eq!(steps[1], ProofStep::Step);
    let have = match &steps[0] {
        ProofStep::Have { proposition, .. } => proposition,
        _ => unreachable!(),
    };
    let cold = root
        .driver()
        .open_have(have.clone())
        .expect("the retained have should be independently reopenable");
    assert!(cold.driver().try_solve_closure().unwrap().is_some());

    // This injected requirement is already present in the fixture's fact
    // context, so the test intentionally checks retention mechanics and exact
    // step lineage, not semantic necessity of the Have.
    let unsupported = Proposition::Predicate {
        name: "unrepresentable".to_string(),
        arguments: Vec::new(),
    };
    let site = std::sync::Arc::new(crate::kernel::CallRequirementSite::for_requirement(
        "identity",
        "identity",
        0,
        &arguments,
        root.execution().unwrap().core.state.memory(),
    ));
    let source = std::sync::Arc::new(crate::kernel::CallRequirementSource::new(
        site, 0, None, false, None,
    ));
    let refusal = ClickError::new("injected unsupported requirement").with_unresolved_requirement(
        &ProofObligation::verification_condition(unsupported.clone())
            .with_call_requirement_site(source.clone()),
    );
    let error = match crate::kernel::search::ProofSearch::retry_statement_after_refusal(
        &(root),
        ProofStep::Step,
        &mut BTreeSet::new(),
        Err(refusal),
    ) {
        Err(error) => error,
        Ok(_) => panic!("an unrepresentable reported goal must remain a refusal"),
    };
    assert_eq!(
        error.unresolved_requirement().unwrap().proposition,
        unsupported
    );
    assert!(std::sync::Arc::ptr_eq(
        error
            .unresolved_requirement()
            .unwrap()
            .call_site
            .as_ref()
            .expect("retry preserves call-site metadata"),
        &source
    ));
    assert!(root.certificate().steps().is_empty());
    assert!(
        root.execution()
            .unwrap()
            .core
            .frontier
            .is_at_function_entry()
    );

    // A nonliteral source-backed requirement whose authoritative source entry is
    // unavailable must remain an error.  In particular, a smart execution
    // caller must not turn this structured refusal into a Planning scratch
    // descendant.  The test fixture intentionally has no source-registry
    // entry for `identity`, so the checked resolver fails closed.
    // A completely evaluated Boolean has its own complete literal spelling;
    // use a comparison here so this continues to exercise missing call metadata.
    let supported = indexed_fact(8);
    let site = std::sync::Arc::new(crate::kernel::CallRequirementSite::for_requirement(
        "identity",
        "identity",
        0,
        &arguments,
        root.execution().unwrap().core.state.memory(),
    ));
    let source = std::sync::Arc::new(crate::kernel::CallRequirementSource::new(
        site,
        0,
        Some(0),
        true,
        None,
    ));
    let refusal = ClickError::new("injected supported source refusal").with_unresolved_requirement(
        &ProofObligation::verification_condition(supported).with_call_requirement_site(source),
    );
    let error = match crate::kernel::search::ProofSearch::retry_statement_after_refusal(
        &(root),
        ProofStep::Step,
        &mut BTreeSet::new(),
        Err(refusal),
    ) {
        Err(error) => error,
        Ok(_) => panic!("a missing authoritative source must not enter Planning"),
    };
    assert!(error.unresolved_requirement().is_some());
    assert!(root.certificate().steps().is_empty());
    assert!(
        root.execution()
            .unwrap()
            .core
            .frontier
            .is_at_function_entry()
    );
}

#[test]
fn smart_retry_falls_back_from_mismatching_registry_to_exact_synthesized_existential() {
    let click_file = crate::surface::parse(
        r#"
            contract int32 Need(int32 x) {
                requires x == 0;
                ensures result == 0;
            }
            int32 caller(int32 (*callback)(int32), int32 x) {
                requires Need(callback);
                ensures result == 0;
            }
        "#,
    )
    .expect("test contract should parse");
    let function_block = click_file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == "caller")
        .expect("caller contract should exist");
    let predicate_environment = PredicateEnvironment::new(&[]).with_contracts(
        click_file.contract_definitions(),
        &click_file.program_function_names,
    );
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let parsed_function = syntax::parse_function(
        "int32 caller(int32 (*callback)(int32), int32 x) { int32 y; y = callback(x); return y; }",
    )
    .expect("test caller should parse");
    let function = parsed_function.to_kernel_function();
    let callback = syntax::parse_function("int32 callback(int32 x) { return 0; }")
        .expect("test callback should parse")
        .to_kernel_function()
        .with_contract(vec![], vec![], vec![], vec![], true);
    let callback_contract =
        FunctionContract::new("Need", callback).expect("callback contract should be representable");
    let function_environment =
        ExecutionEnvironment::new().with_function_contract(callback_contract);
    let resource_environment = ResourceEnvironment::new(&[]);
    let (state, arguments, pure_facts, _) = initial_claim_context(
        function_block,
        &parsed_function,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        "registry mismatch retry",
    )
    .expect("production-shaped caller context should initialize");
    let synthesized_surface = SyntaxProposition::Exists {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "k".into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("k".into())),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                parsed_function.parameters()[1].binding_name().clone(),
            )),
        }),
    };
    let requirement = lower_fixed_state_proposition_with_assumptions(
        &synthesized_surface,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the existential requirement should lower");
    assert!(matches!(&requirement, Proposition::Exists { .. }));
    let synthesized = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        &state,
    )
    .expect("the scalar existential should synthesize");
    assert!(matches!(synthesized, SyntaxProposition::Exists { .. }));
    let actual_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            parsed_function.parameters()[1].binding_name().clone(),
        )),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let actual_requirement = lower_fixed_state_proposition_with_assumptions(
        &actual_surface,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the named contract requirement should lower");

    let registry = std::sync::Arc::new(
        FunctionSourceRegistry::from_function_blocks(
            &crate::surface::validation::combined_external_function_blocks(&click_file)
                .expect("standard function contracts should load"),
        )
        .expect("source registry should build"),
    );
    let root = Proof::for_execution_frontier(
        "registry mismatch retry",
        0,
        ExecutionProofState::at_entry(
            state,
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        [
            pure_facts.into_vec(),
            vec![requirement.clone(), actual_requirement],
        ]
        .concat(),
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            function_source_registry: registry,
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let Some((at_call, _)) = crate::kernel::search::ProofSearch::try_execute_until_descendant(
        &(root),
        &ExecutionPoint::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(1),
            kind: ProgramPointKind::Entry,
        }),
    )
    .expect("declaration should advance to the need call") else {
        panic!("execution should reach the call frontier");
    };
    for (label, callee, interface, ordinal, source_arguments) in [
        (
            "wrong callee",
            "other_callback",
            "Need",
            0,
            vec![ProgramExpression::Variable(
                parsed_function.parameters()[1].binding_name().clone(),
            )],
        ),
        (
            "wrong interface",
            "callback",
            "Other",
            0,
            vec![ProgramExpression::Variable(
                parsed_function.parameters()[1].binding_name().clone(),
            )],
        ),
        (
            "wrong argument",
            "callback",
            "Need",
            0,
            vec![ProgramExpression::Value(int32(7))],
        ),
        (
            "wrong ordinal",
            "callback",
            "Need",
            1,
            vec![ProgramExpression::Variable(
                parsed_function.parameters()[1].binding_name().clone(),
            )],
        ),
    ] {
        let site = std::sync::Arc::new(crate::kernel::CallRequirementSite::for_requirement(
            callee,
            interface,
            0,
            &source_arguments,
            at_call.execution().unwrap().core.state.memory(),
        ));
        let source = std::sync::Arc::new(crate::kernel::CallRequirementSource::new(
            site,
            0,
            Some(ordinal),
            false,
            None,
        ));
        let refusal = ClickError::new("injected unauthorized source").with_unresolved_requirement(
            &ProofObligation::verification_condition(requirement.clone())
                .with_call_requirement_site(source),
        );
        let before = at_call.certificate();
        let error = match crate::kernel::search::ProofSearch::retry_statement_after_refusal(
            &(at_call),
            ProofStep::StepContract("Need".into()),
            &mut BTreeSet::new(),
            Err(refusal),
        ) {
            Err(error) => error,
            Ok(_) => panic!("{label} metadata must be refused before synthesis"),
        };
        assert_eq!(error.message(), "injected unauthorized source");
        assert!(error.unresolved_requirement().is_some());
        assert_eq!(at_call.certificate(), before);
    }
    let site = std::sync::Arc::new(crate::kernel::CallRequirementSite::for_requirement(
        "callback",
        "Need",
        0,
        &[ProgramExpression::Variable(
            parsed_function.parameters()[1].binding_name().clone(),
        )],
        at_call.execution().unwrap().core.state.memory(),
    ));
    let source = std::sync::Arc::new(crate::kernel::CallRequirementSource::new(
        site,
        0,
        Some(0),
        false,
        None,
    ));
    let refusal = ClickError::new("injected registry mismatch").with_unresolved_requirement(
        &ProofObligation::verification_condition(requirement.clone())
            .with_call_requirement_site(source),
    );
    let step = ProofStep::StepContract("Need".into());
    let retried = crate::kernel::search::ProofSearch::retry_statement_after_refusal(
        &(at_call),
        step,
        &mut BTreeSet::new(),
        Err(refusal),
    )
    .expect("the exact synthesized fallback should be retained");
    let certificate = retried.certificate();
    let Some(ProofStep::Have { proposition, .. }) = certificate.steps().get(1) else {
        panic!("retry should retain a Have before the call step");
    };
    assert!(matches!(proposition, SyntaxProposition::Exists { .. }));
    let expected = substitute_click_proposition(
        &synthesized,
        &BTreeMap::from([(
            "x".to_owned(),
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                parsed_function.parameters()[1].binding_name().clone(),
            )),
        )]),
    )
    .unwrap();
    let actual = at_call
        .lower_surface_proposition_direct(proposition, "synthesized retry")
        .unwrap();
    let expected = at_call
        .lower_surface_proposition_direct(&expected, "expected retry")
        .unwrap();
    assert!(crate::kernel::proof::propositions_are_alpha_equal(
        &actual, &expected
    ));
}

#[test]
fn supported_source_refusal_on_branch_does_not_enter_planning() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures result == 0;
            }
        "#,
    )
    .expect("test function should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let parsed_function =
        syntax::parse_function("int32 identity(int32 x) { if (x) { return x; } return x; }")
            .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(&[]);
    let arguments = [ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::constant(7),
    ))];
    let root = Proof::for_execution_frontier(
        "smart branch refusal",
        0,
        ExecutionProofState::at_entry(
            ExecutionState::new(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        Vec::new(),
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let site = std::sync::Arc::new(crate::kernel::CallRequirementSite::for_requirement(
        "identity",
        "identity",
        0,
        &arguments,
        root.execution().unwrap().core.state.memory(),
    ));
    let source = std::sync::Arc::new(crate::kernel::CallRequirementSource::new(
        site,
        0,
        Some(0),
        true,
        None,
    ));
    let refusal = ClickError::new("injected supported branch refusal").with_unresolved_requirement(
        &ProofObligation::verification_condition(Proposition::condition_is(
            OldConditionTerm::Constant(true),
            true,
        ))
        .with_call_requirement_site(source),
    );
    let mut refusal = Some(refusal);
    let result = crate::kernel::search::ProofSearch::try_statement_step_with_apply(&(root), |_| {
        Err(refusal
            .take()
            .expect("the branch selector should invoke the test operation once"))
    });
    assert!(
        result.is_err(),
        "supported refusal must not become a planner miss"
    );
    assert!(root.certificate().steps().is_empty());
    assert!(
        root.execution()
            .unwrap()
            .core
            .frontier
            .is_at_function_entry()
    );
}

/// A retained-have retry must use the caller's recorded qualified spelling
/// when the requirement reads a callee-owned static object.  This helper uses
/// the same indexed surface map that ordinary checked construction receives;
/// keeping the requirement in the root facts makes the closure independently
/// checkable while still forcing retry to synthesize its surface spelling.
fn assert_static_array_retry_uses_recorded_qualified_source(block: &str, name: &str, cells: usize) {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures result == 0;
            }
        "#,
    )
    .expect("test function should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let parsed_function =
        syntax::parse_function("int32 identity(int32 x) { int32 y = x; return y; }")
            .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(&[]);
    let arguments = [ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::constant(7),
    ))];
    let state = ExecutionState::new().with_memory(SymbolicMemory::new().with_block(
        block,
        4 * u32::try_from(cells).expect("test array size should fit in a block"),
    ));
    let base = ProgramValue::typed_pointer(
        Address::new(
            AddressBase::Concrete(block.into()),
            AddressOffset::constant(0),
        ),
        ProgramType::Int32Pointer,
    );
    let mut surface_propositions = SurfacePropositionMap::default();
    let mut lowered_clauses = Vec::new();
    for index in 0..cells {
        // The caller's explicit contract records the qualified load through
        // an equality, while the callee's requirement uses the same load in
        // its bound.  Record that source first, just as checked construction
        // does when it lowers the caller contract.
        let source_surface = SyntaxProposition::Comparison {
            left: SyntaxTerm::Index(
                Box::new(SyntaxTerm::QualifiedC {
                    name: name.to_string(),
                    lowered: ProgramExpression::Value(base.clone()),
                }),
                Box::new(SyntaxTerm::IntegerLiteral(index.to_string())),
            ),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                OldMachineTerm::constant(5),
            ))),
        };
        let source_lowered = lower_fixed_state_proposition_with_assumptions(
            &source_surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("qualified static source cell should lower");
        surface_propositions
            .record_lowering(&source_surface, &source_lowered)
            .expect("qualified static source lowering should be recorded");

        for (operator, bound) in [
            (ComparisonOperator::GreaterThan, -1000i32),
            (ComparisonOperator::LessThan, 1000i32),
        ] {
            let surface = SyntaxProposition::Comparison {
                left: SyntaxTerm::Index(
                    Box::new(SyntaxTerm::QualifiedC {
                        name: name.to_string(),
                        lowered: ProgramExpression::Value(base.clone()),
                    }),
                    Box::new(SyntaxTerm::IntegerLiteral(index.to_string())),
                ),
                operator,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(bound as u32))),
            };
            lowered_clauses.push(
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    &PureFactContext::new(),
                    ParameterBinding::new(parsed_function.parameters(), &arguments),
                    FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                    SpecDefinitions::new(&predicate_environment, &click_function_environment),
                )
                .expect("qualified static bound should lower"),
            );
        }
    }
    let lowered = lowered_clauses
        .into_iter()
        .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right)))
        .expect("test array should have at least one cell");
    let root = Proof::for_execution_frontier(
        "static retry",
        0,
        ExecutionProofState::at_entry(
            state,
            ExecutionFrontier::default(),
            RecordedStates::new(),
            surface_propositions,
            PersistentSequence::default(),
        ),
        vec![lowered.clone()],
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let refusal = ClickError::new("injected static-array requirement")
        .with_unresolved_requirement(&ProofObligation::verification_condition(lowered));
    let retried = crate::kernel::search::ProofSearch::retry_statement_after_refusal(
        &(root),
        ProofStep::Step,
        &mut BTreeSet::new(),
        Err(refusal),
    )
    .expect("recorded qualified static cell should synthesize during retry");
    let certificate = retried.certificate();
    let [ProofStep::Have { proposition, .. }, ProofStep::Step] = certificate.steps() else {
        panic!("retry should retain one checked Have before the exact Step");
    };
    let cold = root
        .driver()
        .open_have(proposition.clone())
        .expect("retained qualified Have should reopen cold");
    assert!(cold.driver().try_solve_closure().unwrap().is_some());
}

#[test]
fn smart_retry_uses_file_scope_static_array_qualified_source() {
    assert_static_array_retry_uses_recorded_qualified_source(
        "global:values#file-static:alpha.c",
        "alpha_file::values",
        2,
    );
}

#[test]
fn smart_retry_uses_static_local_array_qualified_source() {
    assert_static_array_retry_uses_recorded_qualified_source(
        "static:increment_twice:values#static0",
        "static_local::increment_twice::values",
        3,
    );
}

#[test]
fn nested_have_closes_with_known_after_apply() {
    let click_file = crate::surface::parse(
        r#"
            theorem less_than_implies_less_equal(left: int32, right: int32) { requires left < right; ensures left <= right; }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test theorem and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = ExecutionState::new();
    let left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_000)));
    let right = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_000_001)));
    let arguments = vec![ProgramExpression::Value(left.clone())];
    let premise = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let conclusion = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let kernel_premise = lower_fixed_state_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact premise should lower");
    let application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(left)),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };
    let pure_facts = vec![kernel_premise.clone()];
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&premise, &kernel_premise)
        .expect("the selected premise form should be recorded");
    let root = Proof::for_execution_frontier(
        "trailing `known`",
        0,
        ExecutionProofState::at_entry(
            state.clone(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            surface_propositions,
            PersistentSequence::default(),
        ),
        pure_facts,
        ExecutionProofConstants::default(),
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    // The application provides the fact consumed by the final closer.
    let scope = root
        .driver()
        .open_have(conclusion.clone())
        .expect("the have scope opens on the execution proof");
    let script = [
        ProofTactic::ApplyTheorem(application.clone()),
        ProofTactic::Known,
    ];
    let closed = scope
        .driver()
        .try_authoritative_linear_script(&script)
        .expect("the nested script is a bounded check");
    assert!(
        closed.is_some(),
        "the final closer should consume the applied fact"
    );

    let script = [
        ProofTactic::ApplyTheoremUsing {
            application,
            premises: vec![premise.clone()],
        },
        ProofTactic::Have(ProofHave {
            proposition: conclusion.clone(),
            proof: SourceProof::Script(vec![ProofTactic::Known]),
        }),
        ProofTactic::Known,
    ];
    take_checked_have_operations();
    let completed = scope
        .driver()
        .try_authoritative_linear_script(&script)
        .unwrap()
        .unwrap();
    assert_eq!(
        take_checked_have_operations(),
        5,
        "three written proof steps plus the nested have's open and join"
    );
    assert!(matches!(
        completed.body().certificate().steps(),
        [
            ProofStep::ApplyTheoremUsing { .. },
            ProofStep::Have { .. },
            ProofStep::Known
        ]
    ));
    let error = scope
        .driver()
        .try_authoritative_linear_script(&[
            ProofTactic::ApplyTheoremUsing {
                application: missing_application,
                premises: vec![premise],
            },
            ProofTactic::Known,
        ])
        .err()
        .expect("wrong theorem guards must preserve their checked error");
    assert!(error.message().contains("apply"), "{error:?}");
    assert!(scope.body().certificate().steps().is_empty());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn branch_theorem_search_retains_checked_arm_steps_and_scales() {
    let click_file = crate::surface::parse(
        r#"
            theorem less_than_implies_less_equal(left: int32, right: int32) { requires left < right; ensures left <= right; }
            int32 choose(int32 left, int32 right, int32 choose_left) {
                ensures reflexive_result: result == result by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function(
        "int32 choose(int32 left, int32 right, int32 choose_left) { if (choose_left != 0) { return left; } else { return right; } }",
    )
    .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = ExecutionState::new();
    let left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_050_000)));
    let right = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_050_001)));
    let choose_left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_050_002)));
    let arguments = vec![
        ProgramExpression::Value(left.clone()),
        ProgramExpression::Value(right.clone()),
        ProgramExpression::Value(choose_left),
    ];
    let premise = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let kernel_premise = lower_fixed_state_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact theorem premise should lower");
    let application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(left)),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: application.name.clone(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };

    let mut samples = Vec::new();
    let mut nested_samples = Vec::new();
    let mut execute_samples = Vec::new();
    let mut outcome_samples = Vec::new();
    for size in LOCAL_PROOF_FACT_SIZES {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel_premise.clone());
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&premise, &kernel_premise)
            .expect("the selected premise form should be recorded");
        let root = Proof::for_execution_frontier(
            "branch theorem search",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "choose".to_string(),
                    claim: ContractProofClaim::Grouped,
                }),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("the symbolic condition should expose two theorem-search arms");
        let then_id = record.arm_id(true).expect("then arm is feasible");
        let else_id = record.arm_id(false).expect("else arm is feasible");
        let then_arm = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open");
        assert!(
            apply_using(&then_arm, &missing_application, vec![premise.clone()]).is_none(),
            "an unavailable theorem premise must not manufacture an arm descendant"
        );

        let before = fact_node_allocations();
        let branches = apply_using(
            &apply_using(&then_arm, &application, vec![premise.clone()])
                .expect("then arm theorem application should retain its checked step")
                .focus_split_arm(&record, false)
                .expect("the else sibling is open"),
            &application,
            vec![premise.clone()],
        )
        .expect("else arm theorem application should retain its checked step");
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        let arm_steps = branches
            .partition_steps_since(&record.marker, record.split, [then_id, else_id])
            .expect("both theorem-search arms partition by attribution");
        for steps in &arm_steps {
            assert!(matches!(
                steps.as_slice(),
                [ProofStep::ApplyTheoremUsing {
                    application: retained,
                    premises,
                }] if retained == &application && premises == std::slice::from_ref(&premise)
            ));
        }

        // The cross-arm nested-splice rejection is structural in the
        // sibling form: a scope join produces one direct successor of
        // the arm that opened it, so there is no operation that could
        // publish it into the sibling; the scope lineage regressions
        // pin that law.
        let before_nested = fact_node_allocations();
        let nested_branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .open_have(premise.clone())
            .expect("the then arm should open a proposition proof")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the root premise should close the then-arm proof")
            .join()
            .expect("the completed proof should advance the then arm")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .open_have(premise.clone())
            .expect("the else arm should open a proposition proof")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the root premise should close the else-arm proof")
            .join()
            .expect("the completed proof should advance the else arm");
        nested_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before_nested,
        ));
        let nested_steps = nested_branches
            .partition_steps_since(&record.marker, record.split, [then_id, else_id])
            .expect("both nested-proof arms partition by attribution");
        for steps in &nested_steps {
            assert!(matches!(
                steps.as_slice(),
                [ProofStep::Have {
                    proposition: retained,
                    proof,
                }] if retained == &premise
                    && proof.steps() == [ProofStep::Known]
            ));
        }

        let before_execute = fact_node_allocations();
        let execute_branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .try_focused_execute_to_exit()
            .expect("then-arm execution search should run")
            .expect("the direct then return should produce a checked descendant")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .try_focused_execute_to_exit()
            .expect("else-arm execution search should run")
            .expect("the direct else return should produce a checked descendant");
        let execute_steps = execute_branches
            .partition_steps_since(&record.marker, record.split, [then_id, else_id])
            .expect("both terminal execution arms partition by attribution");
        for steps in &execute_steps {
            assert!(
                matches!(
                    steps.as_slice(),
                    [ProofStep::Step] | [ProofStep::Step, ProofStep::Step]
                ),
                "{steps:#?}"
            );
        }
        let terminal = execute_branches
            .join_focused_execution_terminal(&record)
            .expect("the two checked return arms should join as terminal outcomes");
        assert!(matches!(
            terminal.certificate().steps(),
            [ProofStep::If {
                then_proof,
                else_proof,
                ..
            }] if then_proof.steps().len() == 2 && else_proof.steps().len() == 2
        ));
        execute_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before_execute,
        ));
        assert!(matches!(
            terminal.certificate().steps(),
            [ProofStep::If { .. }]
        ));
        assert!(root.certificate().steps().is_empty());

        // The terminal function exit derives its typed outcome goal set:
        // one sibling goal per returning path in one proof, each owning
        // its path-local result and facts while borrowing the frontier
        // state by identity. The ancestor keeps its single frontier.
        let before_outcomes = fact_node_allocations();
        let (outcomes, outcome_ids, _) = terminal
            .split_function_outcomes()
            .expect("the terminal execution should expose typed outcome goals");
        outcome_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before_outcomes,
        ));
        assert_eq!(outcome_ids.len(), 2);
        assert_eq!(outcomes.branches().collect::<Vec<_>>(), outcome_ids);
        assert!(!outcomes.is_complete());
        assert_eq!(terminal.branches().count(), 1);
        let then_outcome = outcomes
            .focus_branch(outcome_ids[0])
            .expect("the first outcome goal is open");
        let else_outcome = outcomes
            .focus_branch(outcome_ids[1])
            .expect("the second outcome goal is open");
        assert_ne!(
            then_outcome.outcome_result(),
            else_outcome.outcome_result(),
            "distinct return paths own distinct path-local results"
        );
        assert!(
            then_outcome.refresh_outcome_from(&else_outcome).is_err(),
            "a retained judgment cannot adopt its sibling's result or resources"
        );
        for outcome in [&then_outcome, &else_outcome] {
            assert!(Arc::ptr_eq(
                outcome
                    .branch_execution()
                    .expect("each outcome borrows the frontier state"),
                terminal
                    .branch_execution()
                    .expect("the terminal frontier owns its state"),
            ));
        }
        assert!(
            outcomes.split_function_outcomes().is_err(),
            "an outcome goal is not a frontier and cannot derive again"
        );
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} two-arm theorem search allocated {allocations} persistent nodes (bound {bound})"
        );
    }
    let (_, base_height, base_allocations) = nested_samples[0];
    for (size, height, allocations) in nested_samples {
        let bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} two-arm nested proof allocated {allocations} persistent nodes (bound {bound})"
        );
    }
    let (_, base_height, base_allocations) = execute_samples[0];
    for (size, height, allocations) in execute_samples {
        let bound = base_allocations + 128 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} two-arm terminal execution and frame allocated {allocations} persistent nodes (bound {bound})"
        );
    }
    let (_, base_height, base_allocations) = outcome_samples[0];
    for (size, height, allocations) in outcome_samples {
        let bound = base_allocations + 64 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} outcome-goal derivation allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_apply_search_uses_indexes_and_retains_its_checked_successor() {
    let click_file = crate::surface::parse(
        r#"
            theorem less_than_implies_less_equal(left: int32, right: int32) { requires left < right; ensures left <= right; }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let state = ExecutionState::new();
    let left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_100_000)));
    let right = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_100_001)));
    let arguments = vec![ProgramExpression::Value(left.clone())];
    let parameter_binding = ParameterBinding::new(parsed_function.parameters(), &arguments);
    let premise = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let conclusion = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let recorded_states = RecordedStates::new();
    let kernel_premise = lower_fixed_state_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        parameter_binding,
        FixedStateFrame::new(&state, &state, None, &recorded_states),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact premise should lower");
    let kernel_conclusion = lower_fixed_state_proposition_with_assumptions(
        &conclusion,
        &PureFactContext::new(),
        parameter_binding,
        FixedStateFrame::new(&state, &state, None, &recorded_states),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the theorem conclusion should lower");
    let application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(left)),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&premise, &kernel_premise)
        .expect("the selected premise form should be recorded");

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(Proposition::And(
            Box::new(kernel_premise.clone()),
            Box::new(indexed_fact(size + 10_000)),
        ));
        let goal = Proposition::And(
            Box::new(kernel_conclusion.clone()),
            Box::new(kernel_premise.clone()),
        );
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state theorem search",
            0,
            &facts,
            goal,
            parameter_binding,
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let extracted = root
            .driver()
            .apply_step(known_have_step(premise.clone()))
            .expect("a checked predecessor should promote the indexed conjunct");
        assert!(
            apply_using(&extracted, &missing_application, vec![premise.clone()]).is_none(),
            "an unavailable fixed-state theorem premise must not manufacture a descendant"
        );
        let step = ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: vec![premise.clone()],
        };
        let tactics = [
            ProofTactic::Have(ProofHave {
                proposition: premise.clone(),
                proof: SourceProof::Script(vec![ProofTactic::Known]),
            }),
            ProofTactic::ApplyTheorem(application.clone()),
            ProofTactic::Solve,
        ];
        let before_apply = fact_node_allocations();
        let complete = root
            .driver()
            .try_authoritative_linear_script(&tactics)
            .expect("mixed linear search should not fail")
            .expect("extract, smart apply, and solve should close the goal");
        let allocations = fact_node_allocations() - before_apply;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} mixed fixed-state script allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps().first(),
            Some(&known_have_step(premise.clone()))
        );
        assert_eq!(
            complete.certificate().steps().get(1),
            Some(&ProofStep::Have {
                proposition: premise.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
            })
        );
        assert_eq!(complete.certificate().steps().get(2), Some(&step));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn result_aware_fixed_state_apply_scales_with_unrelated_facts() {
    let click_file = crate::surface::parse(
        r#"
            theorem result_reflexive(value: int32) {
                ensures value == value by { close(); }
            }

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                step_until(function.exit);
                have result == result by {
                    apply(result_reflexive(result));
                    close();
                }
                close();
            }
        "#,
    )
    .expect("result-aware theorem application should parse");
    let function_block = &click_file.function_blocks()[0];
    let SourceProof::Script(grouped_tactics) = function_block
        .grouped_proof()
        .expect("test function should have a grouped proof")
    else {
        panic!("test function should have a proof script");
    };
    let have = grouped_tactics
        .iter()
        .find_map(|tactic| match tactic {
            ProofTactic::Have(have) => Some(have),
            _ => None,
        })
        .expect("grouped proof should contain the result-aware have");
    let SourceProof::Script(have_tactics) = &have.proof else {
        panic!("result-aware have should contain a proof script");
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(8_150_000)),
    ))];
    let result = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_150_001)));
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let kernel_goal = lower_fixed_state_proposition_with_assumptions(
        &have.proposition,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the result-aware goal should lower");

    for size in LOCAL_PROOF_FACT_SIZES {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_fixed_state_goal_with_requirements(
            "persistent result-aware theorem search",
            0,
            &facts,
            kernel_goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
            None,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
            function_block.requires(),
        );
        let before = fact_node_allocations();
        let complete = root
            .driver()
            .try_authoritative_linear_script(have_tactics)
            .expect("result-aware theorem search should not fail")
            .expect("result-aware theorem application and solve should close the goal");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} result-aware fixed-state script allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(complete.is_complete());
        assert!(matches!(
            complete.certificate().steps().first(),
            Some(ProofStep::ApplyTheorem(application)) if application.name == "result_reflexive"
        ));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn result_aware_fixed_state_context_apply_is_indexed_and_transactional() {
    let click_file = crate::surface::parse(
        r#"
            theorem less_than_implies_less_equal(left: int32, right: int32) { requires left < right; ensures left <= right; }
            int32 bounded(int32 upper) {
                ensures result <= upper;
            } by {
                step_until(function.exit);
                apply(less_than_implies_less_equal(result, upper));
                close();
            }
        "#,
    )
    .expect("result-aware explicit application should parse");
    let function_block = &click_file.function_blocks()[0];
    let SourceProof::Script(tactics) = function_block
        .grouped_proof()
        .expect("test function should have a grouped proof")
    else {
        panic!("test function should have a proof script");
    };
    let application = tactics
        .iter()
        .find_map(|tactic| match tactic {
            ProofTactic::ApplyTheorem(application) => Some(application),
            _ => None,
        })
        .expect("grouped proof should contain a theorem application");
    let [result_expression, upper_expression] = application.arguments.as_slice() else {
        panic!("the application should bind the result and the upper bound");
    };
    let surface_premise = SyntaxProposition::Comparison {
        left: result_expression.clone(),
        operator: ComparisonOperator::LessThan,
        right: upper_expression.clone(),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 bounded(int32 upper) { return upper; }")
        .expect("test C function should parse");
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(8_155_001)),
    ))];
    let result = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_155_000)));
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let kernel_premise = lower_fixed_state_proposition_with_assumptions(
        &surface_premise,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the result-aware theorem premise should lower");
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&surface_premise, &kernel_premise)
        .expect("the selected premise form should be recorded");

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_premise.clone());
        let root = Proof::for_fixed_state_frontier(
            "persistent result-aware outcome apply",
            0,
            &facts,
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let missing = root
            .driver()
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: Vec::new(),
            })
            .err()
            .expect("ambient availability must not discharge an omitted premise");
        assert!(missing.message().contains("required exact fact"));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let step = ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: vec![surface_premise.clone()],
        };
        let before_apply = fact_node_allocations();
        let applied = root
            .driver()
            .apply_step(step.clone())
            .expect("the selected result-aware theorem step should check");
        let allocations = fact_node_allocations() - before_apply;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} result-aware frontier apply allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(!applied.is_complete());
        assert_eq!(applied.certificate().steps(), &[step]);
        assert_eq!(applied.added_facts().len(), 1);
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s in the parallel gate"]
fn fixed_state_transport_can_follow_another_checked_step() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = ExecutionState::new();
    let source = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(8_160_000)),
        ))),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(8_160_001)),
        ))),
    };
    let extracted = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(8_160_002)),
        ))),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(8_160_003)),
        ))),
    };
    let missing = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(8_160_006)),
        ))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(8_160_007)),
        ))),
    };
    let recorded_states = RecordedStates::new();
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &[]),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("test proposition should lower")
    };
    let kernel_source = lower(&source);
    let kernel_extracted = lower(&extracted);
    let surface_propositions = SurfacePropositionMap::default();
    let result = int32(0);
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_source.clone());
        facts.push(Proposition::And(
            Box::new(kernel_extracted.clone()),
            Box::new(indexed_fact(8_160_004)),
        ));
        let root = Proof::for_fixed_state_frontier(
            "nested result-aware fixed-state transport",
            0,
            &facts,
            ParameterBinding::new(parsed_function.parameters(), &[]),
            FixedStateFrame::new(&state, &state, Some(&result), &recorded_states),
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let refined = root
            .driver()
            .apply_step(known_have_step(extracted.clone()))
            .expect("the predecessor should advance the proof");
        let retained_refined = refined.clone();
        let rejected = refined
            .driver()
            .apply_ordinary_transport_steps(&missing, vec![ProofStep::Known]);
        assert!(rejected.is_err());
        assert!(refined.state.shares_state_with(&retained_refined.state));
        if size == 16 {
            assert!(
                crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                    &(refined),
                    &source,
                    &missing,
                    std::iter::empty()
                )
                .expect("an ordinary optional transport miss is not a verification refusal")
                .is_none()
            );
            assert!(
                crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
                    crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                        &(refined),
                        &source,
                        &missing,
                        std::iter::empty(),
                    )
                })
                .is_err(),
                "an interrupted search must not become an ordinary miss"
            );
            let searched = crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                &(refined),
                &source,
                &source,
                std::iter::empty(),
            )
            .expect("the optional transport search should run")
            .expect("the available source should transport");
            assert_eq!(searched.certificate().steps().len(), 2);
            assert!(refined.state.shares_state_with(&retained_refined.state));
        }

        let before = fact_node_allocations();
        let transported = refined
            .driver()
            .apply_ordinary_transport_steps(&source, vec![ProofStep::Known])
            .expect("the exact ambient fact should verify");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 16 * logarithmic_height + 64;
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state transport allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            transported.certificate().steps(),
            &[
                known_have_step(extracted.clone()),
                ProofStep::Have {
                    proposition: source.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
                },
            ]
        );
        assert_eq!(
            transported.added_facts(),
            std::slice::from_ref(&kernel_source)
        );
        assert_eq!(root.certificate().steps(), &[]);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s in the parallel gate"]
fn pure_signed_order_solve_builds_its_certificate_with_logarithmic_local_updates() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard order theorems should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let point = crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new());
    let terms = [
        OldMachineTerm::Variable(Variable(8_150_000)),
        OldMachineTerm::Variable(Variable(8_150_001)),
        OldMachineTerm::Variable(Variable(8_150_002)),
        OldMachineTerm::Variable(Variable(8_150_003)),
    ];
    let named = terms.clone();
    let named_values = named_int32_values(&named);
    let expression = |term: &OldMachineTerm| named_int32(&named, term);
    let comparison = |left: usize, operator, right: usize| SyntaxProposition::Comparison {
        left: expression(&terms[left]),
        operator,
        right: expression(&terms[right]),
    };
    let surfaces = vec![
        comparison(0, ComparisonOperator::LessEqual, 1),
        comparison(1, ComparisonOperator::LessThan, 2),
        comparison(2, ComparisonOperator::LessEqual, 3),
    ];
    let surface_goal = comparison(0, ComparisonOperator::LessThan, 3);
    let lower = |surface: &SyntaxProposition| {
        lower_pure_theorem_proposition(
            "persistent signed-order solve",
            surface,
            ContractEnvironment::new(&named_values, &BTreeMap::new()),
            &point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed signed comparison should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = lower(&surface_goal);
    let mut surface_requirements = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_requirements
            .record_lowering(surface, kernel)
            .expect("the exact requirement form should be indexed");
    }

    let mut baseline = None;
    let mut have_baseline = None;
    for size in LOCAL_PROOF_FACT_SIZES {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.extend(premises.iter().cloned());
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: point.clone(),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: surface_requirements.clone(),
        };
        let root = Proof::for_pure_goal(
            "persistent signed-order solve",
            &requires,
            goal.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the typed path should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let (base_height, base_allocations) =
            *baseline.get_or_insert((logarithmic_height, allocations));
        let allocation_bound = base_allocations * logarithmic_height / base_height;
        assert!(
            allocations <= allocation_bound,
            "size {size} signed-order solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(ordinary_arithmetic_work_size(closed.certificate().steps()).is_some());
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        // A nested smart `have` must not serialize the goal's ambient
        // copy as `close()`: the surface proposition may lower in a
        // different state when expansion is verified from source.
        // Search through a context weakened by only that exact fact and
        // retain the same checked signed-order theorem path on Proof.
        let mut exact_requires = requires.clone();
        exact_requires.push(goal.clone());
        let exact_theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: point.clone(),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: exact_requires.clone(),
            surface_requirements: surface_requirements.clone(),
        };
        let exact_root = Proof::for_pure_goal(
            "source-stable persistent signed-order have",
            &exact_requires,
            goal.clone(),
            &exact_theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let scope = exact_root
            .driver()
            .open_have(surface_goal.clone())
            .expect("the signed-order have should open a nested proof");
        let before = fact_node_allocations();
        let selected = (scope)
            .driver()
            .try_solve_closure()
            .expect("nested smart search must not exceed its deadline")
            .expect("the exact goal should close directly by `close()`");
        let allocations = fact_node_allocations() - before;
        // Retaining the exact premise must also keep persistent updates local.
        // Measure their growth against their own smallest sample.
        let (base_height, base_allocations) =
            *have_baseline.get_or_insert((logarithmic_height, allocations));
        let allocation_bound = base_allocations * logarithmic_height / base_height;
        assert!(
            allocations <= allocation_bound,
            "size {size} exact-goal have allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(selected.body().is_complete());
        assert_eq!(selected.body().certificate().steps(), &[ProofStep::Known],);
        assert!(exact_root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn pure_equality_refinement_solve_applies_one_rewrite_with_logarithmic_local_updates() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let point = crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new());
    let value = OldMachineTerm::Variable(Variable(8_174_000));
    let named = [value.clone()];
    let named_values = named_int32_values(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let equality = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(OldMachineTerm::constant(2)),
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(binary_node!(
            Int32,
            Subtract,
            Box::new(value),
            Box::new(OldMachineTerm::constant(2)),
        )),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_pure_theorem_proposition(
            "persistent equality-refinement solve",
            surface,
            ContractEnvironment::new(&named_values, &BTreeMap::new()),
            &point,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed int32 proposition should lower")
    };
    let kernel_equality = lower(&equality);
    let goal = lower(&goal_surface);
    let mut surface_requirements = SurfacePropositionMap::default();
    surface_requirements
        .record_lowering(&equality, &kernel_equality)
        .expect("the exact equality form should be indexed");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(kernel_equality.clone());
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: point.clone(),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: surface_requirements.clone(),
        };
        let root = Proof::for_pure_goal(
            "persistent equality-refinement solve",
            &requires,
            goal.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("one selected equality should refine and close the Proof");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} equality-refinement solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [ProofStep::Rewrite(_), ProofStep::Known]
        ));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn goal_term_equality_rewrite_ignores_unrelated_equality_buckets() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = SymbolicMemory::new();
    let selected_term = OldMachineTerm::Variable(Variable(8_174_050));
    let named = [selected_term.clone()];
    let named_values = named_int32_values(&named);
    let equality_fact = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(selected_term.clone()),
            right: Box::new(OldMachineTerm::constant(2)),
        },
        true,
    );
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(binary_node!(
                Int32,
                Subtract,
                Box::new(selected_term.clone()),
                Box::new(OldMachineTerm::constant(1)),
            )),
            right: Box::new(OldMachineTerm::constant(1)),
        },
        true,
    );
    let equality_surface = SyntaxProposition::Comparison {
        left: named_int32(&named, &selected_term),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(2))),
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::Subtract(
            Box::new(named_int32(&named, &selected_term)),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        ),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1))),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(OldMachineTerm::Variable(Variable(
                            9_000_000 + u64::from(index),
                        ))),
                        right: Box::new(OldMachineTerm::constant(10_000 + index)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        facts.push(equality_fact.clone());
        let mut surface_requirements = SurfacePropositionMap::default();
        surface_requirements
            .record_lowering(&equality_surface, &equality_fact)
            .expect("the selected equality form should be indexed");
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: crate::kernel::ProgramPoint::starting_at(&memory),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements,
        };
        let root = Proof::for_pure_goal_with_surface(
            "goal-term equality selection",
            &facts,
            goal.clone(),
            Some(goal_surface.clone()),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let selected = root.facts().bitvector_equalities_mentioning(&goal);
        assert_eq!(selected, vec![equality_fact.clone()]);
        let comparisons = root
            .facts()
            .equality_atom_lookup_comparisons(&selected_term);
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        assert!(
            comparisons <= 2 * logarithmic_height + 4,
            "size {size} equality lookup made {comparisons} key comparisons"
        );
        let closed = crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(root))
            .expect("the selected equality should rewrite and normalize the goal");
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [ProofStep::Rewrite(_), ProofStep::Known]
        ));
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn goal_term_equality_rewrite_chain_shrinks_independently_of_unrelated_buckets() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = SymbolicMemory::new();
    let left = OldMachineTerm::Variable(Variable(8_174_060));
    let right = OldMachineTerm::Variable(Variable(8_174_061));
    let named = [left.clone(), right.clone()];
    let named_values = named_int32_values(&named);
    let zero = OldMachineTerm::constant(0);
    let equality = |term: &OldMachineTerm| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(term.clone()),
                right: Box::new(zero.clone()),
            },
            true,
        )
    };
    let surface_equality = |term: &OldMachineTerm| SyntaxProposition::Comparison {
        left: named_int32(&named, term),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(binary_node!(
                Int32,
                Add,
                Box::new(left.clone()),
                Box::new(right.clone()),
            )),
            right: Box::new(zero.clone()),
        },
        true,
    );
    let goal_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::Add(
            Box::new(named_int32(&named, &left)),
            Box::new(named_int32(&named, &right)),
        ),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let selected = [equality(&left), equality(&right)];
    let surfaces = [surface_equality(&left), surface_equality(&right)];

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(OldMachineTerm::Variable(Variable(
                            9_100_000 + u64::from(index),
                        ))),
                        right: Box::new(OldMachineTerm::constant(20_000 + index)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        facts.extend(selected.iter().cloned());
        let mut surface_requirements = SurfacePropositionMap::default();
        for (surface, kernel) in surfaces.iter().zip(selected.iter()) {
            surface_requirements
                .record_lowering(surface, kernel)
                .expect("the selected equality form should be indexed");
        }
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: crate::kernel::ProgramPoint::starting_at(&memory),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements,
        };
        let root = Proof::for_pure_goal_with_surface(
            "shrinking goal-term equality chain",
            &facts,
            goal.clone(),
            Some(goal_surface.clone()),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        for term in [&left, &right] {
            let comparisons = root.facts().equality_atom_lookup_comparisons(term);
            assert!(
                comparisons <= 2 * logarithmic_height + 4,
                "size {size} equality lookup made {comparisons} key comparisons"
            );
        }
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(root))
            .expect("the two selected equalities should shrink and normalize the goal");
        let allocations = fact_node_allocations() - before;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} equality chain allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(
            matches!(closed.certificate().steps(), [.., ProofStep::Known]),
            "{:?}",
            closed.certificate().steps()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_predecessor_solve_builds_checked_scope_with_logarithmic_local_updates() {
    check_fixed_state_predecessor_solve(&[16, 64, 256, 1024, 4096]);
}

/// The predecessor closer once cited a bridge lemma; with `arithmetic()
/// using` in its place it needed a goal source form the fixed state lacks,
/// failed silently, and solve fell through to a costlier search. One small
/// context keeps its certificate in the gate.
#[test]
fn fixed_state_predecessor_solve_closes_with_one_arithmetic_step() {
    check_fixed_state_predecessor_solve(&[16]);
}

fn check_fixed_state_predecessor_solve(sizes: &[u32]) {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let value = OldMachineTerm::Variable(Variable(8_174_100));
    let upper = OldMachineTerm::Variable(Variable(8_174_101));
    let named = [value.clone(), upper.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let equality = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(OldMachineTerm::constant(1)),
    };
    let upper_bound = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(upper.clone()),
    };
    let nonnegative = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::constant(0),
        ))),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: expression(binary_node!(
            Int32,
            Subtract,
            Box::new(value),
            Box::new(OldMachineTerm::constant(1)),
        )),
        operator: ComparisonOperator::LessEqual,
        right: expression(upper),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed fixed-state proposition should lower")
    };
    let kernel_equality = lower(&equality);
    let kernel_upper_bound = lower(&upper_bound);
    let goal = lower(&goal_surface);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&equality, &kernel_equality)
        .expect("the exact equality form should be indexed");
    surface_propositions
        .record_lowering(&upper_bound, &kernel_upper_bound)
        .expect("the exact upper-bound form should be indexed");

    for &size in sizes {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_equality.clone());
        facts.push(kernel_upper_bound.clone());
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state predecessor solve",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the predecessor search should retain one structured descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = (128 * logarithmic_height + 512)
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state predecessor solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        // `have 0 <= x` by rewriting with `x == 1`, then one arithmetic
        // certificate over exactly that fact and the upper bound.
        assert!(
            matches!(
                closed.certificate().steps(),
                [ProofStep::Have { proposition, .. }, rest @ ..]
                    if *proposition == nonnegative
                        && ordinary_arithmetic_work_size(rest).is_some()
            ),
            "{:?}",
            closed.certificate().steps()
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_equality_solve_builds_its_recorded_path_with_logarithmic_local_updates() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = ExecutionState::new();
    let arguments = Vec::new();
    let recorded_states = RecordedStates::new();
    let terms = [
        OldMachineTerm::Variable(Variable(8_175_000)),
        OldMachineTerm::Variable(Variable(8_175_001)),
        OldMachineTerm::Variable(Variable(8_175_002)),
        OldMachineTerm::Variable(Variable(8_175_003)),
    ];
    let expression = |term: &OldMachineTerm| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(term.clone())))
    };
    let equal = |left: usize, right: usize| SyntaxProposition::Comparison {
        left: expression(&terms[left]),
        operator: ComparisonOperator::Equal,
        right: expression(&terms[right]),
    };
    let surfaces = vec![equal(1, 0), equal(1, 2), equal(2, 3)];
    let surface_goal = equal(0, 3);
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed equality should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = lower(&surface_goal);
    let mut surface_propositions = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("the exact state-qualified form should be indexed");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend(premises.iter().cloned());
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state equality solve",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the typed equality path should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state equality solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(
            matches!(closed.certificate().steps(), [ProofStep::Known]),
            "{:?}",
            closed.certificate().steps()
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_arithmetic_rewrite_paths_ignore_unrelated_facts() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = ExecutionState::new();
    let arguments = Vec::new();
    let recorded_states = RecordedStates::new();
    let left = OldMachineTerm::Variable(Variable(8_176_000));
    let right = OldMachineTerm::Variable(Variable(8_176_001));
    let one = OldMachineTerm::constant(1);
    let expression = |term: &OldMachineTerm| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(term.clone())))
    };
    let equality = |left: &OldMachineTerm, right: &OldMachineTerm| SyntaxProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::Equal,
        right: expression(right),
    };
    let surfaces = vec![equality(&left, &one), equality(&one, &right)];
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed equality should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(binary_node!(Int32, Add, Box::new(left), Box::new(right))),
            right: Box::new(OldMachineTerm::constant(2)),
        },
        true,
    );
    let mut surface_propositions = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("the exact state-qualified form should be indexed");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend(premises.iter().cloned());
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state arithmetic rewrite solve",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the retained equality paths should close the arithmetic goal");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = (128 * logarithmic_height + 512)
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} arithmetic rewrite solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(
            matches!(closed.certificate().steps(), [ProofStep::Known]),
            "{:?}",
            closed.certificate().steps()
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn fixed_state_order_solve_builds_its_theorem_path_with_logarithmic_local_updates() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard order theorems should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let terms = [
        OldMachineTerm::Variable(Variable(8_176_000)),
        OldMachineTerm::Variable(Variable(8_176_001)),
        OldMachineTerm::Variable(Variable(8_176_002)),
        OldMachineTerm::Variable(Variable(8_176_003)),
    ];
    let named = terms.clone();
    let (parsed_function, arguments) = named_int32_function(&named);
    let expression = |term: &OldMachineTerm| named_int32(&named, term);
    let comparison = |left: usize, operator, right: usize| SyntaxProposition::Comparison {
        left: expression(&terms[left]),
        operator,
        right: expression(&terms[right]),
    };
    let surfaces = vec![
        comparison(0, ComparisonOperator::LessEqual, 1),
        comparison(1, ComparisonOperator::LessThan, 2),
        comparison(2, ComparisonOperator::LessEqual, 3),
    ];
    let surface_goal = comparison(0, ComparisonOperator::LessThan, 3);
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed signed comparison should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = lower(&surface_goal);
    let mut surface_propositions = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("the exact state-qualified form should be indexed");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend(premises.iter().cloned());
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state order solve",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the typed order path should build one checked fixed-state Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_per_step = 128 * logarithmic_height + 512;
        let allocation_bound = allocation_per_step
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state order solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        // The selected three-premise chain is one arithmetic step.
        assert!(
            ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
            "{:?}",
            closed.certificate().steps()
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 9s in the parallel gate"]
fn fixed_state_single_premise_arithmetic_solves_retain_indexed_theorem_steps() {
    check_fixed_state_single_premise_arithmetic_solves(&LOCAL_PROOF_FACT_SIZES, None);
}

/// The goals [`fixed_state_single_premise_arithmetic_solves_retain_indexed_theorem_steps`]
/// lost when their bridge lemmas became arithmetic steps: a
/// definedness goal is the `int32_defined` rule, and a negated premise names
/// its operands. One small context keeps them in the gate.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn fixed_state_definedness_and_negated_premise_solves_keep_ordinary_proofs() {
    check_fixed_state_single_premise_arithmetic_solves(
        &LOCAL_PROOF_FACT_SIZES[..1],
        Some(&[
            "increment definedness",
            "one-plus definedness",
            "negated strict successor bound",
        ]),
    );
}

fn check_fixed_state_single_premise_arithmetic_solves(sizes: &[u32], labels: Option<&[&str]>) {
    #[derive(Clone, Copy)]
    enum ArithmeticProofShape {
        Direct,
        IncrementDefinedness,
        ComposedNegatedSuccessor,
        ChainedIncrementUpper,
    }

    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard increment theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let value = OldMachineTerm::Variable(Variable(8_177_000));
    let upper = OldMachineTerm::Variable(Variable(8_177_001));
    let named = [value.clone(), upper.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let named_values = named_int32_values(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let premise = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(upper.clone()),
    };
    let definedness_premise = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(OldMachineTerm::constant(i32::MAX as u32)),
    };
    let positive_premise = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let successor_lower_premise = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(2)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let strong_constant_lower_premise = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(3)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let negated_successor_premise =
        SyntaxProposition::Not(Box::new(SyntaxProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(OldMachineTerm::constant(2)),
        }));
    let increment_constant_upper_premise = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(OldMachineTerm::constant(3)),
    };
    let surface_bound_goal = SyntaxProposition::Comparison {
        left: SyntaxTerm::Add(
            Box::new(expression(value.clone())),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        ),
        operator: ComparisonOperator::LessEqual,
        right: expression(upper.clone()),
    };
    let surface_strict_goal = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::Add(
            Box::new(expression(value.clone())),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        ),
    };
    let surface_defined_goal = SyntaxProposition::Defined {
        expression: SyntaxTerm::Add(
            Box::new(expression(value.clone())),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        ),
    };
    let surface_one_plus_defined_goal = SyntaxProposition::Defined {
        expression: SyntaxTerm::Add(
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
            Box::new(expression(value.clone())),
        ),
    };
    let surface_one_plus_strict_goal = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::Add(
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
            Box::new(expression(value.clone())),
        ),
    };
    let surface_nonnegative_goal = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let surface_successor_lower_goal = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(OldMachineTerm::constant(1)),
    };
    let surface_adjacent_strict_goal = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(1)),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let surface_increment_constant_upper_goal = SyntaxProposition::Comparison {
        left: SyntaxTerm::Add(
            Box::new(expression(value.clone())),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        ),
        operator: ComparisonOperator::LessEqual,
        right: expression(OldMachineTerm::constant(5)),
    };
    let lower = |surface: &SyntaxProposition| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            surface,
            &PureFactContext::new(),
            ContractEnvironment::new(&named_values, &BTreeMap::new()),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            FixedStateLoweringOptions::default(),
        )
        .expect("the fixed increment proposition should lower").0
    };
    let kernel_premise = lower(&premise);
    let kernel_definedness_premise = lower(&definedness_premise);
    let kernel_positive_premise = lower(&positive_premise);
    let kernel_successor_lower_premise = lower(&successor_lower_premise);
    let kernel_strong_constant_lower_premise = lower(&strong_constant_lower_premise);
    let kernel_negated_successor_premise = lower(&negated_successor_premise);
    let kernel_increment_constant_upper_premise = lower(&increment_constant_upper_premise);
    let goals = [
        (
            lower(&surface_bound_goal),
            "increment bound",
            &premise,
            &kernel_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_strict_goal),
            "strict increment",
            &premise,
            &kernel_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_defined_goal),
            "increment definedness",
            &definedness_premise,
            &kernel_definedness_premise,
            ArithmeticProofShape::IncrementDefinedness,
        ),
        (
            lower(&surface_one_plus_defined_goal),
            "one-plus definedness",
            &definedness_premise,
            &kernel_definedness_premise,
            ArithmeticProofShape::IncrementDefinedness,
        ),
        (
            lower(&surface_one_plus_strict_goal),
            "one-plus strict increase",
            &definedness_premise,
            &kernel_definedness_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_nonnegative_goal),
            "positive to nonnegative",
            &positive_premise,
            &kernel_positive_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_adjacent_strict_goal),
            "adjacent strict lower bound",
            &successor_lower_premise,
            &kernel_successor_lower_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_nonnegative_goal),
            "constant lower-bound weakening",
            &strong_constant_lower_premise,
            &kernel_strong_constant_lower_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_successor_lower_goal),
            "negated strict successor bound",
            &negated_successor_premise,
            &kernel_negated_successor_premise,
            ArithmeticProofShape::ComposedNegatedSuccessor,
        ),
        (
            lower(&surface_increment_constant_upper_goal),
            "increment under a larger constant",
            &increment_constant_upper_premise,
            &kernel_increment_constant_upper_premise,
            ArithmeticProofShape::ChainedIncrementUpper,
        ),
    ];
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&premise, &kernel_premise)
        .expect("the exact strict premise should be indexed");
    surface_propositions
        .record_lowering(&definedness_premise, &kernel_definedness_premise)
        .expect("the exact maximum premise should be indexed");
    surface_propositions
        .record_lowering(&positive_premise, &kernel_positive_premise)
        .expect("the exact positive premise should be indexed");
    surface_propositions
        .record_lowering(&successor_lower_premise, &kernel_successor_lower_premise)
        .expect("the exact successor lower-bound premise should be indexed");
    surface_propositions
        .record_lowering(
            &strong_constant_lower_premise,
            &kernel_strong_constant_lower_premise,
        )
        .expect("the exact stronger constant lower bound should be indexed");
    surface_propositions
        .record_lowering(
            &negated_successor_premise,
            &kernel_negated_successor_premise,
        )
        .expect("the exact negated successor premise should be indexed");
    surface_propositions
        .record_lowering(
            &increment_constant_upper_premise,
            &kernel_increment_constant_upper_premise,
        )
        .expect("the exact constant upper-bound premise should be indexed");

    for (goal, label, surface_premise, kernel_premise, shape) in goals {
        if labels.is_some_and(|labels| !labels.contains(&label)) {
            continue;
        }
        for &size in sizes {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(kernel_premise.clone());
            let root = Proof::for_fixed_state_goal(
                "persistent fixed-state increment-bound solve",
                0,
                &facts,
                goal.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &state,
                &state,
                &recorded_states,
                &surface_propositions,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
                .expect("smart search must not exceed its deadline")
                .unwrap_or_else(|| panic!("fixed-state solve should prove the {label} goal"));
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_per_step = match shape {
                ArithmeticProofShape::Direct | ArithmeticProofShape::IncrementDefinedness => {
                    64 * logarithmic_height + 256
                }
                ArithmeticProofShape::ComposedNegatedSuccessor
                | ArithmeticProofShape::ChainedIncrementUpper => 96 * logarithmic_height + 384,
            };
            let allocation_bound = allocation_per_step
                * ordinary_arithmetic_work_size(closed.certificate().steps())
                    .expect("ordinary arithmetic output")
                    .max(1);
            assert!(
                allocations <= allocation_bound,
                "size {size} fixed-state {label} solve allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(
                ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
                "{label} retained unexpected fixed-state steps: {:#?}",
                closed.certificate().steps()
            );
            assert!(root.state.shares_state_with(&retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                diagnostic_names: Default::default(),
                declaration_bindings: BTreeMap::new(),
                integer_values: PersistentBinderMap::default(),
                point: state.program_point(),
                values: named_values.clone(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted increment-bound solve",
                &facts,
                goal.clone(),
                &theorem_context,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            assert!(
                crate::kernel::search::ProofSearch::try_restricted_solve_closure(&(pure_root), &[])
                    .is_none(),
                "omitting the named premise must reject the restricted candidate"
            );
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            let before_restricted = fact_node_allocations();
            let pure_closed = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                &(pure_root),
                std::slice::from_ref(surface_premise),
            )
            .unwrap_or_else(|| {
                panic!("restricted solve should retain the checked typed {label} rule")
            });
            let restricted_allocations = fact_node_allocations() - before_restricted;
            let proof_work = ordinary_arithmetic_work_size(pure_closed.certificate().steps())
                .expect("ordinary restricted arithmetic output");
            let allocation_bound = allocation_per_step
                * match shape {
                    // The named increment theorem publishes the whole signed domain at
                    // once. Use a fixed allowance for that application and the commuted
                    // case's additional equality proof. The former composed increment
                    // proof received 81 units under the per-step allowance.
                    ArithmeticProofShape::IncrementDefinedness => 24,
                    _ => proof_work.max(1),
                };
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {label} solve allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            assert!(
                ordinary_arithmetic_work_size(pure_closed.certificate().steps()).is_some(),
                "restricted {label} retained unexpected steps: {:#?}",
                pure_closed.certificate().steps()
            );
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn branch_exported_premise_uses_one_selected_anchor_with_logarithmic_work() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard increment theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 noop(int32 x) { return x; }")
        .expect("test C function should parse");
    let value = OldMachineTerm::Variable(Variable(8_177_900));
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(value))];
    let state = ExecutionState::new();
    let point = ProgramPointRef {
        region: CodeRegionRef::Region(0),
        kind: ProgramPointKind::Entry,
    };
    let mut recorded_states = RecordedStates::new();
    recorded_states.insert(point.clone(), state.clone());
    let variable =
        || SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into()));
    let constant = |value| SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value)));
    let lower_premise = SyntaxProposition::Comparison {
        left: variable(),
        operator: ComparisonOperator::GreaterEqual,
        right: constant(0),
    };
    let upper_premise = SyntaxProposition::Comparison {
        left: variable(),
        operator: ComparisonOperator::LessThan,
        right: constant(i32::MAX as u32),
    };
    let goal_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::Add(Box::new(variable()), Box::new(constant(1))),
        operator: ComparisonOperator::GreaterThan,
        right: constant(0),
    };
    let anchored_lower = surface_at_program_point(&lower_premise, &point)
        .expect("the branch-exported lower bound should admit a state-qualified form");
    let anchored_upper = surface_at_program_point(&upper_premise, &point)
        .expect("the continuation upper bound should admit a state-qualified form");
    let lower = |surface: &SyntaxProposition| {
        lower_arithmetic_fixture_goal(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the selected fixed-state proposition should lower")
    };
    let kernel_lower = lower(&anchored_lower);
    let kernel_upper = lower(&anchored_upper);
    let goal = lower(&goal_surface);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&anchored_upper, &kernel_upper)
        .expect("only the continuation premise should carry the common state anchor");
    let expected_premises = [anchored_lower, anchored_upper];

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_lower.clone(), kernel_upper.clone()]);
        let root = Proof::for_fixed_state_goal(
            "branch-exported premise outcome solve",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the selected anchor should retain the two-premise theorem step");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_per_step = 96 * logarithmic_height + 384;
        let allocation_bound = allocation_per_step
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} anchored branch outcome solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(
            ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
            "size {size} anchored branch outcome solve retained unexpected steps: {:#?}",
            closed.certificate().steps()
        );
        for omitted in [&expected_premises[..1], &expected_premises[1..]] {
            assert!(
                crate::kernel::search::ProofSearch::try_restricted_solve_closure(&root, omitted)
                    .is_none()
            );
        }
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn increment_bound_family_retains_two_indexed_theorem_premises() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard increment theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let lower = OldMachineTerm::Variable(Variable(8_178_000));
    let value = OldMachineTerm::Variable(Variable(8_178_001));
    let upper = OldMachineTerm::Variable(Variable(8_178_002));
    let named = [lower.clone(), value.clone(), upper.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let parameter_binding = ParameterBinding::new(parsed_function.parameters(), &arguments);
    let named_values = named_int32_values(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let lower_premise = SyntaxProposition::Comparison {
        left: expression(lower.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let upper_premise = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(upper.clone()),
    };
    let increment = |term: OldMachineTerm| {
        SyntaxTerm::Add(
            Box::new(expression(term)),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        )
    };
    let surface_goals = [
        (
            SyntaxProposition::Comparison {
                left: expression(lower.clone()),
                operator: ComparisonOperator::LessEqual,
                right: increment(value.clone()),
            },
            "less-equal lower bound",
        ),
        (
            SyntaxProposition::Comparison {
                left: increment(value.clone()),
                operator: ComparisonOperator::GreaterEqual,
                right: expression(lower.clone()),
            },
            "greater-equal lower bound",
        ),
        (
            SyntaxProposition::Comparison {
                left: increment(value.clone()),
                operator: ComparisonOperator::GreaterThan,
                right: expression(lower.clone()),
            },
            "strict-greater lower bound",
        ),
        (
            SyntaxProposition::Comparison {
                left: increment(lower.clone()),
                operator: ComparisonOperator::LessEqual,
                right: increment(value.clone()),
            },
            "incremented order",
        ),
    ];
    let lower_surface = |surface: &SyntaxProposition| {
        lower_arithmetic_fixture_goal(
            surface,
            &PureFactContext::new(),
            parameter_binding,
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed increment-lower-bound proposition should lower")
    };
    let kernel_lower = lower_surface(&lower_premise);
    let kernel_upper = lower_surface(&upper_premise);
    let goals = surface_goals
        .iter()
        .map(|(surface, label)| (lower_surface(surface), *label))
        .collect::<Vec<_>>();
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&lower_premise, &kernel_lower)
        .expect("the exact lower premise should be indexed");
    surface_propositions
        .record_lowering(&upper_premise, &kernel_upper)
        .expect("the exact upper premise should be indexed");
    let selected_premises = [lower_premise.clone(), upper_premise.clone()];

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_lower.clone(), kernel_upper.clone()]);
        for (goal, label) in &goals {
            let root = Proof::for_fixed_state_goal(
                "persistent fixed-state increment-bound-family solve",
                0,
                &facts,
                goal.clone(),
                parameter_binding,
                &state,
                &state,
                &recorded_states,
                &surface_propositions,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
                .expect("smart search must not exceed its deadline")
                .expect("the typed two-premise rule should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            // The incremented order compares two sums, so its certificate
            // carries both increments: about 220 nodes per index level against
            // under 100 for the one-sided bounds. Both slopes stay logarithmic
            // and a linear copy of the 1024 facts still exceeds the ceiling.
            let allocation_per_step = if *label == "incremented order" {
                224 * logarithmic_height + 1536
            } else {
                96 * logarithmic_height + 2048
            };
            let allocation_bound = allocation_per_step
                * ordinary_arithmetic_work_size(closed.certificate().steps())
                    .expect("ordinary arithmetic output")
                    .max(1);
            assert!(
                allocations <= allocation_bound,
                "size {size} fixed-state {label} solve allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(
                ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
                "size {size} fixed-state {label} solve retained unexpected steps: {:#?}",
                closed.certificate().steps()
            );
            assert!(root.state.shares_state_with(&retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                diagnostic_names: Default::default(),
                declaration_bindings: BTreeMap::new(),
                integer_values: PersistentBinderMap::default(),
                point: state.program_point(),
                values: named_values.clone(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted increment-bound-family solve",
                &facts,
                goal.clone(),
                &theorem_context,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted in [
                std::slice::from_ref(&lower_premise),
                std::slice::from_ref(&upper_premise),
            ] {
                assert!(
                    crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                        &(pure_root),
                        omitted
                    )
                    .is_none(),
                    "omitting either theorem premise must reject the restricted candidate"
                );
                assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                &(pure_root),
                &selected_premises,
            )
            .expect("restricted solve should retain the checked two-premise rule");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            let allocation_bound = allocation_per_step
                * ordinary_arithmetic_work_size(pure_closed.certificate().steps())
                    .expect("ordinary restricted arithmetic output")
                    .max(1);
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {label} solve allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            assert!(
                ordinary_arithmetic_work_size(pure_closed.certificate().steps()).is_some(),
                "size {size} restricted {label} solve retained unexpected steps: {:#?}",
                pure_closed.certificate().steps()
            );
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }

    let strict_lower_premise = SyntaxProposition::Comparison {
        left: expression(lower.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let strict_goal_surface = SyntaxProposition::Comparison {
        left: increment(value.clone()),
        operator: ComparisonOperator::GreaterThan,
        right: expression(lower.clone()),
    };
    let kernel_strict_lower = lower_surface(&strict_lower_premise);
    let strict_goal = lower_surface(&strict_goal_surface);
    let mut strict_surface_propositions = SurfacePropositionMap::default();
    strict_surface_propositions
        .record_lowering(&strict_lower_premise, &kernel_strict_lower)
        .expect("the exact strict lower premise should be indexed");
    strict_surface_propositions
        .record_lowering(&upper_premise, &kernel_upper)
        .expect("the exact upper premise should be indexed");
    let strict_selected_premises = [strict_lower_premise.clone(), upper_premise.clone()];

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_strict_lower.clone(), kernel_upper.clone()]);
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state strict increment-bound solve",
            0,
            &facts,
            strict_goal.clone(),
            parameter_binding,
            &state,
            &state,
            &recorded_states,
            &strict_surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the strict-lower increment path should advance one Proof");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_per_step = 96 * logarithmic_height + 2048;
        let allocation_bound = allocation_per_step
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state strict-lower solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(
            ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
            "size {size} fixed-state strict-lower solve retained unexpected steps: {:#?}",
            closed.certificate().steps()
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: state.program_point(),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: strict_surface_propositions.clone(),
        };
        let pure_root = Proof::for_pure_goal(
            "persistent restricted strict increment-bound solve",
            &facts,
            strict_goal.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_pure_root = pure_root.clone();
        for omitted in [
            std::slice::from_ref(&strict_lower_premise),
            std::slice::from_ref(&upper_premise),
        ] {
            assert!(
                crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(pure_root),
                    omitted
                )
                .is_none()
            );
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
        }
        let before_restricted = fact_node_allocations();
        let pure_closed = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
            &(pure_root),
            &strict_selected_premises,
        )
        .expect("restricted strict-lower solve should advance one Proof");
        let restricted_allocations = fact_node_allocations() - before_restricted;
        let allocation_bound = allocation_per_step
            * ordinary_arithmetic_work_size(pure_closed.certificate().steps())
                .expect("ordinary restricted arithmetic output")
                .max(1);
        assert!(
            restricted_allocations <= allocation_bound,
            "size {size} restricted strict-lower solve allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(pure_closed.is_complete());
        assert!(
            ordinary_arithmetic_work_size(pure_closed.certificate().steps()).is_some(),
            "size {size} restricted strict-lower solve retained unexpected steps: {:#?}",
            pure_closed.certificate().steps()
        );
        assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
        assert!(pure_root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s in the parallel gate"]
fn le_and_not_lt_equality_solve_retains_one_indexed_arithmetic_step() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard equality theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let left = OldMachineTerm::Variable(Variable(8_178_100));
    let right = OldMachineTerm::Variable(Variable(8_178_101));
    let named = [left.clone(), right.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let named_values = named_int32_values(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let less_equal = SyntaxProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(right.clone()),
    };
    let not_less_than = SyntaxProposition::Not(Box::new(SyntaxProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(right.clone()),
    }));
    let equality = SyntaxProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::Equal,
        right: expression(right),
    };
    let lower_surface = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed equality proposition should lower")
    };
    let kernel_less_equal = lower_surface(&less_equal);
    let kernel_not_less_than = lower_surface(&not_less_than);
    let kernel_equality = lower_surface(&equality);
    let selected = [less_equal.clone(), not_less_than.clone()];
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&less_equal, &kernel_less_equal)
        .expect("the <= premise should be indexed");
    surface_propositions
        .record_lowering(&not_less_than, &kernel_not_less_than)
        .expect("the not-< premise should be indexed");

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_less_equal.clone(), kernel_not_less_than.clone()]);
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state <=/not-< equality solve",
            0,
            &facts,
            kernel_equality.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the typed equality rule should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = (96 * logarithmic_height + 384)
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state equality solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(ordinary_arithmetic_work_size(closed.certificate().steps()).is_some());
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let restricted_kernels = selected
            .iter()
            .map(|surface| {
                lower_pure_theorem_proposition(
                    "persistent restricted <=/not-< equality solve",
                    surface,
                    ContractEnvironment::new(&named_values, &BTreeMap::new()),
                    &state.program_point(),
                    SpecDefinitions::new(&predicate_environment, &click_function_environment),
                )
                .expect("each restricted equality premise should lower")
            })
            .collect::<Vec<_>>();
        assert_eq!(restricted_kernels[0], kernel_less_equal);
        assert!(condition_polarity_equivalent(
            &restricted_kernels[1],
            &kernel_not_less_than
        ));
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.extend(restricted_kernels.iter().cloned());
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: state.program_point(),
            values: named_values.clone(),
            array_refs: BTreeMap::new(),
            requires: pure_facts.clone(),
            surface_requirements: surface_propositions.clone(),
        };
        let pure_root = Proof::for_pure_goal(
            "persistent restricted <=/not-< equality solve",
            &pure_facts,
            kernel_equality.clone(),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_pure_root = pure_root.clone();
        for omitted in [
            std::slice::from_ref(&less_equal),
            std::slice::from_ref(&not_less_than),
        ] {
            assert!(
                crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(pure_root),
                    omitted
                )
                .is_none()
            );
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
        }
        let restricted_derivation = plan_solve_certificate(
            &kernel_equality,
            &assumptions_from_propositions(&restricted_kernels),
        )
        .expect("the restricted equality facts should produce a derivation");
        let SolveEvidence::Derivation(restricted_derivation) = restricted_derivation else {
            panic!("the equality rule should be contextual")
        };
        assert!(
            restricted_derivation
                .int32_le_and_not_lt_implies_equality_premises()
                .is_some(),
            "the restricted derivation should retain the named equality rule"
        );
        let restricted_pairs = restricted_kernels
            .iter()
            .cloned()
            .zip(selected.iter().cloned())
            .collect::<Vec<_>>();
        let (less_equal, not_less_than) = restricted_derivation
            .int32_le_and_not_lt_implies_equality_premises()
            .expect("the typed equality evidence should name both premises");
        let recorded = recorded_premise_pairs([less_equal, not_less_than], &restricted_pairs, true)
            .expect("the typed equality evidence should recover both Surface premises");
        let planned = plan_explicit_le_and_not_lt_implies_eq(&kernel_equality, &recorded)
            .expect("the typed equality evidence should select the named theorem");
        let planned_certificate = ProofCertificate::from_proof_tactics(&planned)
            .expect("the named equality theorem should form a simple certificate");
        let planned_closed = pure_root
            .driver()
            .try_authoritative_linear_script(&planned_certificate.to_proof_tactics())
            .unwrap_or_else(|error| panic!("the named equality plan failed: {error:?}"))
            .expect("the named equality plan should close through checked Proof operations");
        assert!(planned_closed.is_complete());
        let pure_closed = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
            &(pure_root),
            &selected,
        )
        .expect("restricted solve should retain the checked equality theorem");
        assert!(ordinary_arithmetic_work_size(pure_closed.certificate().steps()).is_some());
        assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn ge_and_not_gt_equality_solve_retains_one_indexed_theorem_application() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard equality theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let left = OldMachineTerm::Variable(Variable(8_178_102));
    let right = OldMachineTerm::Variable(Variable(8_178_103));
    let named = [left.clone(), right.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let greater_equal = SyntaxProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(right.clone()),
    };
    let not_greater_than = SyntaxProposition::Not(Box::new(SyntaxProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::GreaterThan,
        right: expression(right.clone()),
    }));
    let equality = SyntaxProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::Equal,
        right: expression(right),
    };
    let lower_surface = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed equality proposition should lower")
    };
    let kernel_greater_equal = lower_surface(&greater_equal);
    let kernel_not_greater_than = lower_surface(&not_greater_than);
    let kernel_equality = lower_surface(&equality);
    let selected = [greater_equal.clone(), not_greater_than.clone()];
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&greater_equal, &kernel_greater_equal)
        .expect("the >= premise should be indexed");
    surface_propositions
        .record_lowering(&not_greater_than, &kernel_not_greater_than)
        .expect("the not-> premise should be indexed");

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([
            kernel_greater_equal.clone(),
            kernel_not_greater_than.clone(),
        ]);
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state >=/not-> equality solve",
            0,
            &facts,
            kernel_equality.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the typed >=/not-> rule should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = (96 * logarithmic_height + 384)
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state >=/not-> equality solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(
            ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
            "size {size} fixed-state >=/not-> equality solve retained unexpected steps: {:#?}",
            closed.certificate().steps()
        );
        assert!(
            crate::kernel::search::ProofSearch::try_restricted_solve_closure(&root, &selected)
                .is_some()
        );
        for omitted in [&selected[..1], &selected[1..], &[]] {
            assert!(
                crate::kernel::search::ProofSearch::try_restricted_solve_closure(&root, omitted)
                    .is_none()
            );
        }
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn le_and_neq_strict_solve_retains_one_indexed_arithmetic_step() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = proof_theorem_definitions(&click_file)
        .expect("the standard strict-order theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let left = OldMachineTerm::Variable(Variable(8_178_104));
    let right = OldMachineTerm::Variable(Variable(8_178_105));
    let named = [left.clone(), right.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let less_equal = SyntaxProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(right.clone()),
    };
    // Match the direct inequality spelling retained by signed certificates.
    let not_equal = SyntaxProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::NotEqual,
        right: expression(right.clone()),
    };
    let strict = SyntaxProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::LessThan,
        right: expression(right),
    };
    let lower_surface = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed strict-order proposition should lower")
    };
    let kernel_less_equal = lower_surface(&less_equal);
    let kernel_not_equal = lower_surface(&not_equal);
    let kernel_strict = lower_surface(&strict);
    let selected = [less_equal.clone(), not_equal.clone()];
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&less_equal, &kernel_less_equal)
        .expect("the <= premise should be indexed");
    surface_propositions
        .record_lowering(&not_equal, &kernel_not_equal)
        .expect("the != premise should be indexed");

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_less_equal.clone(), kernel_not_equal.clone()]);
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state <=/!= strict-order solve",
            0,
            &facts,
            kernel_strict.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the typed <=/!= rule should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = (96 * logarithmic_height + 384)
            * ordinary_arithmetic_work_size(closed.certificate().steps())
                .expect("ordinary arithmetic output")
                .max(1);
        assert!(
            allocations <= allocation_bound,
            "size {size} fixed-state <=/!= strict-order solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(ordinary_arithmetic_work_size(closed.certificate().steps()).is_some());
        assert!(
            crate::kernel::search::ProofSearch::try_restricted_solve_closure(&root, &selected)
                .is_some()
        );
        for omitted in [&selected[..1], &selected[1..], &[]] {
            assert!(
                crate::kernel::search::ProofSearch::try_restricted_solve_closure(&root, omitted)
                    .is_none()
            );
        }
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6.2s in the parallel gate"]
fn symbolic_arithmetic_definedness_retains_two_indexed_theorem_premises() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = proof_theorem_definitions(&click_file)
        .expect("the standard symbolic-add theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let value = OldMachineTerm::Variable(Variable(8_178_100));
    let amount = OldMachineTerm::Variable(Variable(8_178_101));
    let named = [value.clone(), amount.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let named_values = named_int32_values(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let amount_nonnegative = SyntaxProposition::Comparison {
        left: expression(amount.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(OldMachineTerm::constant(0)),
    };
    let headroom = SyntaxTerm::Subtract(
        Box::new(expression(OldMachineTerm::constant(i32::MAX as u32))),
        Box::new(expression(amount.clone())),
    );
    let within_headroom = SyntaxProposition::Comparison {
        left: headroom,
        operator: ComparisonOperator::GreaterEqual,
        right: expression(value.clone()),
    };
    let within_value = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(amount.clone()),
    };
    let surface_add_goal = SyntaxProposition::Defined {
        expression: SyntaxTerm::Add(
            Box::new(expression(value.clone())),
            Box::new(expression(amount.clone())),
        ),
    };
    let surface_subtract_goal = SyntaxProposition::Defined {
        expression: SyntaxTerm::Subtract(
            Box::new(expression(value.clone())),
            Box::new(expression(amount.clone())),
        ),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the symbolic arithmetic proposition should lower")
    };
    let kernel_nonnegative = lower(&amount_nonnegative);
    let kernel_headroom = lower(&within_headroom);
    let kernel_within_value = lower(&within_value);
    let cases = [
        (
            lower(&surface_add_goal),
            "click::integer::int32_nonnegative_add_within_max_is_defined",
            [amount_nonnegative.clone(), within_headroom.clone()],
            [kernel_nonnegative.clone(), kernel_headroom.clone()],
            "symbolic-add",
        ),
        (
            lower(&surface_subtract_goal),
            "click::integer::int32_nonnegative_subtract_within_value_is_defined",
            [amount_nonnegative.clone(), within_value.clone()],
            [kernel_nonnegative.clone(), kernel_within_value.clone()],
            "symbolic-subtract",
        ),
    ];
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&amount_nonnegative, &kernel_nonnegative)
        .expect("the exact nonnegative premise should be indexed");
    surface_propositions
        .record_lowering(&within_headroom, &kernel_headroom)
        .expect("the exact headroom premise should be indexed");
    surface_propositions
        .record_lowering(&within_value, &kernel_within_value)
        .expect("the exact within-value premise should be indexed");

    for size in [16_u32, 64, 256, 1024, 4096] {
        for (kernel_goal, theorem_name, selected, kernel_premises, label) in &cases {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend(kernel_premises.iter().cloned());
            let root = Proof::for_fixed_state_goal(
                "persistent fixed-state symbolic arithmetic solve",
                0,
                &facts,
                kernel_goal.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &state,
                &state,
                &recorded_states,
                &surface_propositions,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
                .expect("smart search must not exceed its deadline")
                .expect(
                    "the typed symbolic arithmetic rule should build one checked Proof descendant",
                );
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} fixed-state {label} solve allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [ProofStep::ApplyTheoremUsing { application, premises }, ProofStep::Known]
                        if application.name == *theorem_name
                            && premises.as_slice() == selected
            ));
            assert!(root.state.shares_state_with(&retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                diagnostic_names: Default::default(),
                declaration_bindings: BTreeMap::new(),
                integer_values: PersistentBinderMap::default(),
                point: state.program_point(),
                values: named_values.clone(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted symbolic arithmetic solve",
                &facts,
                kernel_goal.clone(),
                &theorem_context,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted in [
                std::slice::from_ref(&selected[0]),
                std::slice::from_ref(&selected[1]),
            ] {
                assert!(
                    crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                        &(pure_root),
                        omitted
                    )
                    .is_none()
                );
                assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                &(pure_root),
                selected,
            )
            .expect("restricted solve should retain the symbolic arithmetic theorem");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {label} solve allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(matches!(
                pure_closed.certificate().steps(),
                [ProofStep::ApplyTheoremUsing { application, premises }, ProofStep::Known]
                    if application.name == *theorem_name
                        && premises.as_slice() == selected
            ));
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn selected_disjunction_solve_retains_checked_cases_and_scales() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let value = OldMachineTerm::Variable(Variable(8_178_900));
    let named = [value.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let equal_zero = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(OldMachineTerm::constant(0)),
    };
    let equal_one = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(OldMachineTerm::constant(1)),
    };
    let disjunction =
        SyntaxProposition::Or(Box::new(equal_zero.clone()), Box::new(equal_one.clone()));
    let surface_goal = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value),
    };
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed proposition should lower")
    };
    let kernel_disjunction = lower(&disjunction);
    let kernel_goal = lower(&surface_goal);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&disjunction, &kernel_disjunction)
        .expect("the selected disjunction should be indexed");

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_disjunction.clone());
        let root = Proof::for_fixed_state_goal(
            "persistent fixed-state disjunction solve",
            0,
            &facts,
            kernel_goal.clone(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &state,
            &recorded_states,
            &surface_propositions,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
            &[],
        );
        assert_eq!(
            root.facts().assumptions().disjunction_fact_count(),
            1,
            "unrelated facts must not enter the disjunction candidate index"
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
            .expect("smart search must not exceed its deadline")
            .expect("the selected disjunction should close both checked Proof arms");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 160 * logarithmic_height + 640;
        assert!(
            allocations <= allocation_bound,
            "size {size} disjunction solve allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [ProofStep::Cases {
                disjunction: retained,
                left_proof,
                right_proof,
            }] if retained == &disjunction
                && matches!(
                    left_proof.steps(),
                    [ProofStep::Rewrite(equality), ProofStep::Known]
                        if equality == &equal_zero
                )
                && matches!(
                    right_proof.steps(),
                    [ProofStep::Rewrite(equality), ProofStep::Known]
                        if equality == &equal_one
                )
        ));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4.3s in the parallel gate"]
fn surface_structural_solve_retains_recursive_child_proofs_and_scales() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("the standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let left_value = OldMachineTerm::Variable(Variable(8_178_910));
    let right_value = OldMachineTerm::Variable(Variable(8_178_911));
    let named = [left_value.clone(), right_value.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let left_positive = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(left_value.clone()),
    };
    let right_positive = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(right_value.clone()),
    };
    let left_nonnegative = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(left_value.clone()),
    };
    let right_nonnegative = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(right_value.clone()),
    };
    let branch_condition = SyntaxProposition::Comparison {
        left: expression(left_value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(right_value),
    };
    let negative = SyntaxProposition::Comparison {
        left: expression(left_value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(OldMachineTerm::constant(0)),
    };
    let reflexive = SyntaxProposition::Comparison {
        left: expression(left_value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(left_value),
    };
    let conjunction = SyntaxProposition::And(
        Box::new(left_nonnegative.clone()),
        Box::new(right_nonnegative),
    );
    let disjunction = SyntaxProposition::Or(Box::new(left_nonnegative.clone()), Box::new(negative));
    let implication =
        SyntaxProposition::Implies(Box::new(reflexive), Box::new(left_positive.clone()));
    let lower = |surface: &SyntaxProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed structural proposition should lower")
    };
    let kernel_left_positive = lower(&left_positive);
    let kernel_right_positive = lower(&right_positive);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&left_positive, &kernel_left_positive)
        .expect("the recursive left premise should be indexed");
    surface_propositions
        .record_lowering(&right_positive, &kernel_right_positive)
        .expect("the recursive right premise should be indexed");

    for size in STRUCTURAL_PROOF_FACT_SIZES {
        let unrelated = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_per_step = 256 * logarithmic_height + 1024;
        for (label, surface_goal, selected_facts) in [
            (
                "conjunction",
                &conjunction,
                &[kernel_left_positive.clone(), kernel_right_positive.clone()][..],
            ),
            (
                "disjunction",
                &disjunction,
                std::slice::from_ref(&kernel_left_positive),
            ),
            (
                "implication",
                &implication,
                std::slice::from_ref(&kernel_left_positive),
            ),
        ] {
            let mut facts = unrelated.clone();
            facts.extend_from_slice(selected_facts);
            let root = Proof::for_fixed_state_surface_goal(
                "persistent surface structural solve",
                0,
                &facts,
                lower(surface_goal),
                surface_goal.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &state,
                &state,
                &recorded_states,
                &surface_propositions,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
                &[],
            );
            let retained_root = root.clone();
            let Some(Obligation::Proposition(root_goal)) = root.focused_obligation() else {
                unreachable!("the structural regression owns a proposition goal")
            };
            let root_surface = root_goal
                .surface
                .as_ref()
                .expect("the root should own its exact Surface goal");
            let (split_proof, _, ids) = root
                .split_focused_if(branch_condition.clone())
                .expect("an unrelated condition should fork the structural goal");
            for id in ids {
                let arm = split_proof
                    .focus_branch(id)
                    .expect("both siblings are open");
                let Some(Obligation::Proposition(arm_goal)) = arm.focused_obligation() else {
                    unreachable!("a pure proof branch retains its proposition goal")
                };
                assert!(Arc::ptr_eq(
                    root_surface,
                    arm_goal
                        .surface
                        .as_ref()
                        .expect("the branch should share the root Surface goal")
                ));
            }
            let before = fact_node_allocations();
            let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
                .expect("smart search must not exceed its deadline")
                .unwrap_or_else(|| panic!("the {label} should retain its recursive proof"));
            let allocations = fact_node_allocations() - before;
            let allocation_bound = allocation_per_step
                * ordinary_arithmetic_work_size(closed.certificate().steps())
                    .expect("ordinary arithmetic output")
                    .max(1);
            assert!(
                allocations <= allocation_bound,
                "size {size} {label} solve allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            let retained_steps = closed.certificate();
            match label {
                "conjunction" => assert!(
                    matches!(
                        retained_steps.steps(),
                        [ProofStep::Both {
                            left_proof: left,
                            right_proof: right,
                            ..
                        }] if ordinary_arithmetic_work_size(left.steps()).is_some()
                            && ordinary_arithmetic_work_size(right.steps()).is_some()
                    ),
                    "{retained_steps:#?}"
                ),
                "disjunction" => assert!(
                    matches!(
                        retained_steps.steps(),
                        [
                            ProofStep::Have { proof, .. },
                            ProofStep::Known,
                        ] if ordinary_arithmetic_work_size(proof.steps()).is_some()
                    ),
                    "{retained_steps:#?}"
                ),
                "implication" => assert!(
                    matches!(
                        retained_steps.steps(),
                        [ProofStep::IntroBlock { binder: None, body }]
                            if body.steps() == [ProofStep::Known]
                    ),
                    "{retained_steps:#?}"
                ),
                _ => unreachable!(),
            }
            assert!(root.state.shares_state_with(&retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn predecessor_solves_retain_indexed_named_rule_premises() {
    let click_file = crate::surface::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = proof_theorem_definitions(&click_file)
        .expect("the standard predecessor theorems should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let state = ExecutionState::new();
    let recorded_states = RecordedStates::new();
    let value = OldMachineTerm::Variable(Variable(8_179_000));
    let bound = OldMachineTerm::Variable(Variable(8_179_001));
    let named = [value.clone(), bound.clone()];
    let (parsed_function, arguments) = named_int32_function(&named);
    let named_values = named_int32_values(&named);
    let expression = |term: OldMachineTerm| named_int32(&named, &term);
    let predecessor = || {
        SyntaxTerm::Subtract(
            Box::new(expression(value.clone())),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(1),
            ))),
        )
    };
    let positive = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let nonnegative = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let bounded = SyntaxProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(bound.clone()),
    };
    let one_le = SyntaxProposition::Comparison {
        left: expression(OldMachineTerm::constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let surface_goals = [
        (
            SyntaxProposition::Comparison {
                left: expression(OldMachineTerm::constant(0)),
                operator: ComparisonOperator::LessEqual,
                right: predecessor(),
            },
            "positive predecessor is nonnegative",
            vec![positive.clone()],
            false,
        ),
        (
            SyntaxProposition::Comparison {
                left: predecessor(),
                operator: ComparisonOperator::LessThan,
                right: expression(value.clone()),
            },
            "positive predecessor strictly decreases",
            vec![positive.clone()],
            false,
        ),
        (
            SyntaxProposition::Comparison {
                left: predecessor(),
                operator: ComparisonOperator::LessEqual,
                right: expression(bound),
            },
            "nonnegative predecessor upper bound",
            vec![nonnegative.clone(), bounded.clone()],
            false,
        ),
        (
            SyntaxProposition::Comparison {
                left: expression(OldMachineTerm::constant(0)),
                operator: ComparisonOperator::LessEqual,
                right: predecessor(),
            },
            "positive predecessor is nonnegative",
            vec![one_le.clone()],
            true,
        ),
        (
            SyntaxProposition::Comparison {
                left: predecessor(),
                operator: ComparisonOperator::LessThan,
                right: expression(value.clone()),
            },
            "positive predecessor strictly decreases",
            vec![one_le.clone()],
            true,
        ),
    ];
    let lower_surface = |surface: &SyntaxProposition| {
        lower_arithmetic_fixture_goal(
            surface,
            &PureFactContext::new(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, None, &recorded_states),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )
        .expect("the fixed predecessor proposition should lower")
    };
    let kernel_positive = lower_surface(&positive);
    let kernel_nonnegative = lower_surface(&nonnegative);
    let kernel_bounded = lower_surface(&bounded);
    let kernel_one_le = lower_surface(&one_le);
    let goals = surface_goals
        .iter()
        .map(|(surface, rule, selected, nested)| {
            (lower_surface(surface), *rule, selected.clone(), *nested)
        })
        .collect::<Vec<_>>();
    let mut surface_propositions = SurfacePropositionMap::default();
    for (surface, kernel) in [
        (&positive, &kernel_positive),
        (&nonnegative, &kernel_nonnegative),
        (&bounded, &kernel_bounded),
        (&one_le, &kernel_one_le),
    ] {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("each exact predecessor premise should be indexed");
    }

    for size in LOCAL_PROOF_FACT_SIZES {
        let unrelated_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        for (goal, rule, selected, nested) in &goals {
            let mut facts = unrelated_facts.clone();
            facts.extend(selected.iter().map(&lower_surface));
            let root = Proof::for_fixed_state_goal(
                "persistent fixed-state predecessor solve",
                0,
                &facts,
                goal.clone(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &state,
                &state,
                &recorded_states,
                &surface_propositions,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = crate::kernel::search::ProofSearch::try_solve_closure(&(root))
                .expect("smart search must not exceed its deadline")
                .unwrap_or_else(|| {
                    panic!(
                        "the typed predecessor rule {rule} (nested={nested}) should build a checked Proof descendant"
                    )
                });
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_per_step = 96 * logarithmic_height + 384;
            let allocation_bound = allocation_per_step
                * ordinary_arithmetic_work_size(closed.certificate().steps())
                    .expect("ordinary arithmetic output")
                    .max(1);
            assert!(
                allocations <= allocation_bound,
                "size {size} fixed-state {rule} allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(
                ordinary_arithmetic_work_size(closed.certificate().steps()).is_some(),
                "size {size} closed {rule} (nested={nested}) retained unexpected steps: {:#?}",
                closed.certificate().steps()
            );
            assert!(root.state.shares_state_with(&retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                diagnostic_names: Default::default(),
                declaration_bindings: BTreeMap::new(),
                integer_values: PersistentBinderMap::default(),
                point: state.program_point(),
                values: named_values.clone(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted predecessor solve",
                &facts,
                goal.clone(),
                &theorem_context,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted_index in 0..selected.len() {
                let omitted = selected
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != omitted_index)
                    .map(|(_, premise)| premise.clone())
                    .collect::<Vec<_>>();
                assert!(
                    crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                        &(pure_root),
                        &omitted
                    )
                    .is_none(),
                    "omitting a theorem premise must reject the restricted candidate"
                );
                assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                &(pure_root),
                selected,
            )
            .expect("restricted solve should retain the checked predecessor rule");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            let allocation_bound = allocation_per_step
                * ordinary_arithmetic_work_size(pure_closed.certificate().steps())
                    .expect("ordinary restricted arithmetic output")
                    .max(1);
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {rule} allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            assert!(
                ordinary_arithmetic_work_size(pure_closed.certificate().steps()).is_some(),
                "size {size} pure_closed {rule} (nested={nested}) retained unexpected steps: {:#?}",
                pure_closed.certificate().steps()
            );
            assert!(pure_root.state.shares_state_with(&retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn pure_apply_search_instantiates_requirements_and_retains_its_successor() {
    let click_file = crate::surface::parse(LESS_THAN_IMPLIES_LESS_EQUAL)
        .expect("the fixture theorem should parse beside the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let point = crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new());
    let left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_200_000)));
    let right = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_200_001)));
    let premise = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let conclusion = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let kernel_premise = lower_pure_theorem_proposition(
        "persistent pure theorem search",
        &premise,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact pure premise should lower");
    let kernel_conclusion = lower_pure_theorem_proposition(
        "persistent pure theorem search",
        &conclusion,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the pure theorem conclusion should lower");
    let application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(left)),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(kernel_premise.clone());
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: PersistentBinderMap::default(),
            point: point.clone(),
            values: ProgramValueBindings::new(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let goal = Proposition::And(
            Box::new(kernel_conclusion.clone()),
            Box::new(kernel_premise.clone()),
        );
        let root = Proof::for_pure_goal(
            "persistent pure theorem search",
            &requires,
            goal,
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let missing = root
            .driver()
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: missing_application.clone(),
                premises: vec![premise.clone()],
            })
            .err()
            .expect("an unavailable instantiated requirement must reject the application");
        assert!(
            missing.message().contains("required exact fact"),
            "{missing:?}"
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let before_script = fact_node_allocations();
        let complete = root
            .driver()
            .try_authoritative_linear_script(&[
                ProofTactic::ApplyTheorem(application.clone()),
                ProofTactic::Solve,
            ])
            .expect("linear pure search should not fail")
            .expect("the checked conclusion should close the conjunction");
        let script_allocations = fact_node_allocations() - before_script;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            script_allocations <= allocation_bound,
            "size {size} pure linear script allocated {script_allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps().first(),
            Some(&ProofStep::ApplyTheorem(application.clone()))
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn pure_apply_using_selects_a_checked_conjunct_without_accepting_disjunctions() {
    let click_file = crate::surface::parse(LESS_THAN_IMPLIES_LESS_EQUAL)
        .expect("the fixture theorem should parse beside the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        proof_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let point = crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new());
    let left = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_210_000)));
    let right = ProgramValue::Int32(OldMachineTerm::Variable(Variable(8_210_001)));
    let premise = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let other = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let selected = SyntaxProposition::And(Box::new(premise.clone()), Box::new(other.clone()));
    let wrong_conjunction =
        SyntaxProposition::And(Box::new(other.clone()), Box::new(other.clone()));
    let disjunction = SyntaxProposition::Or(Box::new(premise.clone()), Box::new(other.clone()));
    let implication =
        SyntaxProposition::Implies(Box::new(other.clone()), Box::new(premise.clone()));
    let kernel_premise = lower_pure_theorem_proposition(
        "checked conjunct theorem application",
        &premise,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the theorem requirement should lower");
    let kernel_selected = lower_pure_theorem_proposition(
        "checked conjunct theorem application",
        &selected,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the conjunction should lower");
    let kernel_disjunction = lower_pure_theorem_proposition(
        "checked conjunct theorem application",
        &disjunction,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the disjunction should lower");
    let kernel_wrong_conjunction = lower_pure_theorem_proposition(
        "checked conjunct theorem application",
        &wrong_conjunction,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the unrelated conjunction should lower");
    let kernel_implication = lower_pure_theorem_proposition(
        "checked conjunct theorem application",
        &implication,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the implication should lower");
    assert!(exact_fact_is_available(
        &kernel_premise,
        std::slice::from_ref(&kernel_selected)
    ));
    assert!(!exact_fact_is_available(
        &kernel_premise,
        &[kernel_disjunction]
    ));
    assert!(!exact_fact_is_available(
        &kernel_premise,
        &[kernel_wrong_conjunction]
    ));
    assert!(!exact_fact_is_available(
        &kernel_premise,
        &[kernel_implication]
    ));

    let conclusion = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(right.clone())),
    };
    let kernel_conclusion = lower_pure_theorem_proposition(
        "checked conjunct theorem application",
        &conclusion,
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the theorem conclusion should lower");
    let theorem_context = PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        integer_values: PersistentBinderMap::default(),
        point: point.clone(),
        values: ProgramValueBindings::new(),
        array_refs: BTreeMap::new(),
        requires: vec![kernel_selected],
        surface_requirements: SurfacePropositionMap::default(),
    };
    let root = Proof::for_pure_goal(
        "checked conjunct theorem application",
        &theorem_context.requires,
        kernel_conclusion,
        &theorem_context,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let application = TheoremApplication {
        name: "less_than_implies_less_equal".to_string(),
        arguments: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(left)),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(right)),
        ],
    };
    let closed = root
        .driver()
        .apply_step(ProofStep::ApplyTheoremUsing {
            application,
            premises: vec![selected],
        })
        .expect("a checked conjunct should satisfy the theorem requirement");
    assert!(!closed.is_complete());
    assert!(
        closed
            .driver()
            .apply_step(ProofStep::Known)
            .unwrap()
            .is_complete()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn execution_unfold_forks_persistently_and_ignores_unrelated_facts() {
    let click_file = crate::surface::parse(
        r#"
            predicate selected(x: int32) { x == x }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test predicate and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let state = ExecutionState::new();
    let argument = ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(7)));
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let arguments = vec![argument.clone()];
    let surface = SyntaxProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: vec![SyntaxTerm::ProgramExpression(argument)],
    };
    let predicate = Proposition::Predicate {
        name: "selected".to_string(),
        arguments: vec![
            Term::ExecutionState(Box::new(state.clone())),
            Term::ProgramValue((ProgramValue::Int32(OldMachineTerm::constant(7))).into()),
        ],
    };

    for size in LOCAL_PROOF_FACT_SIZES {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(predicate.clone());
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&surface, &predicate)
            .expect("the selected predicate form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent unfold",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let successor = root
            .driver()
            .apply_step(ProofStep::UnfoldProposition(
                SyntaxProposition::PredicateCall {
                    name: "selected".into(),
                    arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        int32(7),
                    ))],
                },
            ))
            .expect("the exact selected predicate should unfold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 32 * logarithmic_height + 128;
        assert!(
            allocations <= allocation_bound,
            "size {size} unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );

        assert!(root.state.shares_state_with(&retained_root.state));
        assert_eq!(root.facts().to_vec().len(), size as usize + 1);
        assert_eq!(root.certificate().steps(), &[]);
        assert_eq!(
            successor.certificate().steps(),
            &[ProofStep::UnfoldProposition(
                SyntaxProposition::PredicateCall {
                    name: "selected".into(),
                    arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        int32(7)
                    ))]
                }
            )]
        );
        assert!(successor.facts().to_vec().len() > root.facts().to_vec().len());
        let root_execution = root.execution().expect("root execution state");
        let successor_execution = successor.execution().expect("successor execution state");
        assert!(
            root_execution
                .core
                .state
                .shares_storage_with(&successor_execution.core.state),
            "unfold does not alter the C frontier"
        );
        assert!(
            root_execution
                .core
                .effect_facts
                .shares_storage_with(&successor_execution.core.effect_facts),
            "unfold does not copy unrelated effect history"
        );

        assert!(successor.facts().to_vec().len() > size as usize + 1);
    }
}

#[test]
fn choose_body_leaves_support_have_and_reject_other_binders_and_epochs() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                requires exists (k: int32) { k == x and k >= 0 };
                ensures result == x;
            }
        "#,
    )
    .expect("the existential requirement should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let function = parsed_function.to_kernel_function();
    let predicates = PredicateEnvironment::new(click_file.predicate_definitions());
    let click_functions = ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorems = TheoremEnvironment::new(click_file.theorem_definitions());
    let resources = ResourceEnvironment::new(click_file.resource_definitions());
    let execution_environment = ExecutionEnvironment::new();
    let state = ExecutionState::new();
    let argument = ProgramExpression::Value(int32(7));
    let arguments = vec![argument.clone()];
    let Requirement::Proposition(source_surface) = &function_block.requires()[0] else {
        unreachable!()
    };
    let source = lower_fixed_state_proposition_with_assumptions(
        source_surface,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicates, &click_functions),
    )
    .unwrap();
    let owner = CallerSourceOwnerId::ordinary("test.c", "identity");
    let source_id = RequirementSourceId {
        owner: owner.clone(),
        outer_ordinal: 0,
    };
    let entry_origins = vec![EntryFactOrigin::Requirement {
        source_id: source_id.clone(),
        role: RequirementFactRole::Principal {
            unfolding_path: Vec::new(),
        },
    }];
    let caller_requirement_index = CallerRequirementIndex::from_entry_facts(
        owner.clone(),
        function_block,
        parsed_function.parameters(),
        std::slice::from_ref(&source),
        &entry_origins,
        crate::kernel::MemoryStateIdentity::of(state.memory()),
    );
    let root = Proof::for_execution_frontier(
        "chosen projection",
        0,
        ExecutionProofState::at_entry(
            state.clone(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![source.clone()],
        ExecutionProofConstants {
            function_entry_state: Some(state.clone()),
            execution_start_facts: Arc::new(PureFactList::from(vec![source])),
            entry_fact_origins: entry_origins.into(),
            caller_requirement_index: caller_requirement_index.into(),
            caller_source_owner: Some(owner),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &execution_environment,
        &resources,
        SpecDefinitions::new(&predicates, &click_functions),
        &theorems,
    );
    let scope_goal = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let scope = root
        .driver()
        .open_have(scope_goal)
        .expect("a proposition scope should open at the entry frontier");
    let chosen = scope
        .body()
        .driver()
        .apply_step(ProofStep::Choose(ProofChoice {
            name: "candidate".to_string(),
            source: ProofFactSource::Requirement(0),
        }))
        .expect("choose should use the selected existential");
    let leaf_surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            expression: Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                "candidate".into(),
            ))),
        },
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            expression: Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                "x".into(),
            ))),
        },
    };
    let wrong_binder = substitute_click_proposition(
        &leaf_surface,
        &BTreeMap::from([(
            "candidate".to_string(),
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                ("other".to_string()).into(),
            )),
        )]),
    )
    .expect("renaming a citation should be capture-safe");
    assert!(
        chosen
            .driver()
            .apply_step(known_have_step(wrong_binder))
            .is_err()
    );
    let wrong_epoch_selector = ProgramPointSelector::ProgramPoint(ProgramPointRef {
        region: CodeRegionRef::Function,
        kind: ProgramPointKind::Exit,
    });
    let wrong_epoch_expression = |expression: &SyntaxTerm| match expression {
        SyntaxTerm::At { expression, .. } => SyntaxTerm::At {
            selector: wrong_epoch_selector.clone(),
            expression: expression.clone(),
        },
        other => panic!("chosen projection must retain its source state: {other:?}"),
    };
    let wrong_epoch = match &leaf_surface {
        SyntaxProposition::Comparison {
            left,
            operator,
            right,
        } => SyntaxProposition::Comparison {
            left: wrong_epoch_expression(left),
            operator: *operator,
            right: wrong_epoch_expression(right),
        },
        other => panic!("chosen projection must retain its source state: {other:?}"),
    };
    assert!(
        chosen
            .driver()
            .apply_step(known_have_step(wrong_epoch))
            .is_err()
    );
    let extracted = chosen
        .driver()
        .apply_step(known_have_step(leaf_surface.clone()))
        .expect("extract should consume the checked chosen-body leaf");
    assert!(matches!(
        extracted.certificate().steps(),
        [ProofStep::Choose(_), ProofStep::Have { .. }]
    ));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn execution_resource_observation_is_retained_transactional_and_logarithmic() {
    let click_file = crate::surface::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                views marker(x);
                ensures returns_x: result == x;
            } by {
                observe(marker(x));
                step_until(function.exit);
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource.clone()),
            _ => None,
        })
        .expect("the test function should require its marker view");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
            )
            .expect("the marker resource definition should lower"),
        );
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let empty_state = ExecutionState::new();
    let lowered = lower_resource_clause(
        &resource,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        empty_state.memory(),
    )
    .expect("the required marker view should lower");
    let state =
        empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "persistent resource observation",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let observed = root
            .driver()
            .apply_step(ProofStep::ObserveResource(resource.clone()))
            .expect("the held marker view should be observable");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} observation allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            observed.certificate().steps(),
            &[ProofStep::ObserveResource(resource.clone())]
        );
        assert!(!observed.added_facts().is_empty());
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(
            root.driver()
                .apply_step(ProofStep::ObserveResource(missing))
                .is_err()
        );
        assert!(root.certificate().steps().is_empty());
        assert_eq!(root.facts().to_vec().len(), size as usize);
    }
}

#[test]
fn observe_composite_keeps_the_defined_read_at_the_selected_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let click_file = crate::surface::parse(
        r#"
        resource cell(p: int32*) {
            views *p;
            fact defined(*p);
        }
        verifying "read.c";
        int32 read(int32* p) {
            views cell(p);
            ensures true;
        }
        "#,
    )
    .unwrap();
    let function_block = &click_file.function_blocks()[0];
    let [Requirement::Resource(resource)] = function_block.requires() else {
        panic!("expected the cell resource as the only requirement");
    };
    let parsed = syntax::parse_function("int32 read(int32* p) { return *p; }").unwrap();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(click_file.resource_definitions());
    let specs = SpecDefinitions::new(&predicates, &functions);
    let view_input = ResourceSpec::composite(
        KernelResourceAccessMode::View,
        "cell".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
    );
    let function = parsed
        .to_kernel_function()
        .with_resource_summary(vec![view_input], vec![])
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(&resources, specs)
                .unwrap(),
        );
    let environment = ExecutionEnvironment::new();
    let pointer = Address::symbolic(Variable(88_022));
    let arguments = [ProgramExpression::Value(ProgramValue::typed_pointer(
        pointer.clone(),
        ProgramType::Int32Pointer,
    ))];
    let memory = SymbolicMemory::new().with_block(pointer.base.clone(), 4);
    let held = lower_resource_clause(
        resource,
        ParameterBinding::new(parsed.parameters(), &arguments),
        &memory,
    )
    .unwrap();
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(held));
    let state = crate::kernel::execution_state_with_borrowed_contract_inputs(
        state,
        &function,
        &arguments,
        &PureFactContext::new(),
    )
    .unwrap();
    assert!(matches!(
        state.memory().load(&pointer),
        ExpressionOutcome::UndefinedBehavior(_)
    ));
    let point = state.observation_point_id().unwrap();
    let root = Proof::for_execution_frontier(
        "observe a defined cell",
        0,
        ExecutionProofState::at_entry(
            state,
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![],
        ExecutionProofConstants::default(),
        function_block,
        &function,
        &parsed,
        &arguments,
        &environment,
        &resources,
        specs,
        &theorems,
    );
    let observed = root
        .driver()
        .apply_step(ProofStep::ObserveResource(resource.clone()))
        .expect("observe should name the held cell and publish its definedness");
    let after = &observed.execution().unwrap().core.state;
    assert!(matches!(
        after.memory().load(&pointer),
        ExpressionOutcome::Value(_)
    ));
    assert_eq!(after.observation_point_id(), Some(point));
    assert!(
        observed
            .added_facts()
            .contains(&Proposition::MemoryReadDefined {
                point: Default::default(),
                at: Some(point),
                memory: after.memory().clone(),
                pointer,
                value_type: ProgramType::Int32,
            })
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn execution_resource_unfold_is_retained_transactional_and_logarithmic() {
    let click_file = crate::surface::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                owns marker(x);
                ensures returns_x: result == x;
            } by {
                unfold(marker(x));
                step_until(function.exit);
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource.clone()),
            _ => None,
        })
        .expect("the test function should own its marker resource");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
            )
            .expect("the marker resource definition should lower"),
        );
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let empty_state = ExecutionState::new();
    let lowered = lower_resource_clause(
        &resource,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        empty_state.memory(),
    )
    .expect("the owned marker resource should lower");
    let state =
        empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "persistent resource unfold",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let unfolded = root
            .driver()
            .apply_step(ProofStep::UnfoldResource(resource.clone()))
            .expect("the owned marker resource should unfold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            unfolded.certificate().steps(),
            &[ProofStep::UnfoldResource(resource.clone())]
        );
        assert!(!unfolded.added_facts().is_empty());
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(
            root.driver()
                .apply_step(ProofStep::UnfoldResource(missing))
                .is_err()
        );
        assert!(root.certificate().steps().is_empty());
        assert_eq!(root.facts().to_vec().len(), size as usize);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn execution_resource_fold_is_retained_transactional_and_logarithmic() {
    let click_file = crate::surface::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                owns marker(x);
                ensures returns_x: result == x;
            } by {
                unfold(marker(x));
                fold(marker(x));
                step_until(function.exit);
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource.clone()),
            _ => None,
        })
        .expect("the test function should own its marker resource");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
            )
            .expect("the marker resource definition should lower"),
        );
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let empty_state = ExecutionState::new();
    let lowered = lower_resource_clause(
        &resource,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        empty_state.memory(),
    )
    .expect("the owned marker resource should lower");
    let state =
        empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "persistent resource fold",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let unfolded = root
            .driver()
            .apply_step(ProofStep::UnfoldResource(resource.clone()))
            .expect("the owned marker resource should unfold before folding");
        let retained_unfolded = unfolded.clone();
        let before = fact_node_allocations();
        let folded = unfolded
            .driver()
            .apply_step(ProofStep::FoldResource(resource.clone()))
            .expect("the exposed marker body should fold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} fold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            folded.certificate().steps(),
            &[
                ProofStep::UnfoldResource(resource.clone()),
                ProofStep::StepProved {
                    step: Box::new(ProofStep::FoldResource(resource.clone())),
                    proof: StepProofCertificate::By(Box::new(
                        ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap(),
                    )),
                },
            ]
        );
        assert!(folded.added_facts().is_empty());
        assert!(unfolded.state.shares_state_with(&retained_unfolded.state));

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(
            unfolded
                .driver()
                .apply_step(ProofStep::FoldResource(missing))
                .is_err()
        );
        assert_eq!(
            unfolded.certificate().steps(),
            &[ProofStep::UnfoldResource(resource.clone())]
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn execution_open_scope_owns_entry_body_and_close_transactionally() {
    let click_file = crate::surface::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "two_steps.c";
            int32 two_steps(int32 x) {
                owns marker(x);
                ensures returns_x: result == x;
            } by {
                with(marker(x)) { step(); }
                step();
            }
        "#,
    )
    .expect("test resource scope should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource.clone()),
            _ => None,
        })
        .expect("the test function should own its marker resource");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function("int32 two_steps(int32 x) { x = x; return x; }")
        .expect("test C function should parse");
    let function = parsed_function
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
            )
            .expect("the marker resource definition should lower"),
        );
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let empty_state = ExecutionState::new();
    let lowered = lower_resource_clause(
        &resource,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        empty_state.memory(),
    )
    .expect("the owned marker resource should lower");
    let state =
        empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));
    let reflexive = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramBinding("x".to_string()),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramBinding("x".to_string()),
    };
    let _exposed_reflexive = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "persistent open scope",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let scope = root
            .begin_open(resource.clone(), 0)
            .expect("the held marker should open");
        let rejected = scope
            .driver()
            .open_have(reflexive.clone())
            .expect("the open scope should begin a rejected proposition subproof");
        assert!(rejected.driver().apply_step(ProofStep::Step).is_err());
        assert!(rejected.body().certificate().steps().is_empty());
        let nested = scope
            .driver()
            .open_have(reflexive.clone())
            .expect("the open scope should begin a proposition subproof")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the exposed marker fact should close the nested proof");
        let scope = scope
            .join_nested(nested)
            .expect("the checked have should advance the open scope");
        let scope = scope
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the owned resource scope should retain its checked statement step");
        let closed = scope.join().expect("the marker body should close");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 160 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} open scope allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            closed.certificate().steps(),
            &[ProofStep::Open {
                resource: resource.clone(),
                deferred_tail: None,
                proof: Box::new(
                    ProofCertificate::from_steps(vec![
                        ProofStep::Have {
                            proposition: reflexive.clone(),
                            proof: Box::new(
                                ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap(),
                            ),
                        },
                        ProofStep::Step,
                    ])
                    .unwrap(),
                ),
            }]
        );
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let sibling_scope = root
            .begin_open(resource.clone(), 0)
            .expect("the retained root should open a sibling scope");
        let sibling_nested = sibling_scope
            .driver()
            .open_have(reflexive.clone())
            .expect("the sibling should begin its own nested proof")
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the sibling nested proof should close");
        let unrelated_scope = root
            .begin_open(resource.clone(), 0)
            .expect("the retained root should open an unrelated scope");
        assert!(unrelated_scope.join_nested(sibling_nested).is_err());
        assert!(unrelated_scope.body().certificate().steps().is_empty());
        assert!(
            closed
                .execution()
                .is_some_and(|execution| !execution.core.frontier.is_at_function_exit())
        );

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(root.begin_open(missing, 0).is_err());
        assert!(root.certificate().steps().is_empty());

        let terminal = root
            .begin_open(resource.clone(), 0)
            .expect("the retained root should open an alternate scope")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the terminal scope should cross its assignment")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the terminal scope should cross its return")
            .join()
            .expect("an exit-reaching open should defer its close");
        let terminal_execution = terminal
            .execution()
            .expect("the terminal open retains execution state");
        assert!(terminal_execution.core.frontier.is_at_function_exit());
        assert_eq!(
            terminal_execution.presentation.post_execution_tactics.len(),
            1
        );
        assert_eq!(
            terminal.certificate().steps(),
            &[ProofStep::Open {
                resource: resource.clone(),
                deferred_tail: None,
                proof: Box::new(
                    ProofCertificate::from_steps(vec![ProofStep::Step, ProofStep::Step]).unwrap(),
                ),
            }]
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn execution_transport_forks_without_copying_unrelated_state() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let state = ExecutionState::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(7))),
    };
    let kernel = lower_fixed_state_proposition_with_assumptions(
        &surface,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("constant equality should lower at the frontier position");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel.clone());
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&surface, &kernel)
            .expect("the source form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent transport",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let successor = root
            .driver()
            .apply_ordinary_transport_steps(&surface, vec![ProofStep::Known])
            .expect("the exact ambient fact should verify");

        assert!(root.state.shares_state_with(&retained_root.state));
        assert_eq!(root.certificate().steps(), &[]);
        assert_eq!(
            successor.certificate().steps(),
            &[ProofStep::Have {
                proposition: surface.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
            }]
        );
        assert_eq!(successor.added_facts(), std::slice::from_ref(&kernel));
        assert_eq!(
            successor.state().checked_facts(),
            std::slice::from_ref(&kernel)
        );
        let root_execution = root.execution().expect("root execution state");
        let successor_execution = successor.execution().expect("successor execution state");
        assert!(
            root_execution
                .core
                .state
                .shares_storage_with(&successor_execution.core.state),
            "transport does not alter the C state"
        );
        assert!(
            root_execution
                .core
                .effect_facts
                .shares_storage_with(&successor_execution.core.effect_facts),
            "transport does not copy unrelated effect history"
        );
        assert!(
            root_execution
                .presentation
                .surface_propositions
                .shares_persistent_storage_with(
                    &successor_execution.presentation.surface_propositions
                ),
            "an identity transport does not change the recorded surface lowerings"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn execution_transport_search_returns_checked_successors_and_scales() {
    let click_file = crate::surface::parse(
        r#"
            int32 choose_second(int32 first, int32 second) {
                ensures returns_second: result == second by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function(
        "int32 choose_second(int32 first, int32 second) { first = second; return first; }",
    )
    .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = ExecutionState::new();
    let arguments = vec![
        ProgramExpression::Value(int32(3)),
        ProgramExpression::Value(int32(5)),
    ];
    let term = |variable| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(variable)),
        )))
    };
    let source = SyntaxProposition::Comparison {
        left: term(8_170_000),
        operator: ComparisonOperator::LessThan,
        right: term(8_170_001),
    };
    let missing = SyntaxProposition::Comparison {
        left: term(8_170_002),
        operator: ComparisonOperator::Equal,
        right: term(8_170_003),
    };
    let kernel_source = lower_fixed_state_proposition_with_assumptions(
        &source,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact transport source should lower");

    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel_source.clone());
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&source, &kernel_source)
            .expect("the selected source form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent transport search",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let progressed = root
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the meaningful assignment should advance the execution Proof");
        if size == 16 {
            let retained = progressed.clone();
            let rejected = crate::kernel::search::ProofSearch::try_fact_transport_from_candidates(
                &(progressed),
                &source,
                &missing,
                [source.clone()],
            )
            .expect("a bounded rejected transport search should remain prompt");
            assert!(
                rejected.is_none(),
                "an unrelated target must not be manufactured by transport search"
            );
            assert!(progressed.state.shares_state_with(&retained.state));
            assert!(matches!(
                progressed.certificate().steps(),
                [ProofStep::Step]
            ));
        }

        let before = fact_node_allocations();
        let transported = crate::kernel::search::ProofSearch::try_fact_transport_from_candidates(
            &(progressed),
            &source,
            &source,
            [source.clone()],
        )
        .expect("the bounded source candidate search should run")
        .expect("the source candidate should produce one checked transport descendant");
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            transported.certificate().steps(),
            [
                ProofStep::Step,
                ProofStep::Have {
                    proposition,
                    proof,
                },
            ] if proposition == &source
                && matches!(proof.steps(), [ProofStep::Known])
        ));
        assert!(root.certificate().steps().is_empty());
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} execution transport search allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn statement_assignment_step_ignores_unrelated_proof_facts() {
    let click_file = crate::surface::parse(
        r#"
            int32 set_one(int32 x) {
                ensures returns_one: result == 1 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function("int32 set_one(int32 x) { x = 1; return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let mut samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "contextual local assignment",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let stepped = crate::kernel::search::ProofSearch::try_statement_step(&(root))
            .expect("the assignment step should remain available")
            .expect("unrelated facts should not force mutable planning");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        assert!(matches!(stepped.certificate().steps(), [ProofStep::Step]));
        assert_eq!(stepped.facts().to_vec(), root.facts().to_vec());
        assert!(
            !stepped
                .execution()
                .expect("assignment successor retains execution")
                .core
                .frontier
                .is_at_function_exit()
        );
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let logarithmic_bound = base_allocations + 8 * (height - base_height);
        assert!(
            allocations <= logarithmic_bound,
            "size {size} assignment step allocated {allocations} persistent nodes (bound {logarithmic_bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn contextual_store_step_scales_with_unrelated_named_facts() {
    let click_file = crate::surface::parse(
        r#"
            int32 write_in_bounds(int32 p[], int32 i, int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires i >= 0;
                requires i < n;
                consumes p[0..n];
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function(
        "int32 write_in_bounds(int32 p[], int32 i, int32 n) { p[i] = 9; return 0; }",
    )
    .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let (state, arguments, base_facts, base_surfaces) = initial_claim_context(
        function_block,
        &parsed_function,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        "contextual store step",
    )
    .expect("the resource-backed claim context should initialize");
    let mut samples = Vec::new();

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = base_facts.clone();
        let mut surface_propositions = base_surfaces.clone();
        for index in 0..size {
            let fact = indexed_fact(index + 10_000);
            let surface = SyntaxProposition::Comparison {
                left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    format!("unrelated_{index}").into(),
                )),
                operator: ComparisonOperator::Equal,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
            };
            surface_propositions
                .record_lowering(&surface, &fact)
                .expect("the unrelated surface fact should be indexed");
            pure_facts.push(fact);
        }
        let root = Proof::for_execution_frontier(
            "contextual store step",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts.into_vec(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let stepped = crate::kernel::search::ProofSearch::try_statement_step(&(root))
            .expect("the contextual store step should remain available")
            .expect("the statement-local bounds and resource should prove the store");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let certificate = stepped.certificate();
        // A bare `step()` names no premise: the statement runs in the
        // whole context and selection cannot leak an unrelated fact.
        let [ProofStep::Step] = certificate.steps() else {
            panic!(
                "the selected store should retain one bare statement step: {:#?}",
                certificate.steps()
            );
        };
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let logarithmic_bound = base_allocations * height / base_height;
        assert!(
            allocations <= logarithmic_bound,
            "size {size} contextual store step allocated {allocations} persistent nodes (bound {logarithmic_bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn checked_statement_step_ignores_unrelated_proof_facts() {
    let click_file = crate::surface::parse(
        r#"
            int32 constant(int32 x) {
                ensures returns_one: result == 1 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function("int32 constant(int32 x) { return 1; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut samples = Vec::new();

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "persistent statement step",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let retained_root = root.clone();
        // A bare step runs in the whole context: unrelated ambient facts
        // neither block it nor enter its certificate.
        let stepped = crate::kernel::search::ProofSearch::try_statement_step(&(root))
            .expect("the bare statement step should remain available")
            .expect("unrelated ambient facts must not block the bare step");
        assert!(matches!(stepped.certificate().steps(), [ProofStep::Step]));
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let marked = root
            .driver()
            .apply_step(ProofStep::Mark("candidate".to_string()))
            .expect("a fresh proof mark should produce a checked descendant");
        assert!(matches!(
            marked.certificate().steps(),
            [ProofStep::Mark(name)] if name == "candidate"
        ));
        let duplicate = marked
            .driver()
            .apply_step(ProofStep::Mark("candidate".to_string()))
            .err()
            .expect("a duplicate mark must reject the candidate");
        assert!(duplicate.message().contains("duplicate proof mark"));
        assert!(matches!(
            marked.certificate().steps(),
            [ProofStep::Mark(name)] if name == "candidate"
        ));
        let before = fact_node_allocations();
        let completed = root
            .driver()
            .apply_step(ProofStep::Step)
            .expect("an explicit return step should certify");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));
        assert!(
            completed
                .execution()
                .expect("statement successor retains execution")
                .core
                .frontier
                .is_at_function_exit()
        );
        assert!(matches!(completed.certificate().steps(), [ProofStep::Step]));
        let alternative = root
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the retained ancestor should support another checked descendant");
        assert_eq!(alternative.certificate(), completed.certificate());
        let root_execution = root.execution().expect("root execution state");
        let completed_execution = completed
            .execution()
            .expect("statement successor retains execution state");
        assert!(
            root_execution
                .core
                .state
                .shares_nonlocal_storage_with(&completed_execution.core.state),
            "a return step should not copy unchanged memory, resources, or populations"
        );
        assert!(completed.is_at_function_exit());
        assert!(matches!(completed.certificate().steps(), [ProofStep::Step]));
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let logarithmic_bound = base_allocations + 24 * (height - base_height);
        assert!(
            allocations <= logarithmic_bound,
            "size {size} statement step allocated {allocations} persistent nodes (logarithmic bound {logarithmic_bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.0s in the parallel gate"]
fn close_invariants_is_a_transactional_constant_local_proof_step() {
    let click_file = crate::surface::parse(
        r#"
            int32 loop_region(int32 x) {
                ensures unchanged: result == x by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function("int32 loop_region(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());

    for size in [16_u32, 64, 256, 1024, 4096] {
        let make_root = |loop_invariant_region: bool| {
            let frontier = if loop_invariant_region {
                ExecutionFrontier {
                    region: ExecutionRegionKind::LoopBody,
                    position: FrontierPosition::RegionBoundary,
                    ..ExecutionFrontier::default()
                }
            } else {
                ExecutionFrontier::default()
            };
            Proof::for_execution_frontier(
                "persistent close invariants",
                0,
                ExecutionProofState::at_entry(
                    ExecutionState::new(),
                    frontier,
                    RecordedStates::new(),
                    SurfacePropositionMap::default(),
                    PersistentSequence::default(),
                ),
                (0..size).map(indexed_fact).collect::<Vec<_>>(),
                ExecutionProofConstants::default(),
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
            )
        };

        let outside_loop = make_root(false);
        assert!(
            outside_loop
                .state
                .request_frontier_invariant_closure()
                .is_err(),
            "closure is restricted to loop-region proofs"
        );
        assert!(outside_loop.certificate().steps().is_empty());

        let root = make_root(true);
        let checks = vec![crate::kernel::LoopInvariantCheck::new(
            crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::Value(int32(0)),
                operator: crate::kernel::ComparisonOperator::LessEqual,
                right: crate::kernel::SpecExpression::Value(int32(0)),
            },
            None,
            None,
        )];
        let (body, scope) = root
            .state
            .open_invariant_body(
                &ExecutionState::new(),
                &ExecutionState::new(),
                &crate::kernel::IntegerTerm::var(crate::kernel::Variable(9_999)),
                &checks,
                &[],
                &[],
                &[],
                |_, _| PropositionPresentation {
                    surface: None,
                    surface_bindings: PersistentBinderMap::default(),
                    ..PropositionPresentation::default()
                },
            )
            .unwrap();
        let completed = body
            .apply_known(crate::kernel::proof::PropositionKnownContext::Exact)
            .ok()
            .unwrap();
        let retained =
            root.with_kernel_state(root.state.retain_invariant_body(scope, &completed).unwrap());
        let retained_core = &retained.execution().unwrap().core;
        let evidence = retained_core.checked_invariant_lowerings.as_ref().unwrap();
        assert_eq!(evidence.checks(), checks);
        retained
            .state
            .validate_checked_invariant_lowerings(&checks, &[])
            .unwrap();
        assert!(
            evidence
                .recorded_state()
                .shares_storage_with(&retained_core.state)
        );
        assert!(
            root.execution()
                .unwrap()
                .core
                .checked_invariant_lowerings
                .is_none()
        );
        let mut successor_core = retained_core.clone();
        assert!(Arc::ptr_eq(
            evidence,
            successor_core.checked_invariant_lowerings.as_ref().unwrap()
        ));
        successor_core.state = ExecutionState::new().with_local("changed", int32(1)).into();
        assert!(
            !evidence
                .recorded_state()
                .shares_storage_with(&successor_core.state)
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let Ok(requested) = root.state.request_frontier_invariant_closure() else {
            panic!("the first close should produce a checked descendant")
        };
        let closed = root.with_kernel_state(requested);
        // The one permitted node rewrites the sole goal's execution
        // state in the persistent goal collection; the bound stays
        // independent of ambient fact count.
        assert!(fact_node_allocations() - before <= 1);
        assert!(root.state.shares_state_with(&retained_root.state));
        assert!(root.certificate().steps().is_empty());
        // The closure request is a semantic-core update, not a certificate
        // leaf. `close_invariants() by`, carrying the checked body, is the only
        // step that records a closure; a bare request spells nothing a proof
        // could write, so it contributes no lineage of its own.
        assert!(closed.certificate().steps().is_empty());
        let execution = closed
            .execution()
            .expect("the successor retains execution state");
        assert!(execution.core.region_invariants_close_requested);
        assert!(
            execution.presentation.invariant_closer_step.is_none(),
            "source timing metadata is attached only at the check adapter boundary"
        );
        assert!(
            closed.state.request_frontier_invariant_closure().is_err(),
            "one path closes its invariant bundle at most once"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn proof_condition_split_filters_conflicts_without_rebuilding_facts() {
    let symbolic = Variable(50_000);
    let state = ExecutionState::new().with_local("x", int32(OldMachineTerm::Variable(symbolic)));
    let condition = ProgramExpression::LessThan(
        Box::new(ProgramExpression::Variable(("x".to_string()).into())),
        Box::new(ProgramExpression::Value(int32(0))),
    );
    let empty = PureFactStore::default();
    let branch = ProgramStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(ProgramStatement::Skip),
        else_branch: Box::new(ProgramStatement::Skip),
    };
    let (checked_split, unconstrained) = certified_proof_condition_split(
        &state,
        &empty,
        &branch,
        None,
        "persistent condition split",
        None,
    )
    .expect("a symbolic comparison should expose both paths");
    assert_eq!(unconstrained.len(), 2);
    let mut arm_theorems = [None, None];
    let mut arm_facts = [None, None];
    for transition in &unconstrained {
        let arm_index = usize::from(!transition.is_true);
        arm_theorems[arm_index] = Some(&transition.theorem);
        arm_facts[arm_index] = Some(&transition.pure_facts);
    }
    assert!(checked_split.validates_exhaustive_join(
        &state,
        &condition,
        &empty,
        arm_theorems,
        arm_facts,
    ));
    assert!(!checked_split.validates_exhaustive_join(
        &ExecutionState::new(),
        &condition,
        &empty,
        arm_theorems,
        arm_facts,
    ));
    assert!(!checked_split.validates_exhaustive_join(
        &state,
        &ProgramExpression::Value(int32(1)),
        &empty,
        arm_theorems,
        arm_facts,
    ));
    assert!(!checked_split.validates_exhaustive_join(
        &state,
        &condition,
        &empty.with_kernel_checked_fact(indexed_fact(99_999)),
        arm_theorems,
        arm_facts,
    ));
    assert!(!checked_split.validates_exhaustive_join(
        &state,
        &condition,
        &empty,
        [arm_theorems[1], arm_theorems[0]],
        arm_facts,
    ));
    let rejected_path_fact = unconstrained[0]
        .path_facts
        .first()
        .expect("a symbolic branch path should carry its condition fact")
        .clone();
    let selecting_fact = opposite_atomic_fact(&rejected_path_fact);

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
        available.push(selecting_fact.clone());
        let facts = PureFactStore::from_ordered(&available);
        assert!(facts.directly_conflicts_with(&rejected_path_fact));
        let before = fact_node_allocations();
        let transitions = certified_proof_condition_transitions(
            &state,
            &facts,
            &condition,
            "persistent condition split",
        )
        .expect("the selected condition path should certify");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 24 * logarithmic_height + 64;
        assert!(
            allocations <= allocation_bound,
            "size {size} condition split allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(transitions.len(), 1);
        assert_ne!(transitions[0].is_true, unconstrained[0].is_true);
        assert!(transitions[0].pure_facts.contains(&selecting_fact));
        assert!(matches!(
            implication_body(transitions[0].theorem.proposition()),
            Proposition::ProgramConditionEvaluates { .. }
        ));
        assert_eq!(facts.to_vec().len(), size as usize + 1);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn execution_proof_if_split_is_logarithmic_in_unrelated_facts() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures result == x;
            } by {
                close();
            }
        "#,
    )
    .expect("test contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function(
        "int32 identity(int32 x) { int32 copied; copied = x; return copied; }",
    )
    .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(71_000)),
    ))];
    let function_environment = ExecutionEnvironment::new();
    let condition = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::GreaterEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };

    let mut samples = Vec::new();
    for size in LOCAL_PROOF_FACT_SIZES {
        let root = Proof::for_execution_frontier(
            "execution proof if scaling",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        )
        .driver()
        .apply_step(ProofStep::Step)
        .expect("the declaration prefix should execute before the proof split");
        let before = fact_node_allocations();
        let (split, record) = root
            .split_focused_execution_if(condition.clone())
            .expect("the mid-execution proof if should open two siblings");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        for take_then in [true, false] {
            let focused = split.focus_execution_if_arm(&record, take_then).unwrap();
            let execution = focused.execution().unwrap();
            let cases = focused.facts().assumptions();
            assert_eq!(execution.core.publication_case_prefix().len(), 1);
            let selected = execution
                .presentation
                .case_assumptions
                .iter()
                .last()
                .unwrap();
            assert!(cases.proves_exact(selected.fact.as_ref().unwrap()));
            let opposite = split.focus_execution_if_arm(&record, !take_then).unwrap();
            let opposite_execution = opposite.execution().unwrap();
            let opposite_fact = opposite_execution
                .presentation
                .case_assumptions
                .iter()
                .last()
                .unwrap();
            assert!(!cases.proves_exact(opposite_fact.fact.as_ref().unwrap()));
            assert!(cases.proves_exact(&indexed_fact(0)));
        }

        let completed = split
            .focus_execution_if_arm(&record, true)
            .expect("the then sibling should remain open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the then assignment should check")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the then return should check")
            .focus_execution_if_arm(&record, false)
            .expect("the else sibling should remain open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the else assignment should check")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the else return should check")
            .join_focused_execution_if_terminal(&record)
            .expect("the two terminal proof cases should join");
        assert!(
            completed
                .execution()
                .unwrap()
                .core
                .publication_case_prefix()
                .is_empty()
        );
        assert!(completed.is_at_function_exit());
        assert!(matches!(
            completed.certificate().steps().last(),
            Some(ProofStep::If { .. })
        ));

        // A nested case must keep outer-before-inner source order and share
        // the original arm prefix through both terminal joins.
        let inner_condition = SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                ("x".to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        };
        let outer_then = split.focus_execution_if_arm(&record, true).unwrap();
        let outer_history = outer_then
            .execution()
            .unwrap()
            .presentation
            .branch_decisions
            .clone();
        let (inner, inner_record) = outer_then
            .split_focused_execution_if(inner_condition.clone())
            .unwrap();
        let inner_completed = inner
            .focus_execution_if_arm(&inner_record, true)
            .unwrap()
            .driver()
            .apply_step(ProofStep::Step)
            .unwrap()
            .driver()
            .apply_step(ProofStep::Step)
            .unwrap()
            .focus_execution_if_arm(&inner_record, false)
            .unwrap()
            .driver()
            .apply_step(ProofStep::Step)
            .unwrap()
            .driver()
            .apply_step(ProofStep::Step)
            .unwrap()
            .join_focused_execution_if_terminal(&inner_record)
            .unwrap();
        let inner_evidence = inner_completed
            .execution()
            .unwrap()
            .presentation
            .outcome_evidence
            .clone();
        let nested_completed = inner_completed
            .focus_execution_if_arm(&record, false)
            .unwrap()
            .driver()
            .apply_step(ProofStep::Step)
            .unwrap()
            .driver()
            .apply_step(ProofStep::Step)
            .unwrap()
            .join_focused_execution_if_terminal(&record)
            .unwrap();
        let nested_execution = nested_completed.execution().unwrap();
        let paths = &nested_execution.presentation.outcome_evidence;
        assert_eq!(paths.len(), 3);
        for (index, inner_value) in [true, false].into_iter().enumerate() {
            let decisions = &paths[index].branch_decisions;
            assert_eq!(decisions.value(&condition).unwrap(), Some(true));
            assert_eq!(
                decisions.value(&inner_condition).unwrap(),
                Some(inner_value)
            );
            assert!(decisions.ordered.tail_parent_is(&outer_history.ordered));
            assert!(
                decisions
                    .ordered
                    .shares_tail_with(&inner_evidence[index].branch_decisions.ordered)
            );
            let ordered = decisions.iter().collect::<Vec<_>>();
            assert_eq!(ordered.len(), 2);
            assert_eq!(ordered[0].condition, condition);
            assert_eq!(ordered[1].condition, inner_condition);
        }
        assert_eq!(
            paths[2].branch_decisions.value(&condition).unwrap(),
            Some(false)
        );
        assert_eq!(
            paths[2].branch_decisions.value(&inner_condition).unwrap(),
            None
        );
        assert!(nested_execution.presentation.branch_decisions.is_empty());
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations * height / base_height;
        assert!(
            allocations <= bound,
            "size {size} execution proof-if split allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn execution_proof_cases_split_is_logarithmic_in_unrelated_facts() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures result == x;
            } by {
                close();
            }
        "#,
    )
    .expect("test contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(72_000)),
    ))];
    let function_environment = ExecutionEnvironment::new();
    let nonnegative = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::GreaterEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let negative = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let disjunction =
        SyntaxProposition::Or(Box::new(nonnegative.clone()), Box::new(negative.clone()));
    let state = ExecutionState::new();
    let lowered_disjunction = lower_fixed_state_proposition_with_assumptions(
        &disjunction,
        &PureFactContext::new(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
    )
    .expect("the exact cases disjunction should lower");
    let Proposition::Or(expected_left, expected_right) = lowered_disjunction.clone() else {
        panic!("the cases proposition should lower to a disjunction");
    };

    let mut samples = Vec::new();
    for size in LOCAL_PROOF_FACT_SIZES {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(lowered_disjunction.clone());
        let root = Proof::for_execution_frontier(
            "execution proof cases scaling",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let before = fact_node_allocations();
        let (split, record) = root
            .split_focused_execution_disjunction(disjunction.clone())
            .expect("exact cases should open two execution siblings");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));
        let left = split
            .focus_execution_if_arm(&record, true)
            .expect("the left cases sibling should focus");
        assert_eq!(left.added_facts(), std::slice::from_ref(&*expected_left));
        let right = left
            .focus_execution_if_arm(&record, false)
            .expect("the right cases sibling should focus");
        assert_eq!(right.added_facts(), std::slice::from_ref(&*expected_right));
        assert!(root.certificate().steps().is_empty());
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations * height / base_height;
        assert!(
            allocations <= bound,
            "size {size} execution cases split allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn empty_execution_branch_joins_checked_proof_arms_at_the_shared_frontier() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                ensures returns_x: result == x by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function =
        syntax::parse_function("int32 identity(int32 x) { if (x < 0) {} else {} return x; }")
            .expect("test C branch should parse");
    let function = parsed_function.to_kernel_function();
    let argument = ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(
        Variable(60_000),
    )));
    let arguments = vec![argument];
    let function_environment = ExecutionEnvironment::new();
    let mut allocation_samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut statement_delta: Option<Vec<Proposition>> = None;
    for size in [16_u32, 64, 256, 1024, 4096] {
        let frontier = ExecutionFrontier {
            next_statement_index: 0,
            ..ExecutionFrontier::default()
        };
        let root = Proof::for_execution_frontier(
            "empty branch proof",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let before = fact_node_allocations();
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open two sibling arms");
        assert!(record.arm_id(true).is_some());
        assert!(record.arm_id(false).is_some());
        let joined = split
            .join_focused_execution_empty(&record)
            .expect("identical empty arms should rejoin");
        let allocations = fact_node_allocations() - before;
        allocation_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Branch {
                ensuring: None,
                then_proof,
                else_proof,
            }] if then_proof.steps().is_empty() && else_proof.steps().is_empty()
        ));
        assert!(root.certificate().steps().is_empty());
        let execution = joined
            .execution()
            .expect("joined proof should own its continuation");
        assert!(
            execution
                .presentation
                .recorded_states
                .get(&ProgramPointRef {
                    region: CodeRegionRef::Region(0),
                    kind: ProgramPointKind::Exit,
                })
                .is_some()
        );
        assert_eq!(execution.presentation.branch_path.len(), 0);
        let completed = joined
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the joined continuation should execute its return");
        assert!(
            completed
                .added_facts()
                .iter()
                .all(|fact| { !(0..size).any(|index| *fact == indexed_fact(index)) })
        );
        if let Some(expected) = &statement_delta {
            assert_eq!(completed.added_facts(), expected.as_slice());
        } else {
            statement_delta = Some(completed.added_facts().to_vec());
        }
        assert!(
            completed
                .execution()
                .expect("completed proof retains execution state")
                .core
                .frontier
                .is_at_function_exit()
        );
    }
    let (_, base_height, base_allocations) = allocation_samples[0];
    // Scope forks may maintain more indexes; their growth must remain
    // logarithmic in the inherited context, not linear in its fact count.
    for (size, height, allocations) in allocation_samples {
        let allocation_bound = base_allocations * height / base_height;
        assert!(
            allocations <= allocation_bound,
            "size {size} checked execution branch allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
        );
    }
}

#[test]
fn cursor_execution_branch_join_retains_structural_reads_without_bindings() {
    let click_file = crate::surface::parse(
        r#"
            int32 branch_load(int32 x, int32 p[1]) {
                ensures returns_any: result == result by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function(
        "int32 branch_load(int32 x, int32 p[1]) { if (x < 0) { return p[0]; } else { return p[0]; } }",
    )
    .expect("test C branch should parse");
    let function = parsed_function.to_kernel_function();
    let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            pointer.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        ))),
    );
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            60_001,
        )))),
        ProgramExpression::Value(ProgramValue::pointer(pointer.clone())),
    ];
    let function_environment = ExecutionEnvironment::new();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let root = Proof::for_execution_frontier(
        "cursor load branch proof",
        0,
        ExecutionProofState::at_entry(
            state.clone(),
            ExecutionFrontier {
                next_statement_index: 0,
                ..ExecutionFrontier::default()
            },
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        Vec::new(),
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let (split, record) = root
        .split_focused_execution_branch()
        .expect("symbolic condition should expose both load branches");
    let then_completed = split
        .focus_split_arm(&record, true)
        .expect("then branch should be open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("then return should execute through the cursor");
    let advanced = then_completed
        .focus_split_arm(&record, false)
        .expect("else branch should be open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("else return should execute through the cursor");
    let joined = advanced
        .join_focused_execution_terminal(&record)
        .expect("terminal load branches should join");
    let execution = joined
        .execution()
        .expect("joined execution should remain present");
    assert!(execution.presentation.generated_load_bindings.is_empty());
    assert!(
        execution
            .presentation
            .generated_load_binding_events
            .is_empty()
    );
    let terminal_view = joined
        .finalization_view()
        .expect("terminal cursor outcome should retain its evidence");
    let outcome_count = terminal_view
        .frontier
        .execution()
        .expect("terminal frontier should retain checked outcomes")
        .paths()
        .len();
    assert!(outcome_count > 0);
    for path_index in 0..outcome_count {
        assert!(terminal_view.generated_load_bindings(path_index).is_empty());
    }
    for path in terminal_view.frontier.execution().unwrap().paths() {
        assert!(matches!(path.outcome(),
            FunctionOutcome::Return { value, .. }
                if matches!(value.native().as_ref(), ProgramValue::Int32(OldMachineTerm::MemoryLoad(_, at, crate::kernel::LoadKind::Int32)) if **at == pointer)));
    }

    // A condition fact selects one arm, exercising the single-transition
    // cursor path that records metadata immediately before advancing the
    // selected successor.
    let selecting_fact = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(OldMachineTerm::Variable(Variable(60_001))),
            right: Box::new(OldMachineTerm::constant(0)),
        },
        true,
    );
    let selected_root = Proof::for_execution_frontier(
        "cursor selected load proof",
        0,
        ExecutionProofState::at_entry(
            state,
            ExecutionFrontier {
                next_statement_index: 0,
                ..ExecutionFrontier::default()
            },
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![selecting_fact],
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let (selected_split, selected_record) = selected_root
        .split_focused_execution_branch()
        .expect("condition fact should retain the selected load branch");
    assert_eq!(selected_record.sole_feasible_arm(), Some(true));
    let selected = selected_split
        .focus_split_arm(&selected_record, true)
        .expect("selected load branch should be open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("selected return should execute through the cursor");
    let selected = selected
        .finish_focused_execution_decided(&selected_record)
        .expect("selected load branch should finish as a focused path");
    let selected_execution = selected
        .execution()
        .expect("selected execution should retain its presentation");
    assert!(
        selected_execution
            .presentation
            .generated_load_bindings
            .is_empty()
    );
}

fn generated_load_source_event_fixture(
    variable: u32,
    occurrence: u32,
    pointer_offset: u32,
) -> crate::kernel::GeneratedLoadSourceEvent {
    let pointer = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::constant(pointer_offset.into()),
    );
    crate::kernel::GeneratedLoadSourceEvent::new(
        crate::kernel::LoadSourceId {
            owner: crate::kernel::LoadSourceOwnerId {
                source_unit: std::sync::Arc::from("source.c"),
                function: std::sync::Arc::from("load"),
            },
            occurrence,
            reference_access: None,
        },
        crate::kernel::GeneratedLoadBinding::Exact {
            variable: Variable(variable.into()),
            retained_state: crate::kernel::MemoryStateIdentity::of(&SymbolicMemory::new()),
            pointer: pointer.clone(),
            load: OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new()),
                Box::new(pointer),
                crate::kernel::LoadKind::Int32,
            ),
            typed_pointer_value: None,
            observed_pointer_read: None,
        },
    )
    .expect("the fixture carries an exact generated-load binding")
}

fn generated_load_source_execution() -> ExecutionProofState {
    ExecutionProofState::at_entry(
        ExecutionState::new(),
        ExecutionFrontier::default(),
        RecordedStates::default(),
        SurfacePropositionMap::default(),
        PersistentSequence::default(),
    )
}

#[test]
fn generated_load_source_events_are_idempotent_and_tombstone_conflicts() {
    let mut execution = generated_load_source_execution();
    let first = generated_load_source_event_fixture(70_001, 1, 0);
    let same = first.clone();
    let different_source = generated_load_source_event_fixture(70_001, 2, 0);
    let different_binding = generated_load_source_event_fixture(70_001, 1, 1);

    execution
        .presentation
        .record_generated_load_source_events(&[first.clone(), same]);
    assert_eq!(
        execution
            .presentation
            .generated_load_source_resolutions
            .len(),
        1
    );
    assert_eq!(execution.presentation.generated_load_source_events.len(), 1);
    assert!(matches!(
        execution
            .presentation
            .generated_load_source_resolutions
            .get(&Variable(70_001)),
        Some(crate::kernel::GeneratedLoadSourceResolution::Unique(event)) if event == &first
    ));

    // Either a different source occurrence or a different exact producer
    // binding poisons the variable permanently.
    execution
        .presentation
        .record_generated_load_source_events(&[different_source]);
    assert!(matches!(
        execution
            .presentation
            .generated_load_source_resolutions
            .get(&Variable(70_001)),
        Some(crate::kernel::GeneratedLoadSourceResolution::Ambiguous {
            variable
        }) if *variable == Variable(70_001)
    ));
    assert_eq!(execution.presentation.generated_load_source_events.len(), 2);
    execution
        .presentation
        .record_generated_load_source_events(&[different_binding, first]);
    assert_eq!(
        execution.presentation.generated_load_source_events.len(),
        2,
        "a tombstone must not be reopened or grow with ignored observations"
    );
}

#[test]
fn generated_load_source_event_rejects_ambiguous_binding_input() {
    let source = crate::kernel::LoadSourceId {
        owner: crate::kernel::LoadSourceOwnerId {
            source_unit: std::sync::Arc::from("source.c"),
            function: std::sync::Arc::from("load"),
        },
        occurrence: 1,
        reference_access: None,
    };
    assert!(
        crate::kernel::GeneratedLoadSourceEvent::new(
            source,
            crate::kernel::GeneratedLoadBinding::Ambiguous {
                variable: Variable(70_004),
            },
        )
        .is_none()
    );
}

#[test]
fn generated_load_source_event_forks_merge_by_suffix_without_cross_path_leaks() {
    let base = generated_load_source_execution();
    let first = generated_load_source_event_fixture(70_002, 1, 0);
    let second = generated_load_source_event_fixture(70_002, 2, 0);
    let other_variable = generated_load_source_event_fixture(70_003, 1, 0);

    let mut then_arm = base.clone();
    then_arm
        .presentation
        .record_generated_load_source_events(std::slice::from_ref(&first));
    let mut else_arm = base.clone();
    else_arm
        .presentation
        .record_generated_load_source_events(std::slice::from_ref(&first));

    let mut same_join = base.clone();
    let then_suffix = then_arm
        .presentation
        .generated_load_source_events
        .suffix_since(&base.presentation.generated_load_source_events)
        .expect("then arm must descend from the split root");
    same_join
        .presentation
        .record_generated_load_source_events(&then_suffix);
    let else_suffix = else_arm
        .presentation
        .generated_load_source_events
        .suffix_since(&base.presentation.generated_load_source_events)
        .expect("else arm must descend from the split root");
    same_join
        .presentation
        .record_generated_load_source_events(&else_suffix);
    assert_eq!(
        same_join.presentation.generated_load_source_events.len(),
        1,
        "the same event from both arms is one idempotent observation"
    );
    assert!(matches!(
        same_join
            .presentation
            .generated_load_source_resolutions
            .get(&Variable(70_002)),
        Some(crate::kernel::GeneratedLoadSourceResolution::Unique(event)) if event == &first
    ));

    let mut conflicting_arm = base.clone();
    conflicting_arm
        .presentation
        .record_generated_load_source_events(std::slice::from_ref(&second));
    let mut conflict_join = base.clone();
    conflict_join
        .presentation
        .record_generated_load_source_events(&then_suffix);
    let conflicting_suffix = conflicting_arm
        .presentation
        .generated_load_source_events
        .suffix_since(&base.presentation.generated_load_source_events)
        .expect("conflicting arm must descend from the split root");
    conflict_join
        .presentation
        .record_generated_load_source_events(&conflicting_suffix);
    assert!(matches!(
        conflict_join
            .presentation
            .generated_load_source_resolutions
            .get(&Variable(70_002)),
        Some(crate::kernel::GeneratedLoadSourceResolution::Ambiguous {
            variable
        }) if *variable == Variable(70_002)
    ));

    // A sibling's event is not visible from the root or an unrelated key.
    let mut unrelated_arm = base.clone();
    unrelated_arm
        .presentation
        .record_generated_load_source_events(std::slice::from_ref(&other_variable));
    assert!(base.presentation.generated_load_source_events.is_empty());
    assert!(
        then_arm
            .presentation
            .generated_load_source_resolutions
            .get(&Variable(70_003))
            .is_none()
    );
    assert!(matches!(
        unrelated_arm
            .presentation
            .generated_load_source_resolutions
            .get(&Variable(70_003)),
        Some(crate::kernel::GeneratedLoadSourceResolution::Unique(event)) if event == &other_variable
    ));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn nonempty_execution_branch_retains_checked_arm_steps_at_the_join() {
    let click_file = crate::surface::parse(
        r#"
            theorem int32_reflexive(value: int32) {
                ensures value == value by { close(); }
            }

            int32 constant(int32 x) {
                ensures returns_one: result == 1 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function(
        "int32 constant(int32 x) { if (x < 0) { x = 1; } else { x = 1; } return x; }",
    )
    .expect("test C branch should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(70_000)),
    ))];
    let application = TheoremApplication {
        name: "int32_reflexive".to_string(),
        arguments: vec![SyntaxTerm::ProgramExpression(arguments[0].clone())],
    };
    let reflexive = SyntaxProposition::Comparison {
        left: application.arguments[0].clone(),
        operator: ComparisonOperator::Equal,
        right: application.arguments[0].clone(),
    };
    let missing_application = TheoremApplication {
        name: "missing".to_string(),
        arguments: application.arguments.clone(),
    };
    let function_environment = ExecutionEnvironment::new();
    let mut allocation_samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    for size in LOCAL_PROOF_FACT_SIZES {
        let frontier = ExecutionFrontier {
            next_statement_index: 0,
            ..ExecutionFrontier::default()
        };
        let root = Proof::for_execution_frontier(
            "nonempty branch proof",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "constant".to_string(),
                    claim: ContractProofClaim::Grouped,
                }),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open two sibling arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("else assignment should check");
        let overshoot_step = ProofStep::Step;
        let then_arm = branches
            .focus_split_arm(&record, true)
            .expect("the then sibling stays open until the join");
        let Err(overshoot) = then_arm.driver().apply_step(overshoot_step) else {
            panic!("an arm must not consume the shared return continuation");
        };
        assert!(
            overshoot
                .message()
                .contains("arm of `branch` must stop at the shared continuation"),
            "{overshoot:?}"
        );
        let before = fact_node_allocations();
        let joined = branches
            .join_focused_execution_branch(&record)
            .expect("identical checked assignment arms should rejoin");
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Branch {
                ensuring: None,
                then_proof,
                else_proof,
            }] if matches!(then_proof.steps(), [ProofStep::Step])
                && matches!(else_proof.steps(), [ProofStep::Step])
        ));
        if size == 16 {
            assert!(
                apply_using(&joined, &missing_application, Vec::new()).is_none(),
                "a missing theorem must not manufacture a descendant"
            );
            assert!(matches!(
                joined.certificate().steps(),
                [ProofStep::Branch { .. }]
            ));
        }
        let applied = apply_using(&joined, &application, Vec::new())
            .expect("the reflexive theorem should produce a checked descendant");
        assert!(matches!(
            applied.certificate().steps(),
            [
                ProofStep::Branch { .. },
                ProofStep::ApplyTheoremUsing {
                    application: retained,
                    premises,
                },
            ] if retained == &application && premises.is_empty()
        ));
        let scope = applied
            .driver()
            .open_have(reflexive.clone())
            .expect("the joined proof should open a common nested proposition");
        // The nested proposition goal borrows the frontier's execution
        // state by identity: its path-local lowering context is
        // shared, never cloned, and can never republish a frontier.
        assert!(Arc::ptr_eq(
            scope
                .body
                .branch_execution()
                .expect("the nested goal borrows its lowering context"),
            applied
                .branch_execution()
                .expect("the joined frontier owns its state"),
        ));
        let refined = scope
            .driver()
            .apply_step(ProofStep::Known)
            .expect("the theorem conclusion should close the nested proposition")
            .join()
            .expect("the completed nested proposition should rejoin its root Proof");
        assert!(matches!(
            refined.certificate().steps(),
            [
                ProofStep::Branch { .. },
                ProofStep::ApplyTheoremUsing { .. },
                ProofStep::Have {
                    proposition,
                    proof,
                },
            ] if proposition == &reflexive
                && proof.steps() == [ProofStep::Known]
        ));
        let completed = refined
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the joined continuation should execute its return");
        assert!(
            completed
                .execution()
                .expect("completed proof retains execution state")
                .core
                .frontier
                .is_at_function_exit()
        );
        allocation_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            completed.certificate().steps(),
            [
                ProofStep::Branch { .. },
                ProofStep::ApplyTheoremUsing { .. },
                ProofStep::Have { .. },
                ProofStep::Step,
            ]
        ));

        // The in-`Proof` execution join: an arm still at branch entry
        // has not reached the shared continuation, a foreign split's
        // record fails marker identity, and the genuine join partitions
        // the interleaved sibling steps by attribution and resumes the
        // parent obligation under its original id.
        let parent_id = root.focused_branch_id();
        let (split_proof, record) = root
            .split_focused_execution_branch()
            .expect("the symbolic condition should split in-proof");
        let sibling_ids: Vec<BranchId> = split_proof.branches().collect();
        assert_eq!(sibling_ids.len(), 2);
        let premature = split_proof
            .join_focused_execution_branch(&record)
            .err()
            .expect("arms at branch entry must not join");
        assert!(
            premature
                .message()
                .contains("has not reached its shared continuation"),
            "{premature:?}"
        );
        let then_stepped = split_proof
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the then sibling advances in place");
        let both_stepped = then_stepped
            .focus_branch(sibling_ids[1])
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the else sibling advances in place");
        let (_, foreign_record) = root
            .split_focused_execution_branch()
            .expect("a second split of the same root should open both arms");
        assert_eq!(foreign_record.arm_branches, record.arm_branches);
        let foreign = both_stepped
            .join_focused_execution_branch(&foreign_record)
            .err()
            .expect("a foreign split record must fail marker identity");
        assert!(
            foreign.message().contains("did not pass through split"),
            "{foreign:?}"
        );
        let sibling_joined = both_stepped
            .join_focused_execution_branch(&record)
            .expect("both siblings reached the shared continuation");
        assert_eq!(sibling_joined.focused_branch_id(), parent_id);
        let continuation_ids: Vec<BranchId> = sibling_joined.branches().collect();
        assert_eq!(continuation_ids, [parent_id]);
        assert!(matches!(
            sibling_joined.certificate().steps(),
            [ProofStep::Branch {
                ensuring: None,
                then_proof,
                else_proof,
            }] if matches!(then_proof.steps(), [ProofStep::Step])
                && matches!(else_proof.steps(), [ProofStep::Step])
        ));
        let sibling_completed = sibling_joined
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the joined sibling frontier should execute its return");
        assert!(
            sibling_completed
                .execution()
                .expect("completed sibling join retains execution")
                .core
                .frontier
                .is_at_function_exit()
        );
        // The failed foreign join left the sibling state untouched.
        assert!(
            both_stepped
                .state
                .open_branches()
                .get(sibling_ids[0])
                .is_some()
        );
        assert!(
            both_stepped
                .state
                .open_branches()
                .get(sibling_ids[1])
                .is_some()
        );
    }
    let (_, base_height, base_allocations) = allocation_samples[0];
    for (size, height, allocations) in allocation_samples {
        let allocation_bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= allocation_bound,
            "size {size} branch, theorem, have, common return, and frame allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn branch_interface_is_checked_per_arm_and_scales_with_its_delta() {
    let click_file = crate::surface::parse(
        r#"
            abstract resource marker();
            abstract resource permit();

            resource ready() {
                owns permit();
            }

            int32 nonnegative(int32 x) {
                ensures nonnegative_result: result >= 0 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function(
        "int32 nonnegative(int32 x) { if (x < 0) { x = 1; } else { x = 2; } return x; }",
    )
    .expect("test interface branch should parse");
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let function = parsed_function
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
            )
            .expect("the ready resource definition should lower"),
        );
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(72_000)),
    ))];
    let function_environment = ExecutionEnvironment::new();
    let variable = |name: &str| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name.to_string()).into()))
    };
    let value = |constant| SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(constant)));
    let nonnegative = SyntaxProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::GreaterEqual,
        right: value(0),
    };
    let negative = SyntaxProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::LessThan,
        right: value(0),
    };
    let make_root = |size: u32, state: ExecutionState| {
        let frontier = ExecutionFrontier {
            next_statement_index: 0,
            ..ExecutionFrontier::default()
        };
        Proof::for_execution_frontier(
            "branch interface proof",
            0,
            ExecutionProofState::at_entry(
                state,
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        )
    };

    let mut samples = Vec::new();
    for size in LOCAL_PROOF_FACT_SIZES {
        let root = make_root(size, ExecutionState::new());
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open both interface arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("else assignment should check");
        let before = fact_node_allocations();
        let joined = branches
            .join_focused_execution_interface(
                &record,
                vec![ProofAssertion::Fact(nonnegative.clone())],
            )
            .expect("both assignments should establish the interface");
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Branch {
                ensuring: Some(assertions),
                then_proof,
                else_proof,
            }] if assertions == std::slice::from_ref(&ProofAssertion::Fact(nonnegative.clone()))
                && matches!(then_proof.steps(), [ProofStep::Step])
                && matches!(else_proof.steps(), [ProofStep::Step])
        ));
        assert!(
            joined
                .added_facts()
                .iter()
                .all(|fact| !(0..size).any(|index| *fact == indexed_fact(index))),
            "the interface node must not copy ambient facts into its delta"
        );
        let completed = joined
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the abstract joined frontier should execute its return");
        assert!(
            completed
                .execution()
                .expect("completed interface proof retains execution")
                .core
                .frontier
                .is_at_function_exit()
        );
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 48 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} branch interface allocated {allocations} persistent nodes (bound {bound})"
        );
    }

    let root = make_root(16, ExecutionState::new());
    let retained = root.clone();
    let (split, record) = root
        .split_focused_execution_branch()
        .expect("rejection test should open both arms");
    let error = split
        .focus_split_arm(&record, true)
        .expect("the then sibling is open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("then assignment should check")
        .focus_split_arm(&record, false)
        .expect("the else sibling is open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("else assignment should check")
        .join_focused_execution_interface(&record, vec![ProofAssertion::Fact(negative)])
        .err()
        .expect("each arm must independently establish the interface");
    assert!(error.message().contains("did not establish fact"));
    assert!(root.state.shares_state_with(&retained.state));
    assert!(root.certificate().steps().is_empty());

    // The container's spliced-arm identity regression is superseded by
    // the split-identity regression below: a foreign split of the same
    // root collides numerically and is rejected by marker identity.

    // The in-`Proof` execution split: both feasible arms become sibling
    // frontier goals in one state, each advancing by focus on one
    // lineage, with `introduced_since` recovering each arm's fact delta
    // from its recorded split-time base even after interleaved steps.
    let root = make_root(16, ExecutionState::new());
    let (split_proof, record) = root
        .split_focused_execution_branch()
        .expect("the symbolic condition should split in-proof");
    let sibling_ids: Vec<BranchId> = split_proof.branches().collect();
    assert_eq!(sibling_ids.len(), 2);
    assert_eq!(
        record.arm_branches,
        [Some(sibling_ids[0]), Some(sibling_ids[1])]
    );
    assert!(record.condition_theorems.iter().all(Option::is_some));
    let then_stepped = split_proof
        .driver()
        .apply_step(ProofStep::Step)
        .expect("the then sibling advances in place");
    assert!(
        then_stepped
            .state
            .open_branches()
            .get(sibling_ids[1])
            .is_some()
    );
    let both_stepped = then_stepped
        .focus_branch(sibling_ids[1])
        .expect("the else sibling is open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("the else sibling advances in place");
    for (index, id) in sibling_ids.iter().enumerate() {
        let arm = both_stepped
            .focus_branch(*id)
            .expect("both siblings remain open");
        let base = record.base_facts[index]
            .as_ref()
            .expect("both feasible arms recorded their bases");
        assert!(
            arm.facts().introduced_since(base).is_some(),
            "arm {index} must still descend from its recorded split base"
        );
    }
    assert!(root.certificate().steps().is_empty());
    assert_eq!(root.branches().count(), 1);

    // The in-`Proof` interface join: both siblings advance on one
    // lineage with distinct concrete states, abstract through the same
    // explicit interface, and resume the parent obligation with the
    // agreed abstract continuation.
    let parent_id = root.focused_branch_id();
    let interface = vec![ProofAssertion::Fact(nonnegative.clone())];
    let joined = both_stepped
        .join_focused_execution_interface(&record, interface.clone())
        .expect("both siblings should abstract through the shared interface");
    assert_eq!(joined.focused_branch_id(), parent_id);
    let joined_ids: Vec<BranchId> = joined.branches().collect();
    assert_eq!(joined_ids, [parent_id]);
    assert!(matches!(
        joined.certificate().steps(),
        [ProofStep::Branch {
            ensuring: Some(retained),
            then_proof,
            else_proof,
        }] if retained == interface.as_slice()
            && matches!(then_proof.steps(), [ProofStep::Step])
            && matches!(else_proof.steps(), [ProofStep::Step])
    ));
    let completed = joined
        .driver()
        .apply_step(ProofStep::Step)
        .expect("the abstract sibling continuation should execute its return");
    assert!(
        completed
            .execution()
            .expect("the completed sibling interface proof retains execution")
            .core
            .frontier
            .is_at_function_exit()
    );
    // A failed sibling interface join is transactional.
    let negative_retained = SyntaxProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::LessThan,
        right: value(0),
    };
    let failed = both_stepped
        .join_focused_execution_interface(
            &record,
            vec![ProofAssertion::Fact(negative_retained.clone())],
        )
        .err()
        .expect("each sibling must independently establish the interface");
    assert!(
        failed.message().contains("did not establish fact"),
        "{failed:?}"
    );
    assert!(
        both_stepped
            .state
            .open_branches()
            .get(sibling_ids[0])
            .is_some()
    );
    assert!(
        both_stepped
            .state
            .open_branches()
            .get(sibling_ids[1])
            .is_some()
    );

    let marker_clause = ResourceClause::Declared {
        type_schema: None,
        resource_type_arguments: Vec::new(),
        resource_arguments: Vec::new(),
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Token,
        name: "marker".to_string(),
        arguments: Vec::new(),
        parameter_types: Vec::new(),
    };
    let marker_fact = ResourceFact::own_token("marker".to_string(), Vec::new());
    let mut ownership_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
            }))
            .unchecked_with_fact(marker_fact.clone());
        let (split, record) = make_root(16, ExecutionState::new().with_resource_context(resources))
            .split_focused_execution_branch()
            .expect("the owned-interface condition should expose both arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("owned-interface then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("owned-interface else assignment should check");
        let assertions = vec![ProofAssertion::Resource(marker_clause.clone())];
        let before = fact_node_allocations();
        let joined = branches
            .join_focused_execution_interface(&record, assertions.clone())
            .expect("an exact unchanged owned resource should rejoin");
        ownership_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Branch {
                ensuring: Some(retained),
                ..
            }] if retained == assertions.as_slice()
        ));
        joined
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the exact owned interface should retain its return frontier");
    }
    let (_, base_height, base_allocations) = ownership_samples[0];
    for (size, height, allocations) in ownership_samples {
        let bound = base_allocations + 64 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} exact owned interface allocated {allocations} persistent nodes (bound {bound})"
        );
    }

    let ready_clause = ResourceClause::Declared {
        type_schema: None,
        resource_type_arguments: Vec::new(),
        resource_arguments: Vec::new(),
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Composite,
        name: "ready".to_string(),
        arguments: Vec::new(),
        parameter_types: Vec::new(),
    };
    let permit_fact = ResourceFact::own_token("permit".to_string(), Vec::new());
    let mut changed_state_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
            }))
            .unchecked_with_fact(permit_fact.clone());
        let (split, record) = make_root(16, ExecutionState::new().with_resource_context(resources))
            .split_focused_execution_branch()
            .expect("the transformed-interface condition should expose both arms");
        assert!(
            record.supports_interface_branch(),
            "a structural preflight must not require a resource folded later in the arms"
        );
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("transformed-interface then assignment should check")
            .driver()
            .apply_step(ProofStep::FoldResource(ready_clause.clone()))
            .expect("then arm should fold its ready resource")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("transformed-interface else assignment should check")
            .driver()
            .apply_step(ProofStep::FoldResource(ready_clause.clone()))
            .expect("else arm should independently fold its ready resource");
        let arm_execution = |take_then: bool| {
            let id = record.arm_id(take_then).expect("both arms are feasible");
            let Some(branch) = branches.state.open_branches().get(id) else {
                panic!("both arms should remain open execution frontiers");
            };
            let Obligation::Frontier(_) = &branch.obligation else {
                panic!("both arms should remain open execution frontiers");
            };
            branch
                .state
                .execution
                .as_deref()
                .expect("both arms should retain execution")
        };
        assert!(
            !arm_execution(true)
                .core
                .state
                .resources()
                .shares_storage_with(arm_execution(false).core.state.resources())
        );

        let assertions = vec![ProofAssertion::Resource(ready_clause.clone())];
        let before = fact_node_allocations();
        let joined = branches
            .join_focused_execution_interface(&record, assertions)
            .expect("independently folded resource states should rejoin");
        changed_state_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Branch {
                then_proof,
                else_proof,
                ..
            }] if matches!(
                then_proof.steps(),
                [ProofStep::Step, ProofStep::FoldResource(_)]
            ) && matches!(
                else_proof.steps(),
                [ProofStep::Step, ProofStep::FoldResource(_)]
            )
        ));
        let ready_fact = ResourceFact::own_composite("ready".to_string(), Vec::new());
        let permit_view = ResourceFact::view_token("permit".to_string(), Vec::new());
        let contains = Proposition::ResourceContains {
            parent: Box::new(ready_fact.resource().clone()),
            child: Box::new(permit_fact.resource().clone()),
        };
        let joined_execution = joined
            .execution()
            .expect("the transformed interface should retain execution");
        assert!(
            joined_execution
                .core
                .state
                .resources()
                .contains_exact_representation(&ready_fact)
        );
        assert!(
            !joined_execution
                .core
                .state
                .resources()
                .contains_exact_representation(&permit_view)
                && !joined.facts().contains(&contains),
            "exporting a folded composite must not observe its body"
        );
        let continuation = if size == 16 {
            let observed = joined
                .driver()
                .apply_step(ProofStep::ObserveResource(ready_clause.clone()))
                .expect("explicit observation should project one interface resource layer");
            assert!(
                observed
                    .execution()
                    .expect("observation retains execution")
                    .core
                    .state
                    .resources()
                    .contains_exact_representation(&permit_view)
                    && observed.facts().contains(&contains),
                "the explicit observation should add the immediate child view and containment"
            );
            observed
        } else {
            joined
        };
        continuation
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the transformed owned interface should retain its return frontier");
    }
    let (_, base_height, base_allocations) = changed_state_samples[0];
    for (size, height, allocations) in changed_state_samples {
        let bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} changed-resource Proof join allocated {allocations} persistent nodes (bound {bound})"
        );
    }

    let represented_quantity = ResourceFact::own_quantity(
        Resource::Token {
            name: "marker".to_string(),
            arguments: Vec::new().into(),
        },
        OldMachineTerm::constant(2),
    );
    let mut normalized_quantity_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_token(format!("quantity_unrelated_{index}"), Vec::new())
            }))
            .unchecked_with_fact(represented_quantity.clone());
        let (split, record) = make_root(16, ExecutionState::new().with_resource_context(resources))
            .split_focused_execution_branch()
            .expect("the normalized-ownership probe should expose both arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("normalized-ownership then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("normalized-ownership else assignment should check");
        let before = fact_node_allocations();
        let normalized_join = branches
            .join_focused_execution_interface(
                &record,
                vec![ProofAssertion::Resource(marker_clause.clone())],
            )
            .expect("an entailed quantity representation should be consumed and restored once");
        normalized_quantity_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(
            normalized_join
                .execution()
                .expect("normalized interface retains execution")
                .core
                .state
                .resources()
                .contains_exact_representation(&represented_quantity),
            "the common quantity must not be duplicated or weakened by its unit interface"
        );
    }
    let (_, base_height, base_allocations) = normalized_quantity_samples[0];
    for (size, height, allocations) in normalized_quantity_samples {
        let bound = base_allocations + 160 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} normalized quantity interface allocated {allocations} persistent nodes (bound {bound})"
        );
    }

    let invalid_root = make_root(
        16,
        ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_fact(represented_quantity),
        ),
    );
    let (invalid_split, invalid_record) = invalid_root
        .split_focused_execution_branch()
        .expect("the rejected quantity probe should expose both arms");
    let invalid_branches = invalid_split
        .focus_split_arm(&invalid_record, true)
        .expect("the then sibling is open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("rejected quantity then assignment should check")
        .focus_split_arm(&invalid_record, false)
        .expect("the else sibling is open")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("rejected quantity else assignment should check");
    let quantity_three = ResourceClause::Quantified {
        quantity: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(3))),
        resource: Box::new(marker_clause),
    };
    assert!(
        invalid_branches
            .join_focused_execution_interface(
                &invalid_record,
                vec![ProofAssertion::Resource(quantity_three)],
            )
            .is_err(),
        "an interface may not manufacture a quantity larger than either arm owns"
    );
    assert!(invalid_root.certificate().steps().is_empty());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn nested_end_of_arm_interface_derives_its_enclosing_continuation() {
    let click_file = crate::surface::parse(
        r#"
            int32 nested(int32 x, int32 flag) {
                ensures nonnegative_result: result >= 0 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function(
        "int32 nested(int32 x, int32 flag) { if (flag != 0) { if (x < 0) { x = 1; } else { x = 2; } } else { x = 3; } return x; }",
    )
    .expect("test nested interface branch should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            73_000,
        )))),
        ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            73_001,
        )))),
    ];
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let nonnegative = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("x".to_string()).into())),
        operator: ComparisonOperator::GreaterEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let make_root = |size: u32| {
        let frontier = ExecutionFrontier {
            next_statement_index: 0,
            ..ExecutionFrontier::default()
        };
        Proof::for_execution_frontier(
            "nested branch interface proof",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        )
    };

    let mut samples = Vec::new();
    for size in LOCAL_PROOF_FACT_SIZES {
        let (outer_split, outer_record) = make_root(size)
            .split_focused_execution_branch()
            .expect("outer symbolic condition should expose both arms");
        let outer_then = outer_split
            .focus_split_arm(&outer_record, true)
            .expect("outer then arm should be feasible");
        let (nested_split, nested_record) = outer_then
            .split_focused_execution_branch()
            .expect("nested symbolic condition should expose both arms");
        let nested = nested_split
            .focus_split_arm(&nested_record, true)
            .expect("the nested then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("nested then assignment should check")
            .focus_split_arm(&nested_record, false)
            .expect("the nested else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("nested else assignment should check");
        let nested_statement = nested_record.statement_index;
        assert!(nested_record.continuation_remaining.is_none());

        let before = fact_node_allocations();
        let joined = nested
            .join_focused_execution_interface(
                &nested_record,
                vec![ProofAssertion::Fact(nonnegative.clone())],
            )
            .expect("nested end-of-arm interface should reach the outer continuation");
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        let execution = joined
            .execution()
            .expect("nested join should retain execution");
        assert!(
            execution
                .presentation
                .recorded_states
                .get(&ProgramPointRef {
                    region: CodeRegionRef::Region(nested_statement),
                    kind: ProgramPointKind::Exit,
                })
                .is_some()
        );
        assert!(
            execution.core.frontier.is_at_region_boundary(),
            "the nested join ends the outer arm's own region"
        );
        let joined = joined
            .continue_arm_into_parent_frontier(&outer_record)
            .expect("the outer split record derives the enclosing continuation");
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Branch {
                ensuring: Some(assertions),
                ..
            }] if assertions == std::slice::from_ref(&ProofAssertion::Fact(nonnegative.clone()))
        ));
        let completed = joined
            .driver()
            .apply_step(ProofStep::Step)
            .expect("derived enclosing continuation should execute the return");
        assert!(
            completed
                .execution()
                .expect("completed nested proof retains execution")
                .core
                .frontier
                .is_at_function_exit()
        );
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 64 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} nested branch interface allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
fn mixed_call_outcomes_use_the_enclosing_branch_continuation() {
    use crate::kernel::{
        bool_value, program_call, program_parameter, program_return, program_skip,
        program_try_catch_int32,
    };

    let click_file = crate::surface::parse(
        r#"int32 caller(bool construct, bool should_throw) {
            ensures result == result by {
                branch {
                    true => {
                        outcomes {
                            returned => { }
                            threw => { step_until(function.exit); }
                        }
                    }
                    false => { }
                }
                step();
            }
        }"#,
    )
    .expect("minimal caller contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let helper = program_function(
        ProgramType::Int32,
        "helper",
        vec![program_parameter("should_throw", ProgramType::Bool)],
        program_if(
            crate::kernel::program_expression::variable("should_throw"),
            ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
            program_return(crate::kernel::program_expression::int32_literal(5)),
        ),
    )
    .with_int32_exceptional_outcome()
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let helper_rule = crate::kernel::program_recursive_function_contract_hypothesis(helper.clone())
        .expect("the checked helper should have a modular rule");
    let function_environment = ExecutionEnvironment::new()
        .with_function(helper)
        .with_verified_function_rule(helper_rule);

    let body = program_seq(
        program_if(
            crate::kernel::program_expression::variable("construct"),
            program_try_catch_int32(
                program_call(
                    "helper",
                    vec![crate::kernel::program_expression::variable("should_throw")],
                ),
                "caught",
                program_return(crate::kernel::program_expression::variable("caught")),
            ),
            program_skip(),
        ),
        program_return(crate::kernel::program_expression::int32_literal(5)),
    );
    let function = program_function(
        ProgramType::Int32,
        "caller",
        vec![
            program_parameter("construct", ProgramType::Bool),
            program_parameter("should_throw", ProgramType::Bool),
        ],
        body,
    );
    let parsed_function = crate::languages::interface::ImportedFunction::external(
        InterfaceType::Int32,
        "caller".into(),
        vec![
            crate::languages::interface::ImportedParameter::new(
                InterfaceType::Bool,
                "construct".into(),
                None,
            ),
            crate::languages::interface::ImportedParameter::new(
                InterfaceType::Bool,
                "should_throw".into(),
                None,
            ),
        ],
    )
    .with_prelowered_kernel_function(function.clone());
    let arguments = vec![
        ProgramExpression::Value(bool_value(OldMachineTerm::Variable(Variable(80_011)))),
        ProgramExpression::Value(bool_value(OldMachineTerm::Variable(Variable(80_012)))),
    ];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let resource_environment = ResourceEnvironment::new(&[]);
    let constants = ExecutionProofConstants {
        source_layout: SourceExecutionLayout::for_function(&parsed_function).unwrap(),
        ..ExecutionProofConstants::default()
    };
    let root = Proof::for_execution_frontier(
        "mixed call outcomes",
        0,
        ExecutionProofState::at_entry(
            ExecutionState::new().with_population_creation_tracking(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![],
        constants.clone(),
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    let (outer, outer_record) = root
        .split_focused_execution_branch()
        .expect("conditional should split");
    let (outcomes, call_record) = outer
        .focus_split_arm(&outer_record, true)
        .unwrap()
        .split_focused_call_outcomes([None, None])
        .expect("call split should be checked")
        .expect("modular helper has normal and throwing outcomes");
    let returned = outcomes.focus_split_arm(&call_record, true).unwrap();
    assert!(returned.is_at_region_boundary());
    let threw = returned
        .focus_split_arm(&call_record, false)
        .unwrap()
        .driver()
        .apply_step(ProofStep::Step)
        .expect("the caught arm returns");
    assert!(threw.is_at_function_exit());
    let returned = threw
        .focus_split_arm(&call_record, true)
        .unwrap()
        .continue_arm_into_parent_frontier(&outer_record)
        .expect("the outer branch record owns the final return")
        .driver()
        .apply_step(ProofStep::Step)
        .expect("the final return should complete the normal arm");
    assert!(returned.is_at_function_exit());
    let joined = returned
        .join_focused_call_outcomes_terminal(&call_record)
        .expect("both outcomes have certified terminal paths");
    assert!(joined.is_at_function_exit());

    let tactics = function_block.ensures()[0].proof().tactics().unwrap();
    let program = crate::surface::proof::build_internal_proof(tactics, "mixed call outcomes")
        .expect("explicit branch proof should build");
    let checked = crate::surface::proof::checked_drivers::try_check_structural_function_proof(
        root.execution().unwrap(),
        &PureFactList::default(),
        &constants,
        &program,
        None,
        None,
        function_block,
        &parsed_function,
        "mixed call outcomes",
        &function_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &resource_environment,
        &theorem_environment,
        &function,
        &arguments,
    )
    .expect("the checked structural driver should not error")
    .expect("the checked structural driver should retain this proof");
    assert!(checked.is_at_function_exit());
    let (outcomes, ids, _) = checked
        .split_function_outcomes()
        .expect("the outer join should expose all terminal paths");
    let mut call_edges = ids
        .into_iter()
        .map(|id| {
            outcomes
                .focus_branch(id)
                .unwrap()
                .checked_call_returned(0)
                .ok()
        })
        .collect::<Vec<_>>();
    call_edges.sort_unstable();
    assert_eq!(call_edges, [None, Some(false), Some(true)]);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn decided_execution_branch_retains_one_checked_path_without_copying_context() {
    let click_file = crate::surface::parse(
        r#"
            int32 selected(int32 x) {
                ensures returns_one: result == 1 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function(
        "int32 selected(int32 x) { if (x < 0) { x = 1; } else { x = 2; } return x; }",
    )
    .expect("test decided C branch should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(75_000)),
    ))];
    let function_environment = ExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let make_root = |facts: Vec<Proposition>| {
        let frontier = ExecutionFrontier {
            next_statement_index: 0,
            ..ExecutionFrontier::default()
        };
        Proof::for_execution_frontier(
            "decided branch proof",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            facts,
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        )
    };

    let (_, probe) = make_root(Vec::new())
        .split_focused_execution_branch()
        .expect("the unconstrained condition should expose both arms");
    let selecting_fact = probe.path_facts[0]
        .as_ref()
        .expect("the then arm should be feasible")
        .first()
        .expect("the then arm should retain its condition fact")
        .clone();
    let rejecting_fact = probe.path_facts[1]
        .as_ref()
        .expect("the else arm should be feasible")
        .first()
        .expect("the else arm should retain its condition fact")
        .clone();
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(selecting_fact.clone());
        let root = make_root(facts);
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("the selecting fact should make exactly one arm feasible");
        assert_eq!(record.sole_feasible_arm(), Some(true));
        assert!(record.arm_id(false).is_none());
        let advanced = crate::kernel::search::ProofSearch::try_statement_step(
            &(split
                .focus_split_arm(&record, true)
                .expect("the sole sibling is open")),
        )
        .expect("smart selection should remain bounded")
        .expect("the assignment should produce a checked simple successor");
        let before = fact_node_allocations();
        let decided = advanced
            .finish_focused_execution_decided(&record)
            .expect("the sole checked arm should form a decided path");
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            decided.certificate().steps(),
            [ProofStep::If {
                then_proof,
                else_proof,
                ..
            }] if matches!(
                then_proof.steps(),
                [ProofStep::Step, ProofStep::Step]
            ) && else_proof.steps().is_empty()
        ));
        assert_eq!(
            decided
                .execution()
                .expect("decided path retains execution")
                .branch_path
                .len(),
            0
        );
        assert!(
            decided
                .added_facts()
                .iter()
                .all(|fact| !(0..size).any(|index| *fact == indexed_fact(index))),
            "the decided node delta must not copy unrelated ambient facts"
        );
        let completed = crate::kernel::search::ProofSearch::try_statement_step(&(decided))
            .expect("contextual return selection should remain bounded")
            .expect("the continuation return should check with retained branch facts");
        assert!(
            completed
                .execution()
                .expect("completed decided proof retains execution")
                .core
                .frontier
                .is_at_function_exit()
        );
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} decided branch allocated {allocations} persistent nodes (logarithmic bound {bound})"
        );
    }

    let (split, record) = make_root(vec![rejecting_fact])
        .split_focused_execution_branch()
        .expect("the rejecting fact should retain only the else arm");
    assert_eq!(record.sole_feasible_arm(), Some(false));
    let advanced = crate::kernel::search::ProofSearch::try_statement_step(
        &(split
            .focus_split_arm(&record, false)
            .expect("the sole else sibling is open")),
    )
    .expect("else-arm smart selection should remain bounded")
    .expect("the else assignment should produce a checked successor");
    let decided = advanced
        .finish_focused_execution_decided(&record)
        .expect("the sole else arm should form a decided path");
    let certificate = decided.certificate();
    assert!(
        matches!(
        certificate.steps(),
        [ProofStep::If {
            condition,
            then_proof,
            else_proof,
            ..
        }] if then_proof.steps().is_empty()
            && matches!(
                else_proof.steps(),
                [ProofStep::Step, ProofStep::Step]
            )
        ),
        "{certificate:#?}"
    );

    // The in-`Proof` decided finish: a split under the selecting fact
    // opens exactly one sibling goal; its steps splice under a logical
    // `If` with an empty contradictory arm, and the parent obligation
    // resumes under its original id. Two feasible siblings refuse the
    // decided finish.
    let root = make_root(vec![selecting_fact.clone()]);
    let parent_id = root.focused_branch_id();
    let (split_proof, record) = root
        .split_focused_execution_branch()
        .expect("the selecting fact should split to the sole then sibling");
    assert!(record.arm_branches[0].is_some() && record.arm_branches[1].is_none());
    assert_eq!(split_proof.branches().count(), 1);
    let advanced = crate::kernel::search::ProofSearch::try_statement_step(&(split_proof))
        .expect("sole-sibling selection should remain bounded")
        .expect("the assignment should produce a checked simple successor");
    let decided = advanced
        .finish_focused_execution_decided(&record)
        .expect("the sole checked sibling should form a decided path");
    assert_eq!(decided.focused_branch_id(), parent_id);
    let decided_ids: Vec<BranchId> = decided.branches().collect();
    assert_eq!(decided_ids, [parent_id]);
    assert!(matches!(
        decided.certificate().steps(),
        [ProofStep::If {
            then_proof,
            else_proof,
            ..
        }] if matches!(
            then_proof.steps(),
            [ProofStep::Step, ProofStep::Step]
        ) && else_proof.steps().is_empty()
    ));
    assert_eq!(
        decided
            .execution()
            .expect("the decided sibling path retains execution")
            .branch_path
            .len(),
        0
    );
    let completed = crate::kernel::search::ProofSearch::try_statement_step(&(decided))
        .expect("contextual return selection should remain bounded")
        .expect("the continuation return should check with retained branch facts");
    assert!(
        completed
            .execution()
            .expect("the completed decided sibling proof retains execution")
            .core
            .frontier
            .is_at_function_exit()
    );
    // The decided interface finish mirrors the plain decided finish
    // through the interface entrypoint: an explicit interface on the
    // sole sibling records `Branch { ensuring, .. }` with the empty
    // impossible arm and resumes the parent id.
    let root = make_root(vec![selecting_fact.clone()]);
    let parent_id = root.focused_branch_id();
    let (split_proof, record) = root
        .split_focused_execution_branch()
        .expect("the selecting fact should split to the sole then sibling");
    let advanced = crate::kernel::search::ProofSearch::try_statement_step(&(split_proof))
        .expect("sole-sibling selection should remain bounded")
        .expect("the assignment should produce a checked simple successor");
    let decided = advanced
        .join_focused_execution_interface(&record, Vec::new())
        .expect("the sole checked sibling should finish through the interface");
    assert_eq!(decided.focused_branch_id(), parent_id);
    let decided_ids: Vec<BranchId> = decided.branches().collect();
    assert_eq!(decided_ids, [parent_id]);
    assert!(matches!(
        decided.certificate().steps(),
        [ProofStep::Branch {
            ensuring: Some(retained),
            then_proof,
            else_proof,
        }] if retained.is_empty()
            && matches!(then_proof.steps(), [ProofStep::Step])
            && else_proof.steps().is_empty()
    ));

    let (undecided_proof, undecided_record) = make_root(Vec::new())
        .split_focused_execution_branch()
        .expect("the unconstrained condition should split to both siblings");
    let error = undecided_proof
        .finish_focused_execution_decided(&undecided_record)
        .err()
        .expect("two feasible siblings are not a decided path");
    assert!(
        error.message().contains("exactly one kernel-feasible arm"),
        "{error:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn terminal_execution_branch_retains_distinct_outcomes_as_a_logical_if() {
    let click_file = crate::surface::parse(
        r#"
            int32 choose(int32 x) {
                ensures returns_one_or_two: result == 1 or result == 2 by { close(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let parsed_function = syntax::parse_function(
        "int32 choose(int32 x) { if (x < 0) { return 1; } else { return 2; } }",
    )
    .expect("test terminal C branch should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(
        OldMachineTerm::Variable(Variable(80_000)),
    ))];
    let function_environment = ExecutionEnvironment::new();
    let mut allocation_samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut expected_outcome_fact_sizes = None;
    for size in [16_u32, 64, 256, 1024, 4096] {
        let frontier = ExecutionFrontier {
            next_statement_index: 0,
            ..ExecutionFrontier::default()
        };
        let root = Proof::for_execution_frontier(
            "terminal branch proof",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open two sibling arms");
        let advanced = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("then return should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("else return should check");
        assert!(advanced.split_arms_at_function_exit(&record));
        let arm_candidates = [true, false].map(|value| {
            let arm = advanced
                .focus_split_arm(&record, value)
                .expect("completed arm remains accessible");
            arm.execution()
                .unwrap()
                .core
                .frontier
                .execution()
                .unwrap()
                .paths()[0]
                .clone()
        });
        let before = fact_node_allocations();
        let joined = advanced
            .join_focused_execution_terminal(&record)
            .expect("two checked returns should form a terminal logical case split");
        allocation_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::If {
                condition,
                then_proof,
                else_proof,
                ..
            }] if matches!(
                then_proof.steps(),
                [ProofStep::Step, ProofStep::Step]
            ) && matches!(
                else_proof.steps(),
                [ProofStep::Step, ProofStep::Step]
            )
        ));
        assert!(root.certificate().steps().is_empty());
        let execution = joined
            .execution()
            .expect("terminal join should retain execution state");
        assert!(execution.core.frontier.is_at_function_exit());
        let outcome_paths = execution
            .core
            .frontier
            .execution()
            .expect("terminal join should retain outcomes")
            .paths();
        assert_eq!(outcome_paths.len(), 2);
        for (arm, retained) in arm_candidates.iter().zip(outcome_paths) {
            assert!(
                std::ptr::eq(arm.outcome(), retained.outcome()),
                "terminal joins retain the arm's outcome state without copying it"
            );
            assert!(
                std::ptr::eq(arm.obligations(), retained.obligations()),
                "terminal joins retain the arm's obligation payload"
            );
        }

        assert_eq!(
            execution.presentation.outcome_evidence.len(),
            outcome_paths.len(),
            "every terminal outcome must retain one atomic evidence record"
        );
        assert!(
            execution
                .presentation
                .outcome_evidence
                .iter()
                .all(|outcome_evidence| !outcome_evidence.branch_decisions.is_empty())
        );
        let outcome_fact_sizes = outcome_paths
            .iter()
            .map(|path| path.execution_facts().len())
            .collect::<Vec<_>>();
        if let Some(expected) = &expected_outcome_fact_sizes {
            assert_eq!(
                &outcome_fact_sizes, expected,
                "terminal outcome paths must not copy the growing ambient fact context"
            );
        } else {
            expected_outcome_fact_sizes = Some(outcome_fact_sizes);
        }
        assert_eq!(execution.presentation.branch_path.len(), 0);
        assert!(
            execution
                .presentation
                .outcome_evidence
                .iter()
                .all(|outcome_evidence| outcome_evidence.checked_leaf_facts.is_some())
        );
        let (outcomes, ids, _) = joined.split_function_outcomes().unwrap();
        assert_eq!(ids.len(), 2);
        // An unknown post-execution condition forks each outcome. Its
        // checked case delta extends that leaf, retaining its own guards
        // and cache authority rather than rebuilding unrelated records.
        let unknown = SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                OldMachineTerm::Variable(Variable(80_001)),
            ))),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                OldMachineTerm::constant(0),
            ))),
        };
        let forked = joined
            .driver()
            .split_outcome_paths(&DeferredPostExecutionTactic {
                lexical_bindings: None,
                tactic_index: 0,
                source_index: 0,
                reads_deferred_binding: false,
                tactic: PostExecutionTactic::If {
                    condition: unknown.clone(),
                    disjunction: false,
                    execution_route: None,
                    ensuring: None,
                    then_tactics: Default::default(),
                    else_tactics: Default::default(),
                },
            })
            .unwrap();
        let forked_execution = forked.execution().unwrap();
        let forked_paths = forked_execution.core.frontier.execution().unwrap().paths();
        assert_eq!(forked_paths.len(), 4);
        for (index, path) in forked_paths.iter().enumerate() {
            let outcome_evidence = forked_execution.evidence_for_outcome(index);
            let (candidate, facts, _) = outcome_evidence.checked_leaf_facts.as_deref().unwrap();
            assert!(candidate.shares_record_with(path));
            for fact in path.facts() {
                assert!(facts.contains(fact.proposition()));
                assert!(!facts.directly_conflicts_with(fact.proposition()));
            }
        }
        take_outcome_fact_reads();
        let (forked_goals, forked_ids, _) = forked.split_function_outcomes().unwrap();
        assert_eq!(take_outcome_fact_reads().0, 4);
        assert_eq!(forked_ids.len(), 4);
        for (path, id) in forked_paths.iter().zip(forked_ids) {
            let goal = forked_goals.focus_branch(id).unwrap();
            for fact in path.facts() {
                assert!(goal.facts().contains(fact.proposition()));
                assert!(!goal.facts().directly_conflicts_with(fact.proposition()));
            }
        }
        // A cache belongs to one exact immutable candidate. Swapping only
        // its marker forces the ordinary import, never sibling authority.
        let (mismatched_state, ()) = joined
            .state
            .clone()
            .edit_frontier_presentation(|presentation| {
                for (index, outcome_evidence) in
                    presentation.outcome_evidence.iter_mut().enumerate()
                {
                    Arc::make_mut(outcome_evidence.checked_leaf_facts.as_mut().unwrap()).0 =
                        outcome_paths[1 - index].clone();
                }
            })
            .unwrap_or_else(|_| panic!("the terminal frontier owns editable presentation"));
        let mut mismatched = joined.clone();
        mismatched.state = mismatched_state;
        take_outcome_fact_reads();
        let (_, mismatched_ids, _) = mismatched.split_function_outcomes().unwrap();
        let (reused, imported) = take_outcome_fact_reads();
        assert_eq!(mismatched_ids.len(), 2);
        assert_eq!(
            reused, 0,
            "a different record invalidates the context cache"
        );
        assert!(
            imported > 0,
            "incompatible caches retain ordinary path import"
        );

        for (path, id) in outcome_paths.iter().zip(&ids) {
            let goal = outcomes.focus_branch(*id).unwrap();
            for fact in path.facts() {
                assert!(
                    goal.facts().contains(fact.proposition()),
                    "a leaf keeps its checked guards"
                );
                assert!(
                    !goal.facts().directly_conflicts_with(fact.proposition()),
                    "opposite-arm facts must stay isolated"
                );
            }
        }
        // A new frontier premise selects compatible leaves without reading
        // their complete shared prefixes or admitting the opposite guard.
        let selected = outcome_paths[0]
            .facts()
            .iter()
            .find(|fact| matches!(fact.proposition(), Proposition::ConditionIs(_, _)))
            .expect("the symbolic branch retained its guard")
            .proposition()
            .clone();
        let mut narrowed = joined.clone();
        let mut narrowed_state = narrowed.state.clone().into_state();
        let narrowed_branches = narrowed_state.open_branches().with_facts_at(
            narrowed.focused_branch_id(),
            narrowed.facts().with_kernel_checked_fact(selected),
        );
        *narrowed_state.open_branches_mut() = narrowed_branches;
        narrowed.state = narrowed.state.with_state(narrowed_state);
        let (selected_outcomes, selected_ids, _) = narrowed.split_function_outcomes().unwrap();
        assert_eq!(selected_ids.len(), 1);
        assert_eq!(
            selected_outcomes
                .focus_branch(selected_ids[0])
                .unwrap()
                .outcome_result(),
            outcomes.focus_branch(ids[0]).unwrap().outcome_result()
        );

        // The in-`Proof` terminal join: both siblings return on their
        // own lineage and rejoin as a logical `If` whose outcome paths
        // stay separate, resuming the parent obligation at function
        // exit under its original id.
        let parent_id = root.focused_branch_id();
        let (split_proof, record) = root
            .split_focused_execution_branch()
            .expect("the symbolic condition should split in-proof");
        let sibling_ids: Vec<BranchId> = split_proof.branches().collect();
        assert_eq!(sibling_ids.len(), 2);
        let premature = split_proof
            .join_focused_execution_terminal(&record)
            .err()
            .expect("arms at branch entry have not completed");
        assert!(
            premature
                .message()
                .contains("has not completed at function exit"),
            "{premature:?}"
        );
        let both_returned = split_proof
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the then sibling returns in place")
            .focus_branch(sibling_ids[1])
            .expect("the else sibling is open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("the else sibling returns in place");
        let sibling_joined = both_returned
            .join_focused_execution_terminal(&record)
            .expect("both returned siblings form a terminal logical case split");
        assert_eq!(sibling_joined.focused_branch_id(), parent_id);
        let continuation_ids: Vec<BranchId> = sibling_joined.branches().collect();
        assert_eq!(continuation_ids, [parent_id]);
        assert!(matches!(
            sibling_joined.certificate().steps(),
            [ProofStep::If {
                condition,
                then_proof,
                else_proof,
                ..
            }] if matches!(
                then_proof.steps(),
                [ProofStep::Step, ProofStep::Step]
            ) && matches!(
                else_proof.steps(),
                [ProofStep::Step, ProofStep::Step]
            )
        ));
        let sibling_execution = sibling_joined
            .execution()
            .expect("the sibling terminal join retains execution state");
        assert!(sibling_execution.core.frontier.is_at_function_exit());
        assert_eq!(
            sibling_execution
                .core
                .frontier
                .execution()
                .expect("the sibling terminal join retains outcomes")
                .paths()
                .len(),
            2
        );
    }
    let (_, base_height, base_allocations) = allocation_samples[0];
    for (size, height, allocations) in allocation_samples {
        let allocation_bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= allocation_bound,
            "size {size} terminal branch join allocated {allocations} persistent fact nodes (logarithmic bound {allocation_bound})"
        );
    }
}

#[test]
fn completed_application_retention_does_not_rerun_and_scales() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::constant(0),
        ))),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::constant(0),
        ))),
    };
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let mut allocations = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut context = pure_identity_fixture();
        context.requires = (0..size).map(indexed_fact).collect();
        let goal = lower_pure_theorem_proposition(
            "retained",
            &surface,
            ContractEnvironment::new(&context.values, &context.array_refs),
            &context.point,
            SpecDefinitions::new(&predicates, &functions),
        )
        .unwrap();
        let root = Proof::for_pure_surface_goal(
            "retained",
            &context.requires,
            goal.clone(),
            surface.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let fixed = Proof::for_fixed_state_surface_goal(
            "retained fixed-state",
            0,
            &context.requires,
            goal.clone(),
            surface.clone(),
            ParameterBinding::default(),
            &state,
            &state,
            &retained_states,
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
        );
        for root in [root, fixed] {
            let completed = root.driver().apply_step(ProofStep::Known).unwrap();
            take_checked_have_operations();
            let before = fact_node_allocations();
            let retained = root.retain_completed_goal(&completed, &[]).unwrap();
            allocations.push(fact_node_allocations() - before);
            assert_eq!(
                take_checked_have_operations(),
                0,
                "retention must not reopen and rerun a have body"
            );
            assert!(!retained.is_complete());
            assert!(retained.facts().contains(&goal));
            assert!(root.certificate().steps().is_empty());
            assert!(
                matches!(retained.certificate().steps(), [ProofStep::Have { proof, .. }] if matches!(proof.steps(), [ProofStep::Known]))
            );
            retained
                .driver()
                .apply_step(ProofStep::Known)
                .unwrap()
                .completed_proposition()
                .unwrap();
            let other = Proof::for_pure_surface_goal(
                "other",
                &context.requires,
                goal.clone(),
                surface.clone(),
                &context,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
            )
            .driver()
            .apply_step(ProofStep::Known)
            .unwrap();
            assert!(root.retain_completed_goal(&other, &[]).is_err());
            assert!(root.retain_completed_goal(&root, &[]).is_err());
        }
    }
    for pair in allocations.windows(2) {
        assert!(
            pair[1] <= pair[0] + 128,
            "retention must share unrelated facts: {allocations:?}"
        );
    }
}

#[test]
fn fixed_state_source_failure_is_only_a_miss_at_an_explicit_search_boundary() {
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let goal = indexed_fact(10);
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(Variable(0)),
        ))),
        operator: ComparisonOperator::LessThan,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(10))),
    };
    let root = Proof::for_fixed_state_surface_goal(
        "source error",
        0,
        std::slice::from_ref(&goal),
        goal.clone(),
        surface,
        ParameterBinding::default(),
        &state,
        &state,
        &retained_states,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
    );
    let retained = root.clone();
    let script = [ProofTactic::CloseBounds(Vec::new()), ProofTactic::Known];
    let error = root
        .driver()
        .try_authoritative_linear_script(&script)
        .err()
        .expect("the written bound check must fail even though known could close the goal");
    assert!(error.message().contains("checked bound rule"), "{error:?}");
    assert!(error.message().contains("tactic 1"), "{error:?}");
    assert!(
        attempt::candidate_outcome(root.driver().try_authoritative_linear_script(&script))
            .unwrap()
            .is_none()
    );
    assert!(root.state.shares_state_with(&retained.state));
    assert!(root.certificate().steps().is_empty());
    let completed = root
        .driver()
        .try_authoritative_linear_script(&[ProofTactic::Known])
        .unwrap()
        .unwrap();
    assert_eq!(
        completed.completed_proposition().unwrap().proposition(),
        &goal
    );
    assert_eq!(
        completed.completed_certificate().unwrap().steps(),
        &[ProofStep::Known]
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn outcome_haves_and_folds_share_facts_and_keep_sibling_resources_isolated() {
    let click_file = crate::surface::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                owns marker(x);
                ensures returns_x: result == x;
            } by {
                unfold(marker(x));
                fold(marker(x));
                step_until(function.exit);
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource.clone()),
            _ => None,
        })
        .expect("the test function should own its marker resource");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
            )
            .expect("the marker resource definition should lower"),
        );
    let function_environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let empty_state = ExecutionState::new();
    let lowered = lower_resource_clause(
        &resource,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        empty_state.memory(),
    )
    .expect("the owned marker resource should lower");
    let state =
        empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

    for size in [8_u32, 16, 32, 64] {
        let root = Proof::for_execution_frontier(
            "persistent resource fold",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );

        let terminal = root
            .driver()
            .apply_step(ProofStep::Step)
            .expect("return step checks");
        let (outcomes, ids, _) = terminal
            .split_function_outcomes()
            .expect("checked exit produces an outcome");
        let root = outcomes
            .focus_branch(ids[0])
            .unwrap()
            .project_outcome_resources()
            .unwrap();
        for operations in [1_usize, 4, 16] {
            let mut current = root.clone();
            let before = current.checkpoint();
            crate::kernel::proof::take_fact_entry_counts();
            for index in 0..operations {
                let value = SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(
                    index as u32 + 1000,
                )));
                let proposition = SyntaxProposition::Comparison {
                    left: value.clone(),
                    operator: ComparisonOperator::Equal,
                    right: value,
                };
                current = current
                    .driver()
                    .open_have(proposition)
                    .unwrap()
                    .driver()
                    .try_authoritative_linear_script(&[ProofTactic::Known])
                    .unwrap()
                    .unwrap()
                    .join()
                    .unwrap()
                    .driver()
                    .apply_step(ProofStep::UnfoldResource(resource.clone()))
                    .unwrap()
                    .driver()
                    .apply_step(ProofStep::FoldResource(resource.clone()))
                    .unwrap();
            }
            let (indexed, materialized) = crate::kernel::proof::take_fact_entry_counts();
            assert_eq!(
                materialized, 0,
                "ambient {size}, operations {operations} rebuilt a fact vector"
            );
            assert!(
                indexed <= 8 * operations,
                "only explicit operation deltas may be indexed: {indexed}"
            );
            assert_eq!(
                current.certificate_since(&before).unwrap().steps().len(),
                3 * operations
            );
            assert_eq!(root.certificate().steps(), terminal.certificate().steps());
            assert_eq!(root.outcome_result(), current.outcome_result());
            let FunctionOutcome::Return { state: initial, .. } =
                root.focused_outcome_state().unwrap()
            else {
                unreachable!()
            };
            let FunctionOutcome::Return {
                state: final_state, ..
            } = current.focused_outcome_state().unwrap()
            else {
                unreachable!()
            };
            assert_eq!(initial.resources().facts(), final_state.resources().facts());
        }
        let unfolded = root
            .driver()
            .apply_step(ProofStep::UnfoldResource(resource.clone()))
            .unwrap();
        assert_ne!(
            unfolded.focused_outcome_state().unwrap(),
            root.focused_outcome_state().unwrap()
        );
    }
}

#[test]
fn execution_entry_retains_prepared_symbolic_write_selection() {
    let click_file = crate::surface::parse(
        r#"
        void put(int32* p, int32 i, int32 n) {
            requires 1 <= i;
            requires i < n;
            owns p[1..n];
        }
    "#,
    )
    .unwrap();
    let function =
        syntax::parse_function("void put(int32* p, int32 i, int32 n) { p[i] = 7; }").unwrap();
    let (state, _, facts, _) = initial_claim_context(
        &click_file.function_blocks()[0],
        &function,
        &ResourceEnvironment::new(click_file.resource_definitions()),
        SpecDefinitions::new(
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(click_file.click_function_definitions()),
        ),
        "symbolic write entry",
    )
    .unwrap();
    let owner = state
        .resources()
        .facts()
        .iter()
        .find_map(ResourceFact::memory_own_range)
        .expect("the written ownership clause remains live")
        .clone();
    let assumptions = facts.context();
    let root_facts = PureFactStore::from_source(&facts);
    assert!(
        state
            .resources()
            .memory_write_selection_is_known_for_test(&owner, root_facts.assumptions()),
        "proof root construction must preserve entry publication"
    );
    assert!(
        state
            .resources()
            .memory_write_selection_is_known_for_test(&owner, &assumptions),
        "execution must retain prepared selection in its final entry context"
    );
}

/// A generated tactic carries `usize::MAX` for its source index. A site asked
/// to address it names no written tactic, so the diagnostic falls back to the
/// checked-step count instead of printing the sentinel as a tactic number.
#[test]
fn a_generated_tactic_is_not_addressed_as_a_source_tactic() {
    let written = ProofStepSite::default().at_source_tactic(3);
    assert_eq!(written.path().as_deref(), Some("tactic 3"));
    let generated = written.at_source_tactic(usize::MAX);
    assert_eq!(generated.path(), None);
    assert_eq!(generated.source_tactic_path(), None);
}

#[test]
fn generated_scripts_inside_have_bodies_never_capture_written_tactics() {
    let written = ProofStepSite::default().at_source_tactic(3).in_have_body(0);
    assert_eq!(written.written_source_tactic_path(), Some(vec![3, 0]));
    let generated = written.at_source_tactic(usize::MAX);
    assert_eq!(generated.written_source_tactic_path(), None);
    // Traces can still attribute generated checking operations to the body
    // whose smart tactic requested them.
    assert_eq!(
        generated.at_block_position(0).source_tactic_path(),
        Some(vec![3, 0])
    );
    assert_eq!(
        generated.at_block_position(0).written_source_tactic_path(),
        None
    );
    assert_eq!(generated.in_have_body(0).written_source_tactic_path(), None);
    assert_eq!(
        generated.in_arm(0, "then", 0).written_source_tactic_path(),
        None
    );
    assert_eq!(written.written_source_tactic_path(), Some(vec![3, 0]));
}

#[test]
fn checked_callback_statement_publishes_its_typed_read_evidence() {
    let _session = crate::kernel::VerificationSession::enter();
    let click_file = crate::surface::parse("void read(int32* cb) { ensures true; }").unwrap();
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_functions(
        "typedef void (*callback)(int *p); struct callbacks { callback call; }; void read(struct callbacks *cb) { callback f = cb->call; }",
    ).unwrap().pop().unwrap();
    let function = parsed_function.to_kernel_function();
    fn load_type(statement: &ProgramStatement) -> Option<(ProgramType, &str)> {
        match statement {
            ProgramStatement::Seq(statements) => {
                statements.iter().find_map(|statement| load_type(statement))
            }
            ProgramStatement::Assign {
                name,
                expression: ProgramExpression::TypedLoad { value_type, .. },
                ..
            } => Some((*value_type, name.source_name())),
            _ => None,
        }
    }
    let (interface_type, read_local) =
        load_type(function.body()).expect("callback field is a typed load");
    let argument = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(210_520)), 4),
    );
    let table = Address::new("global:callback-table".into(), AddressOffset::constant(0));
    let target = Address::function("callback");
    let memory = SymbolicMemory::new().store(
        table.clone(),
        ProgramValue::typed_pointer(target.clone(), interface_type),
    );
    let source = crate::kernel::intern_memory_ref(&memory);
    let memory = memory.with_seeded_cells(argument.clone(), 4, interface_type, 0, 2, source);
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::new_with_element_width(
                argument.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
                8,
            )),
        ));
    let arguments = vec![ProgramExpression::Value(ProgramValue::pointer(
        argument.clone(),
    ))];
    let function_environment = ExecutionEnvironment::new();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut proof = Proof::for_execution_frontier(
        "callback read publication",
        0,
        ExecutionProofState::at_entry(
            state,
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![Proposition::condition_is(
            OldConditionTerm::address_equal(argument, table),
            true,
        )],
        ExecutionProofConstants {
            source_layout: SourceExecutionLayout::new(parsed_function.body()),
            ..ExecutionProofConstants::default()
        },
        function_block,
        &function,
        &parsed_function,
        &arguments,
        &function_environment,
        &resource_environment,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
    );
    proof = proof
        .driver()
        .apply_step(ProofStep::Step)
        .expect("declare callback local");
    proof = proof
        .driver()
        .apply_step(ProofStep::Step)
        .expect("read callback field");
    let execution = proof.execution().unwrap();
    let value = execution
        .core
        .state
        .scalar_local_value(read_local)
        .expect("callback local has a value");
    let ProgramValue::Pointer(read) = value else {
        panic!("callback local is a pointer")
    };
    assert!(
        execution
            .core
            .effect_facts
            .iter()
            .any(|fact| fact.has_checked_pointer_read()),
        "no typed read evidence: {:?}",
        execution.core.effect_facts
    );
    assert!(
        proof
            .facts()
            .assumptions()
            .contains_known(&Proposition::condition_is(
                OldConditionTerm::address_equal(read.address().clone(), target),
                true
            )),
        "typed read did not reach proof facts: {:?}",
        execution.core.effect_facts
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/proof/proof_object/tests.rs");
}
#[test]
fn fixed_state_transport_retains_checked_spellings_for_rewrite() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let names = SurfacePropositionMap::default();
    let left = OldMachineTerm::Variable(Variable(9_104_000));
    let right = OldMachineTerm::Variable(Variable(9_104_001));
    let equality = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        true,
    );
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(OldMachineTerm::constant(7)),
        },
        true,
    );
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::Binding("left".into()),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::Binding("right".into()),
    };
    let mut samples = Vec::new();
    for size in [0_u32, 16, 64, 256] {
        let parsed = syntax::parse_function("void noop(int32 left, int32 right) {}").unwrap();
        let arguments = vec![
            ProgramExpression::Value(ProgramValue::Int32(left.clone())),
            ProgramExpression::Value(ProgramValue::Int32(right.clone())),
        ];
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(equality.clone());
        let root = Proof::for_fixed_state_goal(
            "nested transport spellings",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::new(parsed.parameters(), &arguments),
            &state,
            &state,
            &retained_states,
            &names,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
        );
        let transported = root
            .driver()
            .apply_ordinary_transport_steps(&surface, vec![ProofStep::Known])
            .unwrap();
        assert!(matches!(
            transported.certificate().steps(),
            [ProofStep::Have { .. }]
        ));
        let mut forgotten_locals = transported.state().locals().clone();
        forgotten_locals.checked_lowerings = SurfacePropositionMap::default();
        let forgotten =
            transported.with_kernel_state(transported.state.with_locals(forgotten_locals));
        let (cached, cached_work) = crate::instrumentation::measure_deterministic_work(|| {
            transported
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
        });
        let (uncached, uncached_work) = crate::instrumentation::measure_deterministic_work(|| {
            forgotten
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
        });
        let cached = cached.unwrap();
        let uncached = uncached.unwrap();
        assert_eq!(cached.goal(), uncached.goal());
        assert!(
            cached_work <= uncached_work,
            "{size}: cached {cached_work}, uncached {uncached_work}"
        );
        assert!(
            root.local_surface_facts()
                .available_kernel_matching(&surface, |_| true)
                .is_none()
        );
        samples.push(cached_work);
        let absent = Proof::for_fixed_state_goal(
            "spelling is not authority",
            0,
            &[],
            goal.clone(),
            ParameterBinding::new(parsed.parameters(), &arguments),
            &state,
            &state,
            &retained_states,
            &names,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
        );
        let mut absent_locals = absent.state().locals().clone();
        absent_locals
            .checked_lowerings
            .record_lowering(&surface, &equality)
            .unwrap();
        let absent = absent.with_kernel_state(absent.state.with_locals(absent_locals));
        assert!(
            absent
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
                .is_err()
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 64),
        "{samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn fixed_state_instantiation_retains_checked_spellings_for_rewrite() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let names = SurfacePropositionMap::default();
    let parsed = syntax::parse_function("void noop(int32 left, int32 right) {}").unwrap();
    let left = OldMachineTerm::Variable(Variable(9_104_100));
    let right = OldMachineTerm::Variable(Variable(9_104_101));
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::Int32(left.clone())),
        ProgramExpression::Value(ProgramValue::Int32(right.clone())),
    ];
    let binding = ParameterBinding::new(parsed.parameters(), &arguments);
    let equal = |left: &str, right: &str| SyntaxProposition::Comparison {
        left: SyntaxTerm::Binding(left.into()),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::Binding(right.into()),
    };
    let quantified = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "item".into(),
        written_name: None,
        body: Box::new(SyntaxProposition::Implies(
            Box::new(equal("item", "left")),
            Box::new(equal("item", "right")),
        )),
    };
    let kernel = lower_fixed_state_proposition_with_assumptions(
        &quantified,
        &PureFactContext::new(),
        binding,
        FixedStateFrame::new(&state, &state, None, &retained_states),
        SpecDefinitions::new(&predicates, &functions),
    )
    .unwrap();
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(OldMachineTerm::constant(7)),
        },
        true,
    );
    let surface = equal("chosen", "right");
    let mut samples = Vec::new();
    for size in [0_u32, 16, 64, 256] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel.clone());
        let root = Proof::for_fixed_state_goal(
            "instantiated spelling",
            0,
            &facts,
            goal.clone(),
            binding,
            &state,
            &state,
            &retained_states,
            &names,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
        );
        let mut locals = root.state().locals().clone();
        locals.set_values(locals.values.with_inserted(
            "chosen",
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                left.clone(),
            ))),
        ));
        let root = root.with_kernel_state(root.state.with_locals(locals));
        let step = |argument| ProofStep::Instantiate {
            quantified: quantified.clone(),
            arguments: vec![argument],
        };
        let guarded = root
            .driver()
            .apply_step(step(SyntaxTerm::Binding("right".into())))
            .unwrap();
        assert!(!guarded.is_complete());
        assert!(
            guarded
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
                .is_err(),
            "a conditional equality cannot authorize the rewrite without its guard"
        );
        let instantiated = root
            .driver()
            .apply_step(step(SyntaxTerm::Binding("chosen".into())))
            .unwrap();
        assert!(
            instantiated
                .local_surface_facts()
                .shares_persistent_storage_with(root.local_surface_facts()),
            "captured instantiation values must not become certificate-printing candidates"
        );
        let mut locals = instantiated.state().locals().clone();
        locals.checked_lowerings = SurfacePropositionMap::default();
        let forgotten = instantiated.with_kernel_state(instantiated.state.with_locals(locals));
        let (cached, cached_work) = crate::instrumentation::measure_deterministic_work(|| {
            instantiated
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
        });
        let (uncached, uncached_work) = crate::instrumentation::measure_deterministic_work(|| {
            forgotten
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
        });
        assert_eq!(cached.unwrap().goal(), uncached.unwrap().goal());
        assert!(
            cached_work < uncached_work,
            "{size}: cached {cached_work}, uncached {uncached_work}"
        );
        samples.push(cached_work);
        let mut changed_locals = instantiated.state().locals().clone();
        changed_locals.set_values(changed_locals.values.with_inserted(
            "chosen",
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                OldMachineTerm::Variable(Variable(9_104_102)),
            ))),
        ));
        let shadowed =
            instantiated.with_kernel_state(instantiated.state.with_locals(changed_locals));
        assert!(
            shadowed
                .driver()
                .apply_step(ProofStep::Rewrite(surface.clone()))
                .is_err(),
            "a rebound proof name must not reuse the old argument's spelling"
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn fixed_state_rewrite_keeps_authored_goal_names_after_lookup_substitution() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let names = SurfacePropositionMap::default();
    let parsed = syntax::parse_function("void noop(int32 left, int32 right) {}").unwrap();
    let left = OldMachineTerm::Variable(Variable(9_104_200));
    let right = OldMachineTerm::Variable(Variable(9_104_201));
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::Int32(left.clone())),
        ProgramExpression::Value(ProgramValue::Int32(right.clone())),
    ];
    let facts = vec![Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        true,
    )];
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(OldMachineTerm::constant(7)),
        },
        true,
    );
    let surface_goal = |name: &str| SyntaxProposition::Comparison {
        left: SyntaxTerm::Binding(name.into()),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::IntegerLiteral("7".into()),
    };
    let root = Proof::for_fixed_state_surface_goal(
        "authored rewrite presentation",
        0,
        &facts,
        goal,
        surface_goal("left"),
        ParameterBinding::new(parsed.parameters(), &arguments),
        &state,
        &state,
        &retained_states,
        &names,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
    );
    let mut locals = root.state().locals().clone();
    locals.set_values(locals.values.with_inserted(
        "chosen",
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(right))),
    ));
    let root = root.with_kernel_state(root.state.with_locals(locals));
    let rewritten = root
        .driver()
        .apply_step(ProofStep::Rewrite(SyntaxProposition::Comparison {
            left: SyntaxTerm::Binding("left".into()),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::Binding("chosen".into()),
        }))
        .unwrap();
    assert_eq!(
        rewritten.surface_goal(),
        Some(&surface_goal("chosen")),
        "internal captured values must not replace authored proof names"
    );
}

#[test]
fn have_primitive_reports_prerequisites_and_driver_solves_them() {
    let file = crate::surface::parse(r#"
        theorem scoped_conversion(j: int32) {
            requires 0 <= j and j <= 255;
            ensures 0 == 0;
            ensures forall (k: int32) { k < j implies to_uint8(to_integer(j)) == to_uint8(to_integer(j)) };
        }
    "#).unwrap();
    let theorem = &file.theorem_definitions()[0];
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let definitions = SpecDefinitions::new(&predicates, &functions);
    let mut context = pure_identity_fixture();
    context.values.insert(
        "j".into(),
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(0))),
    );
    for requirement in theorem.requires() {
        let Requirement::Proposition(surface) = requirement else {
            panic!("pure requirement");
        };
        let kernel = lower_pure_theorem_proposition(
            "have prerequisite",
            surface,
            ContractEnvironment::new(&context.values, &context.array_refs),
            &context.point,
            definitions,
        )
        .unwrap();
        context
            .surface_requirements
            .record_lowering(surface, &kernel)
            .unwrap();
        context.requires.push(kernel);
    }
    let Ensure::Proposition(parent) = theorem.ensures()[0].ensure() else {
        panic!("pure goal");
    };
    let Ensure::Proposition(target) = theorem.ensures()[1].ensure() else {
        panic!("pure goal");
    };
    let kernel = lower_pure_theorem_proposition(
        "have prerequisite",
        parent,
        ContractEnvironment::new(&context.values, &context.array_refs),
        &context.point,
        definitions,
    )
    .unwrap();
    let root = Proof::for_pure_surface_goal(
        "have prerequisite",
        &context.requires,
        kernel,
        parent.clone(),
        &context,
        definitions,
        &theorems,
    );
    // No without_implicit_solve scope: the primitive itself must not solve.
    assert!(root.begin_have(target.clone(), true).is_err());
    let (_, obligations) = probe_open_obligations(|| root.begin_have(target.clone(), true));
    assert!(
        !obligations.recorded.is_empty(),
        "opening must expose its prerequisites"
    );
    assert!(
        root.certificate().steps().is_empty(),
        "preparation cannot publish a proof"
    );
    let scope = root
        .driver()
        .open_have(target.clone())
        .expect("the driver solves the prerequisites");
    let scope = scope.driver().apply_step(ProofStep::Intro).unwrap();
    let scope = scope.driver().apply_step(ProofStep::Intro).unwrap();
    let scope = scope.driver().try_solve_closure().unwrap().unwrap();
    let joined = scope.join().unwrap();
    assert!(
        joined.certificate().steps().len() > 1,
        "prerequisite proofs precede the have"
    );
    assert!(root.certificate().steps().is_empty());
}

#[test]
fn proposed_goal_spelling_retains_unproved_domains_for_the_driver() {
    let file = crate::surface::parse(
        r#"
        theorem spelling_domain(x: int32) {
            ensures 0 == 0;
            ensures to_integer(x + 1) == to_integer(x + 1);
        }
    "#,
    )
    .unwrap();
    let theorem = &file.theorem_definitions()[0];
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let definitions = SpecDefinitions::new(&predicates, &functions);
    let mut context = pure_identity_fixture();
    context.values.insert(
        "x".into(),
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(995899))),
    );
    let Ensure::Proposition(parent) = theorem.ensures()[0].ensure() else {
        panic!("parent");
    };
    let Ensure::Proposition(target) = theorem.ensures()[1].ensure() else {
        panic!("target");
    };
    let kernel = lower_pure_theorem_proposition(
        "spelling domain",
        parent,
        ContractEnvironment::new(&context.values, &context.array_refs),
        &context.point,
        definitions,
    )
    .unwrap();
    let root = Proof::for_pure_surface_goal(
        "spelling domain",
        &[],
        kernel,
        parent.clone(),
        &context,
        definitions,
        &theorems,
    );
    let (target_kernel, requirements) =
        probe_open_obligations(|| root.lower_surface_proposition_direct(target, "target"));
    let target_kernel = target_kernel.unwrap();
    assert!(!requirements.recorded.is_empty());
    let mut recorded = SurfacePropositionMap::default();
    recorded.record_lowering(target, &target_kernel).unwrap();
    let (premise, premise_probe) = probe_open_obligations(|| {
        crate::kernel::search::ProofSearch::available_surface_fact(
            &root,
            &recorded,
            None,
            &target_kernel,
        )
    });
    assert!(premise.is_none());
    assert!(
        premise_probe.recorded.is_empty(),
        "premise validation stays strict inside an outer probe"
    );
    let (candidate, outer) = probe_open_obligations(|| {
        crate::kernel::search::ProofSearch::proposed_surface_goal(&root, &recorded, &target_kernel)
    });
    let candidate =
        candidate.expect("a proposed goal can spell its term before proving its domain");
    assert!(
        outer.recorded.is_empty(),
        "presentation cannot leak debts into another operation"
    );
    assert!(root.begin_have(candidate.clone(), true).is_err());
    assert!(
        root.driver().open_have(candidate).is_err(),
        "reflexivity cannot prove the unbounded addition's domain"
    );
    assert!(root.certificate().steps().is_empty());
    assert!(!root.facts().contains(&requirements.recorded[0].proposition));
}

#[test]
fn partition_known_uses_the_fixed_state_not_its_entry_partition() {
    let cell = |name: &str| {
        Resource::Memory(MemoryRange::new(
            Address::new(name.into(), AddressOffset::constant(0)),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        ))
    };
    let left = cell("partition-left");
    let right = cell("partition-right");
    let entry =
        ExecutionState::new().with_resource_context(ResourceContext::new().unchecked_with_facts([
            ResourceFact::own(left.clone()),
            ResourceFact::View(right.clone()),
        ]));
    let goal = Proposition::ResourceSeparate {
        left: Box::new(left.clone()),
        right: Box::new(right),
    };
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    for retained in [false, true] {
        let current = if retained {
            entry.clone()
        } else {
            ExecutionState::new().with_resource_context(
                ResourceContext::new().unchecked_with_facts([ResourceFact::own(left.clone())]),
            )
        };
        let root = Proof::for_fixed_state_frontier(
            "partition known",
            0,
            &[],
            ParameterBinding::default(),
            FixedStateFrame::new(&entry, &current, None, &retained_states),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
        );
        let focused = root.focus_fixed_state_goal(goal.clone()).unwrap();
        // Exercise the partition rule itself, with no materialized separation.
        let state = focused
            .state
            .replace_focused_obligation_and_facts(
                focused.focused_obligation().unwrap().clone(),
                PureFactStore::default(),
            )
            .unwrap_or_else(|_| panic!("the selected goal must stay open"));
        let focused = focused.with_kernel_state(state);
        let _guard = crate::kernel::search::FastOperationScope::enter("partition known");
        assert_eq!(focused.apply_known().is_ok(), retained);
    }
}

#[test]
fn proof_binding_name_index_tracks_aliases_scopes_and_forks() {
    let value = |variable| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::typed_pointer(
            Address::symbolic(Variable(variable)),
            ProgramType::Int32Pointer,
        )))
    };
    let mut parent = ProofLocals::default();
    parent.set_values(parent.values.with_inserted("identity", value(981_010)));
    parent.set_values(parent.values.with_inserted("other_name", value(981_010)));
    let mut child = parent.clone();
    child.set_values(child.values.with_inserted("identity", value(981_011)));
    assert_eq!(
        parent
            .value_names
            .name(Variable(981_010))
            .and_then(SurfaceBinder::written),
        Some("identity")
    );
    assert_eq!(
        parent
            .value_names
            .name(Variable(981_011))
            .and_then(SurfaceBinder::written),
        None
    );
    assert_eq!(
        child
            .value_names
            .name(Variable(981_010))
            .and_then(SurfaceBinder::written),
        Some("other_name")
    );
    assert_eq!(
        child
            .value_names
            .name(Variable(981_011))
            .and_then(SurfaceBinder::written),
        Some("identity")
    );
    child.set_values(child.values.without_key(&"other_name".to_string()));
    assert_eq!(
        child
            .value_names
            .name(Variable(981_010))
            .and_then(SurfaceBinder::written),
        None
    );
    child.set_values(parent.values.clone());
    assert_eq!(
        child
            .value_names
            .name(Variable(981_010))
            .and_then(SurfaceBinder::written),
        Some("identity")
    );
    assert_eq!(
        child
            .value_names
            .name(Variable(981_011))
            .and_then(SurfaceBinder::written),
        None
    );
}

#[test]
fn proof_binding_names_keep_typed_scopes_when_a_generic_alias_leaves() {
    let variable = Variable(981_012);
    let mut locals = ProofLocals::default();
    locals.set_values(locals.values.with_inserted(
        "number",
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
            OldMachineTerm::Variable(variable),
        ))),
    ));
    locals.set_integer_values(locals.integer_values.with_inserted(
        "number",
        crate::kernel::SpecIntegerExpression::Term(IntegerTerm::Variable(variable)),
    ));
    locals.set_values(PersistentBinderMap::default());
    assert_eq!(
        locals
            .value_names
            .name(variable)
            .and_then(SurfaceBinder::written),
        Some("number")
    );
    locals.set_integer_values(PersistentBinderMap::default());
    assert_eq!(
        locals
            .value_names
            .name(variable)
            .and_then(SurfaceBinder::written),
        None
    );
    locals.set_algebraic_values(locals.algebraic_values.with_inserted(
        "model",
        crate::kernel::SpecAlgebraicExpression {
            algebraic_type: crate::kernel::AlgebraicType::parameter("T".into()),
            node: crate::kernel::SpecAlgebraicExpressionNode::Variable(variable),
        },
    ));
    let parent = locals.clone();
    locals.set_algebraic_values(PersistentBinderMap::default());
    assert_eq!(
        locals
            .value_names
            .name(variable)
            .and_then(SurfaceBinder::written),
        None
    );
    assert_eq!(
        parent
            .value_names
            .name(variable)
            .and_then(SurfaceBinder::written),
        Some("model")
    );
}

#[test]
fn generated_pointer_requirement_retains_lexical_binder_without_capturing_a_shadow() {
    let variable = Variable(981_020);
    let pointer =
        crate::kernel::Pointer::new(Address::symbolic(variable), ProgramType::Int32Pointer);
    let expression = SyntaxTerm::ProgramExpression(ProgramExpression::Value(
        ProgramValue::Pointer(pointer.clone()),
    ));
    let mut locals = ProofLocals::default();
    locals.set_values(locals.values.with_inserted("identity", expression));
    let state = ExecutionState::new();
    let goal = Proposition::condition_is(
        OldConditionTerm::address_equal(pointer.address().clone(), Address::null()),
        false,
    );
    let synthesize = || {
        crate::surface::proof::surface_synthesis::synthesize_surface_proposition(
            &goal,
            ParameterBinding::default(),
            &state,
        )
    };
    assert!(synthesize().is_none());
    {
        let _scope = crate::surface::proof::surface_synthesis::ProofBindingNamesScope::enter(
            locals.value_names.clone(),
            PersistentBinderMap::default(),
        );
        let spelling = crate::surface::printing::source_click_proposition(&synthesize().unwrap());
        assert!(spelling.contains("identity"), "{spelling}");
        let shadows = PersistentBinderMap::default().with_inserted(
            "identity",
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::typed_pointer(
                Address::symbolic(Variable(981_021)),
                ProgramType::Int32Pointer,
            ))),
        );
        {
            let _shadow = crate::surface::proof::surface_synthesis::ProofBindingNamesScope::enter(
                locals.value_names.clone(),
                shadows,
            );
            assert!(
                synthesize().is_none(),
                "an intro must not capture an outer pointer name"
            );
        }
        assert!(
            synthesize().is_some(),
            "the parent lexical scope is restored"
        );
    }
    assert!(synthesize().is_none(), "the arm's names must not leak");
}

fn known_have_step(proposition: SyntaxProposition) -> ProofStep {
    ProofStep::Have {
        proposition,
        proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Known]).unwrap()),
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.77s in the parallel scaling selection; guard classification has fast scaling coverage"]
fn loop_exit_eligibility_comes_from_the_guard_not_an_ownership_failure() {
    let file = crate::surface::parse("void boundary() { ensures true; }").unwrap();
    let parsed = syntax::parse_function("void boundary() {}").unwrap();
    let function = parsed.to_kernel_function();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let environment = ExecutionEnvironment::new();
    let state = ExecutionState::new().with_local(
        "gate",
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_771_000))),
    );
    let root = Proof::for_execution_frontier(
        "loop edge",
        0,
        ExecutionProofState::at_entry(
            state.clone(),
            ExecutionFrontier {
                region: ExecutionRegionKind::LoopBody,
                position: FrontierPosition::RegionBoundary,
                ..ExecutionFrontier::default()
            },
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        ),
        vec![],
        ExecutionProofConstants::default(),
        &file.function_blocks()[0],
        &function,
        &parsed,
        &[],
        &environment,
        &resources,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
    );
    let true_guard = ProgramExpression::Value(crate::kernel::int32(1));
    let false_guard = ProgramExpression::Value(crate::kernel::int32(0));
    let unknown_guard = ProgramExpression::Variable("gate".into());
    let owned = state.clone().with_resource_context(
        crate::kernel::ResourceContext::new().unchecked_with_fact(
            crate::kernel::ResourceFact::own_token("keep".into(), Vec::new()),
        ),
    );
    for (guard, consumed, may_continue, may_exit) in [
        (&false_guard, false, false, true),
        (&false_guard, true, false, true),
        (&true_guard, true, true, false),
        (&unknown_guard, true, true, true),
    ] {
        let head = if consumed { &owned } else { &state };
        let result = root.check_loop_boundary(
            head,
            head,
            &crate::kernel::IntegerTerm::constant_i64(0),
            Some(guard),
            &[],
            &[],
            None,
            &[],
            false,
        );
        if consumed && may_continue {
            assert!(
                result
                    .err()
                    .unwrap()
                    .message()
                    .contains("resource ownership"),
                "a continuing edge cannot become an exit when ownership is missing"
            );
        } else {
            let edge = result.unwrap();
            assert_eq!(edge.may_exit(), may_exit);
            assert_eq!(edge.state(), &state);
            assert_eq!(edge.explicit_exit_state().is_some(), consumed && may_exit);
        }
    }
}

/// `application` checked with exactly `premises`, as a written
/// `apply(...) using { ... }` is; `None` when the checker refuses it.
fn apply_using<'a>(
    proof: &Proof<'a>,
    application: &TheoremApplication,
    premises: Vec<SyntaxProposition>,
) -> Option<Proof<'a>> {
    proof
        .driver()
        .apply_step(ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises,
        })
        .ok()
}
