use super::*;

fn indexed_fact(index: u32) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(Bitvector32Term::Variable(Variable(0))),
            Box::new(Bitvector32Term::Constant(index)),
        ),
        true,
    )
}

fn fact_node_allocations() -> usize {
    persistent_node_allocations()
}

fn opposite_atomic_fact(fact: &Proposition) -> Proposition {
    match fact {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(body) => *body.clone(),
        other => Proposition::Not(Box::new(other.clone())),
    }
}

#[test]
fn execution_frontier_owns_compact_selected_effect_goals() {
    let click_file = crate::lang::click::parse(
        r#"
            verifying "identity.c";
            int32 identity(int32 x) {
                immutable;
                ensures result == x;
            } by {
                execute();
                frame();
                simp();
            }
        "#,
    )
    .expect("the effect-goal fixture should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("the effect-goal C function should parse");
    let function = parsed_function.to_kernel_function();
    let arguments = vec![CExpression::Value(int32(7))];
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(&[]);
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);

    for (claim, expected, selection) in [
        (CProofClaim::Grouped, 1, EffectGoalSelection::All),
        (CProofClaim::Effect(0), 1, EffectGoalSelection::One(0)),
        (CProofClaim::Ensure(0), 0, EffectGoalSelection::None),
    ] {
        let root = Proof::for_execution_frontier(
            "typed effect goals",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                TacticReplayState::default(),
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            Vec::new(),
            ExecutionProofConstants {
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "identity".to_string(),
                    claim,
                }),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        assert_eq!(root.effect_goal_count(), expected);
        assert!(
            matches!(root.focused_goal(), Some(Goal::Frontier(FrontierGoal { selection: actual, .. })) if *actual == selection)
        );
        let marked = root
            .apply_step(SimpleProofStep::Mark("selected".to_string()))
            .expect("an ordinary frontier step should preserve its effect goals");
        assert_eq!(marked.effect_goal_count(), expected);
        assert!(
            matches!(marked.focused_goal(), Some(Goal::Frontier(FrontierGoal { selection: actual, .. })) if *actual == selection)
        );
    }
}

fn pure_identity_fixture() -> PureTheoremContext {
    PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    }
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
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );

    // A locally successful prefix whose continuation fails is one
    // discarded candidate: the ancestor is unchanged and no partial
    // expansion is published.
    let mut budget = attempt::AttemptBudget::unbounded();
    let missed = attempt::attempt(&root, &mut budget, |candidate| {
        let prefix = attempt::candidate_outcome(candidate.apply_step(SimpleProofStep::Intro))?
            .expect("intro is locally valid on the implication goal");
        // The continuation demands a step the prefix cannot support.
        attempt::candidate_outcome(prefix.apply_step(SimpleProofStep::Split))
    })
    .expect("a rejected continuation is a miss, not a tooling failure");
    assert!(missed.is_none());
    assert!(root.certificate().steps().is_empty());
    assert!(!root.is_complete());

    // N candidate suffixes over one shared checked prefix cost N suffix
    // checks: every attempt starts from the same prefix state, which was
    // produced by exactly one accepted `Intro`.
    let prefix = root
        .apply_step(SimpleProofStep::Intro)
        .expect("intro should refine the implication goal");
    let mut attempts = 0usize;
    let mut budget = attempt::AttemptBudget::unbounded();
    let selected = attempt::first_success(
        &prefix,
        &mut budget,
        [
            SimpleProofStep::Split,
            SimpleProofStep::Left,
            SimpleProofStep::Right,
            SimpleProofStep::Assumption,
        ],
        |shared, step| {
            attempts += 1;
            assert!(Arc::ptr_eq(&shared.state, &prefix.state));
            attempt::candidate_outcome(shared.apply_step(step))
        },
    )
    .expect("candidate misses must not abort the search")
    .expect("the assumption suffix should close the goal");
    assert_eq!(attempts, 4);
    assert!(selected.is_complete());
    assert_eq!(
        selected.certificate().steps(),
        &[SimpleProofStep::Intro, SimpleProofStep::Assumption],
        "the retained certificate contains only the accepted path"
    );

    // An exhausted deterministic budget is a prompt bounded miss.
    let mut attempts = 0usize;
    let mut budget = attempt::AttemptBudget::new(1);
    let bounded = attempt::first_success(
        &prefix,
        &mut budget,
        [
            SimpleProofStep::Split,
            SimpleProofStep::Assumption,
            SimpleProofStep::Left,
        ],
        |shared, step| {
            attempts += 1;
            attempt::candidate_outcome(shared.apply_step(step))
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
        &[SimpleProofStep::Intro, SimpleProofStep::Split],
    )
    .expect("a rejected sequence tail is a miss");
    assert!(sequence.is_none());
    let mut budget = attempt::AttemptBudget::unbounded();
    let sequence = attempt::try_sequence(
        &root,
        &mut budget,
        &[SimpleProofStep::Intro, SimpleProofStep::Assumption],
    )
    .expect("an accepted sequence is not an error")
    .expect("the checked sequence should close the goal");
    assert_eq!(
        sequence.certificate().steps(),
        &[SimpleProofStep::Intro, SimpleProofStep::Assumption]
    );
}

#[test]
fn focused_case_split_partitions_by_attribution_and_rejects_foreign_joins() {
    let equality = |value| ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(value))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(value))),
    };
    let disjunction = ClickProposition::Or(Box::new(equality(0)), Box::new(equality(1)));
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let theorem_context = pure_identity_fixture();
    let kernel_disjunction = lower_pure_theorem_proposition(
        "focused cases",
        &disjunction,
        &theorem_context.values,
        &theorem_context.array_refs,
        &theorem_context.memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("constant disjunction should lower");
    let root = Proof::for_pure_goal(
        "focused cases",
        std::slice::from_ref(&kernel_disjunction),
        kernel_disjunction.clone(),
        &theorem_context,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );

    // The split retires the parent id and opens both sibling goals in
    // one state, each carrying its own disjunct in its own context.
    let root_goal = root.sole_goal_id().expect("the root owns its goal");
    let (split_proof, split, ids) = root
        .split_focused_cases(disjunction.clone())
        .expect("the exact disjunction splits in-proof");
    assert_eq!(split_proof.goals().collect::<Vec<_>>(), ids);
    assert!(split_proof.state.goals.get(root_goal).is_none());
    let marker = split_proof.checkpoint();

    // Arms are proven by focusing each recorded id on one lineage; the
    // interleaved steps carry their goal attribution.
    let left_closed = split_proof
        .focus(ids[0])
        .expect("the left sibling is open")
        .apply_step(SimpleProofStep::Assumption)
        .expect("the shared disjunction fact closes the left claim");
    assert!(left_closed.state.goals.get(ids[1]).is_some());
    let both_closed = left_closed
        .focus(ids[1])
        .expect("the right sibling is still open")
        .apply_step(SimpleProofStep::Assumption)
        .expect("the shared disjunction fact closes the right claim");
    assert!(both_closed.is_complete());

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
    // one structured step whose parent is the pre-split provenance.
    let joined = both_closed
        .join_focused_cases(&marker, split, ids, disjunction.clone())
        .expect("both recorded arms are discharged");
    assert!(joined.is_complete());
    assert!(matches!(
        joined.certificate().steps(),
        [SimpleProofStep::Cases {
            left_proof,
            right_proof,
            ..
        }] if left_proof.steps() == [SimpleProofStep::Assumption]
            && right_proof.steps() == [SimpleProofStep::Assumption]
    ));
    assert!(root.certificate().steps().is_empty());
    assert_eq!(root.sole_goal_id(), Some(root_goal));

    // An incomplete sibling refuses the join transactionally.
    assert!(
        left_closed
            .join_focused_cases(&marker, split, ids, disjunction)
            .is_err(),
        "an open sibling goal must refuse the join"
    );

    // A rejected arm candidate leaves the split state untouched.
    let focused = split_proof.focus(ids[0]).expect("the left sibling is open");
    assert!(
        focused.apply_step(SimpleProofStep::Intro).is_err(),
        "an atomic claim rejects `intro`"
    );
    assert_eq!(split_proof.goals().collect::<Vec<_>>(), ids);
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
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );

    // Without a deadline the unprovable candidate is an ordinary miss.
    let mut budget = attempt::AttemptBudget::unbounded();
    let missed = attempt::try_steps(&root, &mut budget, [SimpleProofStep::Assumption])
        .expect("a rejected candidate is a miss");
    assert!(missed.is_none());

    // With the deadline exceeded, the same rejection is a tooling
    // failure: the search aborts loudly instead of reading the error as
    // one more rejected candidate and continuing.
    let aborted = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        let mut budget = attempt::AttemptBudget::unbounded();
        attempt::try_steps(&root, &mut budget, [SimpleProofStep::Assumption])
    });
    assert!(
        aborted.is_err(),
        "an exceeded deadline must abort the search, not read as a miss"
    );
    let aborted = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        root.try_direct_logical_closure()
    });
    assert!(
        aborted.is_err(),
        "the shared closure search must propagate an exceeded deadline"
    );
}

#[test]
fn proof_failure_preserves_ancestor_and_selected_provenance() {
    let goal = indexed_fact(7);
    let theorem_context = PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::new(),
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
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );
    let fork = root.clone();
    assert!(Arc::ptr_eq(&root.state, &fork.state));
    assert!(Arc::ptr_eq(&root.node, &fork.node));

    assert!(
        fork.apply_step(SimpleProofStep::Normalize).is_err(),
        "a symbolic comparison must not normalize to true"
    );
    assert!(!root.is_complete());
    assert!(root.certificate().steps().is_empty());

    let complete = root
        .apply_step(SimpleProofStep::Assumption)
        .expect("the exact root fact should close the goal");
    assert!(complete.is_complete());
    assert_eq!(
        complete.certificate().steps(),
        &[SimpleProofStep::Assumption]
    );
    assert!(!root.is_complete());
    assert!(root.certificate().steps().is_empty());
}

#[test]
fn goal_identity_is_stable_across_fork_refinement_and_discharge() {
    let fact = indexed_fact(7);
    let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
    let theorem_context = PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::new(),
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
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );

    // Forking preserves every open goal's identity and allocates nothing.
    let root_id = root
        .sole_goal_id()
        .expect("a fresh proof owns its root goal");
    let fork = root.clone();
    assert_eq!(fork.sole_goal_id(), Some(root_id));

    // A goal-preserving refinement rule changes the obligation's content
    // but keeps its id and allocates no new identifier. The persistent
    // budget covers the one-node goal-map update plus inserting the
    // introduced antecedent into each fact index of this one-fact proof;
    // it must stay a small constant, not scale with proof size.
    let before_refinement = fact_node_allocations();
    let introduced = root
        .apply_step(SimpleProofStep::Intro)
        .expect("intro should refine the implication goal");
    assert_eq!(introduced.sole_goal_id(), Some(root_id));
    assert_eq!(introduced.goals_next_id(), root.goals_next_id());
    // Provenance records which goal each step advanced: certificate
    // extraction partitions interleaved multi-goal derivations by this
    // attribution rather than inferring ownership from final states.
    assert_eq!(introduced.node.focused, root_id);
    assert_eq!(introduced.focused, root_id);
    assert!(
        fact_node_allocations() - before_refinement <= 24,
        "refining the sole goal must touch only constant persistent state"
    );

    // Discharge retires the id: the collection is empty and the allocator
    // never reuses the retired identifier.
    let complete = introduced
        .apply_step(SimpleProofStep::Assumption)
        .expect("the introduced fact should close the consequent");
    assert!(complete.is_complete());
    assert_eq!(complete.sole_goal_id(), None);
    assert_eq!(complete.goals_next_id(), introduced.goals_next_id());

    // Retiring the goal in one descendant leaves the forked sibling's
    // obligation open under the same identity.
    assert_eq!(fork.sole_goal_id(), Some(root_id));
    assert!(!fork.is_complete());
    assert!(!introduced.is_complete());
}

#[test]
fn certificate_suffix_requires_an_exact_shared_ancestor() {
    let fact = indexed_fact(7);
    let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
    let theorem_context = PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::new(),
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
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );
    let root_checkpoint = root.checkpoint();
    let introduced = root
        .apply_step(SimpleProofStep::Intro)
        .expect("intro should create the exact antecedent fact");
    let introduced_checkpoint = introduced.checkpoint();
    let complete = introduced
        .apply_step(SimpleProofStep::Assumption)
        .expect("the introduced fact should close the consequent");

    assert_eq!(
        complete
            .certificate_since(&root_checkpoint)
            .expect("root is an ancestor")
            .steps(),
        &[SimpleProofStep::Intro, SimpleProofStep::Assumption]
    );
    assert_eq!(
        complete
            .certificate_since(&introduced_checkpoint)
            .expect("introduced proof is an ancestor")
            .steps(),
        &[SimpleProofStep::Assumption]
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
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );
    assert!(
        complete.certificate_since(&unrelated.checkpoint()).is_err(),
        "a structurally identical but separately rooted proof cannot be spliced"
    );
}

#[test]
fn have_scope_publishes_only_a_completed_checked_body() {
    let proposition = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let theorem_context = PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let kernel = lower_pure_theorem_proposition(
        "have",
        &proposition,
        &theorem_context.values,
        &theorem_context.array_refs,
        &theorem_context.memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("constant equality should lower");
    let root = Proof::for_pure_goal(
        "have",
        &[],
        kernel,
        &theorem_context,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
    );
    let scope = root
        .begin_have(proposition.clone())
        .expect("have should open a nested proposition proof");
    assert!(scope.clone().join().is_err());
    assert!(scope.apply_step(SimpleProofStep::Intro).is_err());
    assert!(scope.body().certificate().steps().is_empty());

    let scope = scope
        .apply_step(SimpleProofStep::Normalize)
        .expect("constant equality should normalize inside the body");
    let enclosing = scope.join().expect("completed body should close the scope");
    assert!(!enclosing.is_complete());
    assert_eq!(enclosing.added_facts().len(), 1);
    let complete = enclosing
        .apply_step(SimpleProofStep::Assumption)
        .expect("published have fact should close the enclosing goal");
    assert_eq!(
        complete.certificate().steps(),
        &[
            SimpleProofStep::Have {
                proposition: proposition.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![
                    SimpleProofStep::Normalize,
                ])),
            },
            SimpleProofStep::Assumption,
        ]
    );
    assert!(!root.is_complete());
    assert!(root.certificate().steps().is_empty());
    assert!(
        root.apply_step(SimpleProofStep::Have {
            proposition: proposition.clone(),
            proof: Box::new(ProofCertificate::from_steps(vec![SimpleProofStep::Intro])),
        })
        .is_err(),
        "an invalid explicit Have body must be rejected"
    );
    assert!(
        root.certificate().steps().is_empty(),
        "a rejected explicit Have body must leave its immutable root untouched"
    );

    let checked_have = root
        .apply_step(SimpleProofStep::Have {
            proposition: proposition.clone(),
            proof: Box::new(ProofCertificate::from_steps(vec![
                SimpleProofStep::Normalize,
            ])),
        })
        .expect("an explicit Have step should use the owned checked scope");
    let complete = checked_have
        .apply_step(SimpleProofStep::Assumption)
        .expect("the checked Have step should publish its proposition");
    assert_eq!(
        complete.certificate().steps(),
        &[
            SimpleProofStep::Have {
                proposition,
                proof: Box::new(ProofCertificate::from_steps(vec![
                    SimpleProofStep::Normalize,
                ])),
            },
            SimpleProofStep::Assumption,
        ]
    );
}

#[test]
fn smart_have_scope_and_explicit_step_scale_with_local_output() {
    let proposition = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let memory = CMemory::new();
    let kernel = lower_pure_theorem_proposition(
        "smart have scaling",
        &proposition,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("constant equality should lower");
    let smart_body = [ProofTactic::Simp];
    let missing_body = [
        ProofTactic::ApplyTheorem(TheoremApplication {
            name: "missing".to_string(),
            arguments: Vec::new(),
        }),
        ProofTactic::Simp,
    ];

    for size in [16_u32, 64, 256, 1024, 4096] {
        let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let theorem_context = PureTheoremContext {
            memory: memory.clone(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let root = Proof::for_pure_goal(
            "smart have scaling",
            &requires,
            kernel.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let scope = root
            .begin_have(proposition.clone())
            .expect("have should open a nested proof");
        assert!(
            scope
                .try_linear_smart_script(&missing_body)
                .expect("an unknown theorem should be a bounded smart-search miss")
                .is_none(),
            "an unknown theorem must not manufacture a nested descendant"
        );
        assert!(scope.body().certificate().steps().is_empty());

        let before = fact_node_allocations();
        let selected = scope
            .try_linear_smart_script(&smart_body)
            .expect("nested smart search should not fail")
            .expect("simp should close the constant equality");
        let enclosing = selected
            .join()
            .expect("the completed nested proof should join");
        let complete = enclosing
            .apply_step(SimpleProofStep::Assumption)
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
                SimpleProofStep::Have {
                    proposition: proposition.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![
                        SimpleProofStep::Normalize,
                    ])),
                },
                SimpleProofStep::Assumption,
            ]
        );

        let before = fact_node_allocations();
        let complete = root
            .apply_step(SimpleProofStep::Have {
                proposition: proposition.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![
                    SimpleProofStep::Normalize,
                ])),
            })
            .expect("the explicit Have should check through its owned scope")
            .apply_step(SimpleProofStep::Assumption)
            .expect("the explicit Have should publish its proposition");
        let allocations = fact_node_allocations() - before;
        assert!(
            allocations <= allocation_bound,
            "size {size} explicit Have allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            complete.certificate().steps(),
            &[
                SimpleProofStep::Have {
                    proposition: proposition.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![
                        SimpleProofStep::Normalize,
                    ])),
                },
                SimpleProofStep::Assumption,
            ]
        );
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn persistent_fact_lookup_scales_logarithmically() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    for size in [16_u32, 64, 256, 1024, 4096] {
        let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let goal = indexed_fact(size - 1);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires,
            surface_requirements: SurfacePropositionMap::default(),
        };
        let proof = Proof::for_pure_goal(
            "scaling",
            &theorem_context.requires,
            goal.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let shared = proof.clone();
        assert!(Arc::ptr_eq(&proof.state, &shared.state));
        assert!(Arc::ptr_eq(&proof.node, &shared.node));

        let comparisons = proof.fact_lookup_comparisons(&goal);
        let logarithmic_bound = 2 * (u32::BITS - size.leading_zeros()) as usize + 2;
        assert!(
            comparisons <= logarithmic_bound,
            "size {size} lookup took {comparisons} comparisons (bound {logarithmic_bound})"
        );

        let complete = shared
            .apply_step(SimpleProofStep::Assumption)
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
fn introduced_since_recovers_only_the_appended_delta() {
    for size in [16_u32, 64, 256, 1024, 4096] {
        let ancestor_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let ancestor = ProofFacts::from_ordered(&ancestor_facts);

        // A fork that adds two ordinary facts reports exactly those, in
        // insertion order, regardless of the shared ancestor's size.
        let first = indexed_fact(size + 1);
        let second = indexed_fact(size + 2);
        let fork = ancestor.with_fact(first.clone()).with_fact(second.clone());
        assert_eq!(
            fork.introduced_since(&ancestor),
            Some(vec![first.clone(), second.clone()])
        );

        // A duplicate insertion introduces nothing.
        let unchanged = ancestor.with_fact(indexed_fact(0));
        assert_eq!(unchanged.introduced_since(&ancestor), Some(Vec::new()));

        // The ancestor itself is a trivial delta, and identity — not
        // structure — proves the shared history: an equal-content
        // context built independently is not an ancestor.
        assert_eq!(ancestor.introduced_since(&ancestor), Some(Vec::new()));
        let rebuilt = ProofFacts::from_ordered(&ancestor_facts);
        assert_eq!(fork.introduced_since(&rebuilt), None);

        // Divergent forks are not each other's ancestors.
        let sibling = ancestor.with_fact(indexed_fact(size + 3));
        assert_eq!(sibling.introduced_since(&fork), None);
    }
}

#[test]
fn proof_fact_forks_share_context_and_local_insertions_are_logarithmic() {
    let mut allocation_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let facts = ProofFacts::from_ordered(&initial);
        let fork = facts.clone();
        assert!(facts.exact.shares_root_with(&fork.exact));
        assert!(
            facts
                .assumptions
                .shares_persistent_storage_with(&fork.assumptions)
        );

        let added = indexed_fact(size + 1);
        let before = fact_node_allocations();
        let successor = fork.with_fact(added.clone());
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        allocation_samples.push((size, logarithmic_height, allocations));
        assert!(!facts.contains(&added));
        assert!(successor.contains(&added));
        assert!(successor.assumptions.proves(&added));
    }
    let (_, base_height, base_allocations) = allocation_samples[0];
    assert!(
        base_allocations <= 48,
        "small persistent fact insertion allocated {base_allocations} nodes"
    );
    for (size, height, allocations) in allocation_samples {
        // A condition fact updates the exact and normalized indexes, the
        // kernel condition map, and the two endpoint maps in its signed
        // order index. Every one is an AVL path copy; adding two tree
        // levels may therefore add at most 24 nodes.
        let allocation_bound = base_allocations + 12 * (height - base_height);
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
    let facts = ProofFacts::from_ordered(&[first.clone(), promoted.clone()]);
    let ambient_tail = facts.ordered.clone();
    let successor = facts.with_statement_facts(vec![promoted.clone(), added.clone()]);

    assert!(successor.ordered.shares_tail_with(&ambient_tail));
    assert_eq!(successor.to_vec(), vec![promoted, added, first]);
}

#[test]
fn replay_availability_probes_equivalent_condition_polarities_by_exact_index() {
    let left = Bitvector32Term::Variable(Variable(80_000));
    let right = Bitvector32Term::Variable(Variable(80_001));
    let available = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(Box::new(left.clone()), Box::new(right.clone())),
        true,
    );
    let facts = ProofFacts::from_ordered(&[available]);
    for required in [
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ),
            false,
        ),
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(right.clone()),
                Box::new(left.clone()),
            ),
            false,
        ),
        Proposition::Not(Box::new(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(right.clone()),
                Box::new(left.clone()),
            ),
            false,
        ))),
    ] {
        assert!(facts.replay_available_across_effects(&required, &[]));
    }
}

#[test]
fn proof_fact_predicate_index_ignores_unrelated_context() {
    let name = "selected".to_string();
    let predicate = Proposition::Predicate {
        name: name.clone(),
        arguments: Vec::new(),
    };
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
        initial.push(predicate.clone());
        let facts = ProofFacts::from_ordered(&initial);
        let fork = facts.clone();

        assert!(facts.ordered.shares_tail_with(&fork.ordered));
        assert!(facts.exact.shares_root_with(&fork.exact));
        assert!(facts.by_predicate.shares_root_with(&fork.by_predicate));
        assert_eq!(facts.to_vec(), initial);
        assert_eq!(
            facts.mentioning_predicate(&name).collect::<Vec<_>>(),
            vec![&predicate]
        );
    }
}

#[test]
fn outcome_fact_resync_preserves_only_surviving_unfold_provenance() {
    let universal = |index: u64| Proposition::ForAll {
        var: Variable(index),
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(index))),
                Box::new(Bitvector32Term::Variable(Variable(index))),
            ),
            true,
        )),
    };
    let surviving = universal(9_000_000);
    let removed = universal(9_000_001);

    for size in [16_u64, 64, 256, 1024, 4096] {
        let ambient = (0..size)
            .map(|index| universal(10_000_000 + index))
            .collect::<Vec<_>>();
        let mut original_order = ambient.clone();
        original_order.push(surviving.clone());
        original_order.push(removed.clone());
        let original = ProofFacts::from_ordered(&original_order)
            .with_predicate_unfold_fact(surviving.clone())
            .with_predicate_unfold_fact(removed.clone());

        let mut successor_order = ambient;
        successor_order.push(surviving.clone());
        let before_baseline = fact_node_allocations();
        let _baseline = ProofFacts::from_ordered(&successor_order);
        let baseline_allocations = fact_node_allocations() - before_baseline;
        let before_resync = fact_node_allocations();
        let successor = original.resync_ordered_preserving_provenance(&successor_order);
        let resync_allocations = fact_node_allocations() - before_resync;

        assert_eq!(
            successor
                .predicate_unfolded_universal_facts
                .iter()
                .collect::<Vec<_>>(),
            vec![&surviving],
            "size {size} must retain only surviving checked-unfold provenance"
        );
        assert!(successor.contains_top_level(&surviving));
        assert!(!successor.contains_top_level(&removed));
        let logarithmic_height = (u64::BITS - size.leading_zeros()) as usize;
        let provenance_overhead = resync_allocations.saturating_sub(baseline_allocations);
        let overhead_bound = 16 * logarithmic_height + 32;
        assert!(
            provenance_overhead <= overhead_bound,
            "size {size} provenance resync added {provenance_overhead} persistent nodes over the legacy rebuild (bound {overhead_bound})"
        );
    }
}

#[test]
fn proposition_unfold_uses_indexed_facts_and_persistent_local_state() {
    let click_file = crate::lang::click::parse(
        r#"
            predicate selected(x: int32) { x == x }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
            }
        "#,
    )
    .expect("test predicate should parse");
    let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let predicate_surface = ClickProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: vec![ContractExpression::CFragment(CExpression::Value(int32(7)))],
    };
    let goal_surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(7))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };
    let base_context = PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::new(),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let lower = |surface: &ClickProposition| {
        lower_pure_theorem_proposition(
            "persistent proposition unfold",
            surface,
            &base_context.values,
            &base_context.array_refs,
            &base_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("test proposition should lower")
    };
    let predicate = lower(&predicate_surface);
    let goal = lower(&goal_surface);

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(predicate.clone());
        let theorem_context = PureTheoremContext {
            requires: requires.clone(),
            ..base_context.clone()
        };
        let root = Proof::for_pure_surface_goal(
            "persistent proposition unfold",
            &requires,
            predicate.clone(),
            predicate_surface.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
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
            root.apply_step(SimpleProofStep::UnfoldPredicate("missing".to_string()))
                .is_err(),
            "an unknown predicate must reject transactionally"
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let unfold = SimpleProofStep::UnfoldPredicate("selected".to_string());
        let before = fact_node_allocations();
        let unfolded = root
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
        assert!(
            unfolded
                .focused_goal_unfolds()
                .contains(&"selected".to_string())
        );
        let complete = unfolded
            .apply_step(SimpleProofStep::Assumption)
            .expect("the unfolded predicate fact should close the unfolded goal");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[unfold.clone(), SimpleProofStep::Assumption]
        );

        let certificate =
            ProofCertificate::from_steps(vec![unfold.clone(), SimpleProofStep::Assumption]);
        let checked = root
            .try_planned_linear_script(&certificate.to_proof_tactics())
            .expect("the explicit proposition unfold script should apply through Proof")
            .expect("the explicit proposition unfold script should close");
        assert!(checked.is_complete());
        assert_eq!(checked.certificate(), certificate);
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_proposition_unfold_checks_the_same_retained_step() {
    let click_file = crate::lang::click::parse(
        r#"
            predicate selected(x: int32) { x == x }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
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
    let state = CState::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let program_point_states = ProgramPointStates::new();
    let predicate_surface = ClickProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: vec![ContractExpression::CFragment(CExpression::Value(int32(7)))],
    };
    let goal_surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(7))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("point proposition should lower")
    };
    let predicate = lower(&predicate_surface);
    let goal = lower(&goal_surface);
    let surface_propositions = SurfacePropositionMap::default();
    let root = Proof::for_point_goal(
        "point proposition unfold",
        0,
        std::slice::from_ref(&predicate),
        goal.clone(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        &program_point_states,
        &surface_propositions,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
        &[],
        &[],
    );
    let certificate = ProofCertificate::from_steps(vec![
        SimpleProofStep::UnfoldPredicate("selected".to_string()),
        SimpleProofStep::Assumption,
    ]);
    let checked = root
        .try_planned_linear_script(&certificate.to_proof_tactics())
        .expect("point unfold should use the shared Proof script driver")
        .expect("point unfold should close through the shared predicate transition");
    assert!(checked.is_complete());
    assert_eq!(checked.certificate(), certificate);
    assert!(root.certificate().steps().is_empty());

    let result = int32(7);
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(predicate.clone());
        let root = Proof::for_point_frontier(
            "result-aware point-frontier unfold",
            0,
            &facts,
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        assert!(
            root.apply_step(SimpleProofStep::UnfoldPredicate("missing".to_string()))
                .is_err()
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));

        let step = SimpleProofStep::UnfoldPredicate("selected".to_string());
        let before = fact_node_allocations();
        let unfolded = root
            .apply_step(step.clone())
            .expect("a point frontier should accept a facts-only predicate unfold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 40 * logarithmic_height + 160;
        assert!(
            allocations <= allocation_bound,
            "size {size} result-aware frontier unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(unfolded.certificate().steps(), &[step]);
        assert_eq!(unfolded.added_facts(), std::slice::from_ref(&goal));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_proof_root_borrows_inherited_unfold_history_without_reindexing_it() {
    let inherited = (0..4096)
        .map(|index| format!("predicate_{index}"))
        .collect::<Vec<_>>();
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let goal = indexed_fact(7);
    let before = fact_node_allocations();
    let root = Proof::for_point_goal(
        "borrowed unfold history",
        0,
        &[],
        goal,
        &[],
        &[],
        &state,
        &state,
        &program_point_states,
        &surface_propositions,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
        &inherited,
        &[],
    );
    let allocations = fact_node_allocations() - before;
    // The one permitted node stores the root goal in the persistent goal
    // collection; the bound must stay independent of the inherited size.
    assert!(
        allocations <= 1,
        "creating a point Proof must not rebuild inherited unfold history \
         ({allocations} persistent nodes allocated)"
    );
    assert_eq!(root.focused_goal_unfolds().len(), 0);
    assert_eq!(root.active_unfolded_predicates(), inherited);
}

#[test]
fn result_aware_point_goal_focus_shares_facts_and_checks_assumption() {
    let state = CState::new();
    let result = int32(0);
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let goal = indexed_fact(9_000_000);
    let missing = indexed_fact(9_000_001);

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(goal.clone());
        let root = Proof::for_point_frontier(
            "result-aware point goal focus",
            0,
            &facts,
            &[],
            &[],
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let before = fact_node_allocations();
        let focused = root
            .focus_point_goal(goal.clone())
            .expect("an initial point frontier should focus one ensure goal");
        // The one permitted node stores the focused root goal in the
        // fresh proof's goal collection; every fact index stays shared.
        assert!(
            fact_node_allocations() - before <= 1,
            "focusing a goal must share every persistent fact index"
        );
        assert!(root.facts().exact.shares_root_with(&focused.facts().exact));
        let retained_focused = focused.clone();
        assert!(
            root.focus_point_goal(missing.clone())
                .expect("focusing does not prove the selected goal")
                .apply_step(SimpleProofStep::Assumption)
                .is_err()
        );
        assert!(Arc::ptr_eq(&focused.state, &retained_focused.state));

        let complete = focused
            .apply_step(SimpleProofStep::Assumption)
            .expect("the focused exact goal should close through Proof");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[SimpleProofStep::Assumption]
        );
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_frontier_have_publishes_checked_fact_for_later_scope() {
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let state = CState::new();
    let result = int32(0);
    let arguments = vec![CExpression::Value(result.clone())];
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let proposition = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_point_frontier(
            "point frontier have",
            0,
            &facts,
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let first = root
            .begin_have(proposition.clone())
            .expect("a point frontier should open a checked have scope")
            .apply_step(SimpleProofStep::Normalize)
            .expect("the first scope should prove the concrete equality")
            .join()
            .expect("a completed point-frontier scope should publish its fact");
        let second = first
            .begin_have(proposition.clone())
            .expect("the checked successor should open a dependent scope")
            .apply_step(SimpleProofStep::Assumption)
            .expect("the later scope should see the first checked fact")
            .join()
            .expect("the dependent scope should publish its retained proof");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 40 * logarithmic_height + 160;
        assert!(
            allocations <= allocation_bound,
            "size {size} two-scope point proof allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(matches!(
            second.certificate().steps(),
            [
                SimpleProofStep::Have { proof: first, .. },
                SimpleProofStep::Have { proof: second, .. }
            ] if first.steps() == [SimpleProofStep::Normalize]
                && second.steps() == [SimpleProofStep::Assumption]
        ));
        let completed = second
            .complete_point_obligations(std::slice::from_ref(&proposition))
            .expect("the accumulated frontier should close its external obligation");
        assert!(matches!(
            completed.steps(),
            [
                SimpleProofStep::Have { .. },
                SimpleProofStep::Have { .. },
                SimpleProofStep::Assumption
            ]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_frontier_have_goal_does_not_reuse_an_older_surface_lowering() {
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let state = CState::new();
    let result = int32(1);
    let arguments = vec![CExpression::Value(result.clone())];
    let program_point_states = ProgramPointStates::new();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let older = indexed_fact(9_200_000);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&surface, &older)
        .expect("the older form should be recorded");
    let root = Proof::for_point_frontier(
        "point have current goal",
        0,
        std::slice::from_ref(&older),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        Some(&result),
        &program_point_states,
        &surface_propositions,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
        &[],
        &[],
    );
    let scope = root
        .begin_have(surface)
        .expect("the current point goal should lower independently");
    assert!(
        scope.apply_step(SimpleProofStep::Assumption).is_err(),
        "an older fact with the same surface form must not close the current goal"
    );
    assert!(root.certificate().steps().is_empty());
}

#[test]
fn proof_if_fork_and_join_work_is_logarithmic_in_unrelated_facts() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let condition = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(1))),
    };
    let surface_goal = ClickProposition::Or(
        Box::new(condition.clone()),
        Box::new(ClickProposition::Not(Box::new(condition.clone()))),
    );

    for size in [16_u32, 64, 256, 1024, 4096] {
        let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires,
            surface_requirements: SurfacePropositionMap::default(),
        };
        let goal = lower_pure_theorem_proposition(
            "branch scaling",
            &surface_goal,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("excluded-middle goal should lower");
        let root = Proof::for_pure_goal(
            "branch scaling",
            &theorem_context.requires,
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
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
            .apply_step(SimpleProofStep::Left)
            .expect("the condition closes the then arm")
            .focus(ids[1])
            .expect("the else sibling remains open")
            .apply_step(SimpleProofStep::Right)
            .expect("the exact negation closes the else arm")
            .join_focused_if(&marker, split, ids, condition.clone())
            .expect("both discharged siblings should join");
        assert!(joined.is_complete());
        assert_eq!(joined.certificate().steps().len(), 1);
        assert!(matches!(
            joined.certificate().steps(),
            [SimpleProofStep::If { then_proof, else_proof, .. }]
                if then_proof.steps() == [SimpleProofStep::Left]
                    && else_proof.steps() == [SimpleProofStep::Right]
        ));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn execution_frontier_rejects_proposition_closers_transactionally() {
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let root = Proof::for_point_frontier(
        "frontier",
        0,
        &[],
        &[],
        &[],
        &state,
        &state,
        None,
        &program_point_states,
        &surface_propositions,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
        &[],
        &[],
    );
    let fork = root.clone();
    assert!(root.goal().is_none());
    assert!(Arc::ptr_eq(&root.state, &fork.state));
    assert!(Arc::ptr_eq(&root.node, &fork.node));
    for closer in [SimpleProofStep::Assumption, SimpleProofStep::Normalize] {
        let error = fork
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
fn point_witness_refines_existential_transactionally_with_constant_local_work() {
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let variable = Variable(9_000_000);
    let expected = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );
    let goal = Proposition::Exists {
        name: "chosen".to_string(),
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(expected),
    };
    let witness = ProofWitness {
        name: "chosen".to_string(),
        value: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };
    let expected_surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("chosen".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };
    let surface_goal = ClickProposition::Exists {
        c_type: C0Type::Int32,
        name: "chosen".to_string(),
        body: Box::new(expected_surface),
    };
    let instantiated_surface = ClickProposition::Comparison {
        left: witness.value.clone(),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_point_surface_goal(
            "persistent witness",
            0,
            &facts,
            goal.clone(),
            surface_goal.clone(),
            &[],
            &[],
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let wrong_name = SimpleProofStep::Witness(ProofWitness {
            name: "other".to_string(),
            value: ContractExpression::CFragment(CExpression::Value(int32(7))),
        });
        let error = root
            .apply_step(wrong_name)
            .err()
            .expect("a mismatched witness must reject the candidate");
        assert!(error.message().contains("binds `chosen`"), "{error:?}");
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let before = fact_node_allocations();
        let refined = root
            .apply_step(SimpleProofStep::Witness(witness.clone()))
            .expect("the named int32 witness should refine the existential");
        let allocations = fact_node_allocations() - before;
        // The one permitted node rewrites the sole entry of the goal
        // collection; the bound must stay independent of `size` because
        // the witness never touches the persistent fact index.
        assert!(
            allocations <= 1,
            "size {size} witness should not alter the persistent fact index \
             ({allocations} persistent nodes allocated)"
        );
        assert_eq!(
            refined.certificate().steps(),
            &[SimpleProofStep::Witness(witness.clone())]
        );
        assert_eq!(refined.surface_goal(), Some(&instantiated_surface));
        assert!(refined.added_facts().is_empty());
        assert!(!refined.is_complete());
        let completed = refined
            .apply_step(SimpleProofStep::Normalize)
            .expect("the instantiated constant equality should normalize");
        assert!(completed.is_complete());
        assert_eq!(
            completed.certificate().steps(),
            &[
                SimpleProofStep::Witness(witness.clone()),
                SimpleProofStep::Normalize,
            ]
        );
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn universal_intro_binding_is_local_to_its_focused_sibling_goal() {
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test function should parse");
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let binder = "k".to_string();
    let binder_expression = ContractExpression::CFragment(CExpression::Variable(binder.clone()));
    let constant = |value| ContractExpression::CFragment(CExpression::Value(int32(value)));
    let surface_goal = ClickProposition::ForAll {
        c_type: C0Type::Int32,
        name: binder.clone(),
        body: Box::new(ClickProposition::Comparison {
            left: binder_expression.clone(),
            operator: ComparisonOperator::Equal,
            right: binder_expression,
        }),
    };
    let disjunction = ClickProposition::Or(
        Box::new(ClickProposition::Comparison {
            left: constant(0),
            operator: ComparisonOperator::Equal,
            right: constant(0),
        }),
        Box::new(ClickProposition::Comparison {
            left: constant(1),
            operator: ComparisonOperator::Equal,
            right: constant(1),
        }),
    );
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &[],
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("test proposition should lower")
    };
    let kernel_goal = lower(&surface_goal);
    let kernel_disjunction = lower(&disjunction);
    let available = [kernel_disjunction];
    let root = Proof::for_point_surface_goal(
        "goal-local forall binder",
        0,
        &available,
        kernel_goal,
        surface_goal,
        parsed_function.parameters(),
        &[],
        &state,
        &state,
        &program_point_states,
        &surface_propositions,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
        &[],
        &[],
    );
    let (split, _, ids) = root
        .split_focused_cases(disjunction)
        .expect("the exact disjunction should open sibling goals");
    let introduced = split
        .focus(ids[0])
        .expect("the first sibling should be focusable")
        .apply_step(SimpleProofStep::Intro)
        .expect("the universal binder should refine the first sibling");

    let binding_count = |id| match introduced.state.goals.get(id) {
        Some(Goal::Proposition(goal)) => goal.surface_bindings.len(),
        _ => panic!("the split should retain proposition siblings"),
    };
    assert_eq!(binding_count(ids[0]), 1);
    assert_eq!(binding_count(ids[1]), 0);
    assert!(root.state.locals.values.is_empty());
    assert!(introduced.state.locals.values.is_empty());
}

#[test]
fn point_choose_uses_indexed_requirement_and_persistent_local_bindings() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 choose_source(int32 x) {
                requires source: exists (k: int32) { k == x };
                ensures result == x by { assumption(); }
            }
        "#,
    )
    .expect("labeled existential requirement should parse");
    let function_block = &click_file.function_blocks()[0];
    assert_eq!(
        function_block.requirement_label_indices().get("source"),
        Some(&0),
        "the parser should build the requirement-label index once"
    );
    let parsed_function = syntax::parse_function("int32 choose_source(int32 x) { return x; }")
        .expect("test function should parse");
    let state = CState::new().with_local("x", int32(7));
    let arguments = vec![CExpression::Value(int32(7))];
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let source_variable = Variable(9_200_000);
    let source_fact = Proposition::Exists {
        name: "source_value".to_string(),
        var: source_variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(source_variable)),
                Box::new(Bitvector32Term::Constant(7)),
            ),
            true,
        )),
    };
    let goal_variable = Variable(9_200_001);
    let goal = Proposition::Exists {
        name: "witness".to_string(),
        var: goal_variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(goal_variable)),
                Box::new(Bitvector32Term::Constant(7)),
            ),
            true,
        )),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = vec![source_fact.clone()];
        facts.extend((0..size).map(indexed_fact));
        let root = Proof::for_point_goal_with_requirements(
            "persistent choose",
            0,
            &facts,
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            None,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
            function_block.requires(),
            function_block.requirement_label_indices(),
        );
        let retained_root = root.clone();
        let missing = root
            .apply_step(SimpleProofStep::Choose(ProofChoice {
                name: "candidate".to_string(),
                source: ProofFactSource::RequirementLabel("missing".to_string()),
            }))
            .err()
            .expect("an unknown label must reject the candidate");
        assert!(missing.message().contains("unknown requirement label"));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));

        let choice = ProofChoice {
            name: "candidate".to_string(),
            source: ProofFactSource::RequirementLabel("source".to_string()),
        };
        let before = fact_node_allocations();
        let chosen = root
            .apply_step(SimpleProofStep::Choose(choice.clone()))
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
            &[SimpleProofStep::Choose(choice.clone())]
        );
        assert_eq!(chosen.state.locals.values.len(), 1);
        assert!(root.state.locals.values.is_empty());

        let duplicate = chosen
            .apply_step(SimpleProofStep::Choose(choice.clone()))
            .err()
            .expect("a duplicate local name must reject transactionally");
        assert!(duplicate.message().contains("already in scope"));
        assert_eq!(
            chosen.certificate().steps(),
            &[SimpleProofStep::Choose(choice)]
        );

        let completed = chosen
            .apply_step(SimpleProofStep::Witness(ProofWitness {
                name: "witness".to_string(),
                value: ContractExpression::CFragment(CExpression::Variable(
                    "candidate".to_string(),
                )),
            }))
            .expect("witness should resolve the one referenced proof local")
            .apply_step(SimpleProofStep::Assumption)
            .expect("the chosen existential fact should close the refined goal");
        assert!(completed.is_complete());
        assert!(matches!(
            completed.certificate().steps(),
            [
                SimpleProofStep::Choose(_),
                SimpleProofStep::Witness(_),
                SimpleProofStep::Assumption
            ]
        ));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn pure_rewrite_uses_indexed_equality_availability_without_changing_facts() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let equality = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Variable("y".to_string())),
    };
    let unavailable = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("z".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Variable("w".to_string())),
    };
    let values = BTreeMap::from([
        (
            "x".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(9_100_000))),
        ),
        ("y".to_string(), int32(1)),
        (
            "z".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(9_100_001))),
        ),
        ("w".to_string(), int32(3)),
    ]);
    let base_context = PureTheoremContext {
        memory: CMemory::new(),
        values,
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let kernel_equality = lower_pure_theorem_proposition(
        "persistent rewrite",
        &equality,
        &base_context.values,
        &base_context.array_refs,
        &base_context.memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("constant equality should lower");
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(kernel_equality.clone());
        let theorem_context = PureTheoremContext {
            requires: requires.clone(),
            ..base_context.clone()
        };
        let root = Proof::for_pure_surface_goal(
            "persistent rewrite",
            &requires,
            kernel_equality.clone(),
            equality.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let error = root
            .apply_step(SimpleProofStep::Rewrite(unavailable.clone()))
            .err()
            .expect("an unavailable equality must reject the candidate");
        assert!(
            error.message().contains("exact available fact"),
            "{error:?}"
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let step = SimpleProofStep::Rewrite(equality.clone());
        let before = fact_node_allocations();
        let rewritten = root
            .apply_step(step.clone())
            .expect("the exact available equality should rewrite the goal");
        let allocations = fact_node_allocations() - before;
        // The one permitted node rewrites the sole entry of the goal
        // collection; the bound must stay independent of `size` because
        // the rewrite never touches the persistent fact index.
        assert!(
            allocations <= 1,
            "size {size} rewrite should not alter the persistent fact index \
             ({allocations} persistent nodes allocated)"
        );
        assert_eq!(rewritten.certificate().steps(), &[step.clone()]);
        assert!(
            rewritten.surface_goal().is_none(),
            "a surface form that lowers through extra normalization must not be paired with the unnormalized kernel successor"
        );
        assert!(rewritten.added_facts().is_empty());
        assert!(!rewritten.is_complete());
        let complete = rewritten
            .apply_step(SimpleProofStep::Normalize)
            .expect("the rewritten constant equality should normalize");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[step.clone(), SimpleProofStep::Normalize]
        );
        let alternative = root
            .apply_step(step)
            .expect("the ancestor should remain usable for another descendant");
        assert_eq!(alternative.certificate(), rewritten.certificate());
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn surface_rewrite_retains_structural_successor_and_scales() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let variable =
        |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
    let zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
    let comparison =
        |left: ContractExpression, operator: ComparisonOperator, right: ContractExpression| {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            }
        };
    let equality = comparison(variable("x"), ComparisonOperator::Equal, variable("y"));
    let y_zero = comparison(variable("y"), ComparisonOperator::Equal, zero.clone());
    let z_zero = comparison(variable("z"), ComparisonOperator::Equal, zero.clone());
    let goal_surface = ClickProposition::And(
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
    let rewritten_surface = ClickProposition::And(
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
    let values = BTreeMap::from([
        (
            "x".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(9_101_000))),
        ),
        (
            "y".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(9_101_001))),
        ),
        (
            "z".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(9_101_002))),
        ),
    ]);
    let base_context = PureTheoremContext {
        memory: CMemory::new(),
        values,
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let lower = |surface: &ClickProposition| {
        lower_pure_theorem_proposition(
            "persistent structural rewrite",
            surface,
            &base_context.values,
            &base_context.array_refs,
            &base_context.memory,
            &predicate_environment,
            &click_function_environment,
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let rewritten = root
            .apply_step(SimpleProofStep::Rewrite(equality.clone()))
            .expect("the exact equality should produce a checked rewrite successor");
        let closed = rewritten
            .try_simp_closure()
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
                SimpleProofStep::Rewrite(root_equality),
                SimpleProofStep::Have { proof: left, .. },
                SimpleProofStep::Have { proof: right, .. },
                SimpleProofStep::Split,
            ] if root_equality == &equality
                && matches!(left.steps(), [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize])
                && matches!(right.steps(), [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize])
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_extract_uses_persistent_proper_conjunct_membership() {
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(7))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };
    let kernel = lower_point_proposition_with_assumptions(
        &surface,
        &PureFactContext::new(),
        &[],
        &[],
        &state,
        &state,
        None,
        &program_point_states,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("constant equality should lower");

    let merely_top_level = Proof::for_point_goal(
        "top-level is not a proper conjunct",
        0,
        std::slice::from_ref(&kernel),
        kernel.clone(),
        &[],
        &[],
        &state,
        &state,
        &program_point_states,
        &surface_propositions,
        &predicate_environment,
        &click_function_environment,
        &theorem_environment,
        &[],
        &[],
    );
    assert!(
        merely_top_level
            .apply_step(SimpleProofStep::Extract(surface.clone()))
            .is_err(),
        "an independently available fact is not extractable unless it is also a proper conjunct"
    );

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
        available.push(Proposition::And(
            Box::new(indexed_fact(size + 1)),
            Box::new(Proposition::And(
                Box::new(kernel.clone()),
                Box::new(indexed_fact(size + 2)),
            )),
        ));
        let root = Proof::for_point_goal(
            "persistent extract",
            0,
            &available,
            kernel.clone(),
            &[],
            &[],
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let step = SimpleProofStep::Extract(surface.clone());
        let before = fact_node_allocations();
        let extracted = root
            .apply_step(step.clone())
            .expect("the nested proper conjunct should extract");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 32 * logarithmic_height + 128;
        assert!(
            allocations <= allocation_bound,
            "size {size} extract allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        assert_eq!(extracted.certificate().steps(), &[step]);
        assert_eq!(extracted.added_facts(), std::slice::from_ref(&kernel));
        assert!(extracted.is_complete());
    }
}

#[test]
fn implication_extract_uses_indexed_consequent_and_alpha_equivalent_antecedent() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let target_surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(1))),
    };
    let theorem_context = PureTheoremContext {
        memory: CMemory::new(),
        values: BTreeMap::from([(
            "x".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(8_000_000))),
        )]),
        array_refs: BTreeMap::new(),
        requires: Vec::new(),
        surface_requirements: SurfacePropositionMap::default(),
    };
    let target = lower_pure_theorem_proposition(
        "indexed implication extract",
        &target_surface,
        &theorem_context.values,
        &theorem_context.array_refs,
        &theorem_context.memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("target should lower");
    let universal = |variable| Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::Variable(variable)),
            ),
            true,
        )),
    };
    let required_antecedent = universal(Variable(8_100_000));
    let available_antecedent = universal(Variable(8_200_000));
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
            "indexed implication extract",
            &facts,
            target.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let target_key = snapshot_blind_proposition_key(&target);
        assert_eq!(
            root.facts()
                .implications_by_consequent
                .get(&target_key)
                .expect("selected consequent should be indexed")
                .len(),
            1,
            "unrelated implications must not enter the selected bucket"
        );
        let quantified_key = quantified_replay_index_key(&required_antecedent)
            .expect("a universal has an alpha-invariant key");
        assert_eq!(
            root.facts()
                .by_quantified_replay
                .get(&quantified_key)
                .expect("alpha-equivalent antecedent should be indexed")
                .len(),
            1
        );

        let step = SimpleProofStep::Extract(target_surface.clone());
        let before = fact_node_allocations();
        let extracted = root
            .apply_step(step.clone())
            .expect("the alpha-equivalent antecedent should discharge the implication");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 48 * logarithmic_height + 192;
        assert!(
            allocations <= allocation_bound,
            "size {size} implication extract allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        assert_eq!(extracted.certificate().steps(), &[step]);
        assert_eq!(extracted.added_facts(), std::slice::from_ref(&target));
        assert!(extracted.is_complete());

        let missing_antecedent = Proof::for_pure_goal(
            "missing implication antecedent",
            std::slice::from_ref(&selected_implication),
            target.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        assert!(
            missing_antecedent
                .apply_step(SimpleProofStep::Extract(target_surface.clone()))
                .is_err(),
            "an indexed consequent does not bypass its antecedent"
        );
        assert!(missing_antecedent.certificate().steps().is_empty());
    }
}

#[test]
fn point_instantiate_uses_indexed_universal_and_only_named_guards() {
    let parsed_function = syntax::parse_function("int32 selected(int32 x) { return x; }")
        .expect("test function should parse");
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let x_value = CValue::Int32(Bitvector32Term::Variable(Variable(8_700_000)));
    let arguments = vec![CExpression::Value(x_value)];
    let value = |constant| ContractExpression::CFragment(CExpression::Value(int32(constant)));
    let variable =
        |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
    let premise = ClickProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::LessEqual,
        right: value(7),
    };
    let goal_surface = ClickProposition::Comparison {
        left: value(7),
        operator: ComparisonOperator::Equal,
        right: variable("x"),
    };
    let quantified_surface = ClickProposition::ForAll {
        c_type: C0Type::Int32,
        name: "k".to_string(),
        body: Box::new(ClickProposition::Implies(
            Box::new(ClickProposition::Comparison {
                left: variable("x"),
                operator: ComparisonOperator::LessEqual,
                right: variable("k"),
            }),
            Box::new(ClickProposition::Comparison {
                left: variable("k"),
                operator: ComparisonOperator::Equal,
                right: variable("x"),
            }),
        )),
    };
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("test proposition should lower")
    };
    let kernel_premise = lower(&premise);
    let kernel_goal = lower(&goal_surface);
    let kernel_quantified = lower(&quantified_surface);

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut available = (0..size)
            .flat_map(|index| {
                [
                    indexed_fact(index),
                    Proposition::ForAll {
                        var: Variable(9_000_000 + u64::from(index)),
                        sort: Sort::CInt32,
                        body: Box::new(indexed_fact(100_000 + index)),
                    },
                ]
            })
            .collect::<Vec<_>>();
        available.push(kernel_premise.clone());
        available.push(kernel_quantified.clone());
        let root = Proof::for_point_goal(
            "indexed instantiate",
            0,
            &available,
            kernel_goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        if size == 16 {
            let premise_pairs = vec![
                (kernel_quantified.clone(), quantified_surface.clone()),
                (kernel_premise.clone(), premise.clone()),
            ];
            let (selected, certificate_checks) = count_source_certificate_checks(|| {
                root.try_selected_forall_instantiation(&kernel_goal, &premise_pairs)
            });
            let selected =
                selected.expect("the selected universal candidate should close through Proof");
            assert_eq!(
                certificate_checks, 0,
                "universal instantiation planning must not check a candidate certificate"
            );
            assert!(selected.is_complete());
            assert!(matches!(
                selected.certificate().steps(),
                [
                    SimpleProofStep::InstantiateUsing { .. },
                    SimpleProofStep::Assumption
                ]
            ));
        }
        let retained_root = root.clone();
        let key = quantified_replay_index_key(&kernel_quantified)
            .expect("the selected universal should have an alpha key");
        assert_eq!(
            root.facts()
                .by_quantified_replay
                .get(&key)
                .expect("the selected universal should be indexed")
                .len(),
            1,
            "unrelated facts must not enter the selected universal bucket"
        );
        let unfolded_facts = root
            .facts()
            .with_predicate_unfold_fact(kernel_quantified.clone());
        assert_eq!(
            unfolded_facts.predicate_unfolded_universal_facts.len(),
            1,
            "unrelated ambient facts and universals must not enter predicate-unfold search"
        );

        let mut indexed_root = root.clone();
        let mut indexed_state = Arc::unwrap_or_clone(indexed_root.state);
        indexed_state.goals = indexed_state
            .goals
            .with_facts_at(indexed_root.focused, unfolded_facts);
        indexed_root.state = Arc::new(indexed_state);
        let before = fact_node_allocations();
        let selected = indexed_root
            .try_indexed_forall_instantiation()
            .expect("the unfold-owned universal should close without scanning ambient universals");
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
            [
                SimpleProofStep::InstantiateUsing { .. },
                SimpleProofStep::Assumption
            ]
        ));

        let step = SimpleProofStep::InstantiateUsing {
            quantified: quantified_surface.clone(),
            argument: value(7),
            premises: vec![premise.clone()],
        };
        let omitted = SimpleProofStep::InstantiateUsing {
            quantified: quantified_surface.clone(),
            argument: value(7),
            premises: Vec::new(),
        };
        assert!(
            root.apply_step(omitted).is_err(),
            "ambient availability must not discharge an omitted guard"
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let before = fact_node_allocations();
        let instantiated = root
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
        assert_eq!(instantiated.certificate().steps(), &[step.clone()]);
        assert_eq!(
            instantiated.added_facts(),
            std::slice::from_ref(&kernel_goal)
        );
        let completed = instantiated
            .apply_step(SimpleProofStep::Assumption)
            .expect("the specialized exact fact should close by assumption");
        assert!(completed.is_complete());
        assert_eq!(
            completed.certificate().steps(),
            &[step, SimpleProofStep::Assumption]
        );
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn execution_apply_uses_only_named_evidence_and_forks_persistently() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
            }
        "#,
    )
    .expect("test theorem and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = CState::new();
    let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_000_000)));
    let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_000_001)));
    let arguments = vec![CExpression::Value(left.clone())];
    let premise = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let conclusion = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let kernel_premise = lower_point_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &ProgramPointStates::new(),
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the exact premise should lower");
    let kernel_conclusion = lower_point_proposition_with_assumptions(
        &conclusion,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &ProgramPointStates::new(),
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the theorem conclusion should lower");
    let application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: vec![
            ContractExpression::CFragment(CExpression::Value(left)),
            ContractExpression::CFragment(CExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel_premise.clone());
        let replay = TacticReplayState::default();
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&premise, &kernel_premise)
            .expect("the selected premise form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent theorem application",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        assert!(
            root.try_theorem_application(&missing_application)
                .expect("missing execution theorem search should be a bounded miss")
                .is_none(),
            "an unavailable execution theorem premise must not manufacture a descendant"
        );
        let before_query = fact_node_allocations();
        let selected = root
            .select_execution_theorem_application_step(&application)
            .expect("smart search should select one explicit indexed premise");
        assert_eq!(
            fact_node_allocations() - before_query,
            0,
            "size {size} execution theorem selection must not rebuild persistent fact indexes"
        );
        assert_eq!(
            selected,
            SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: vec![premise.clone()],
            }
        );
        let omitted = root
            .apply_step(SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: Vec::new(),
            })
            .err()
            .expect("ambient facts must not discharge an omitted named premise");
        assert!(
            omitted.message().contains("required exact fact"),
            "{omitted:?}"
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let step = selected;
        let before = fact_node_allocations();
        let applied = root
            .apply_step(step.clone())
            .expect("the exact named premise should certify the application");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 32 * logarithmic_height + 128;
        assert!(
            allocations <= allocation_bound,
            "size {size} theorem application allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(applied.certificate().steps(), &[step.clone()]);
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
                .state
                .shares_storage_with(&applied_execution.state),
            "theorem application does not alter the C state"
        );
        assert!(root_execution.function_entry_execution_prerequisites.len() == 0);
        assert!(
            applied_execution
                .function_entry_execution_prerequisites
                .contains(&kernel_conclusion)
        );
        assert_eq!(
            applied_execution
                .last_step_delta
                .function_entry_prerequisites,
            vec![kernel_conclusion.clone()]
        );
        assert_eq!(
            applied_execution
                .last_step_delta
                .function_entry_derivations
                .len(),
            1
        );
        let alternative = root
            .apply_step(step)
            .expect("the retained ancestor should support another checked descendant");
        assert_eq!(alternative.certificate(), applied.certificate());
        assert!(root.certificate().steps().is_empty());
        assert!(applied.facts().contains(&kernel_conclusion));
    }
}

#[test]
fn branch_theorem_search_retains_checked_arm_steps_and_scales() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 choose(int32 left, int32 right, int32 choose_left) {
                immutable;
                ensures reflexive_result: result == result by { assumption(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function(
        "int32 choose(int32 left, int32 right, int32 choose_left) { if (choose_left != 0) { return left; } else { return right; } }",
    )
    .expect("test C function should parse");
    let function = parsed_function.to_kernel_function();
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = CState::new();
    let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_050_000)));
    let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_050_001)));
    let choose_left = CValue::Int32(Bitvector32Term::Variable(Variable(8_050_002)));
    let arguments = vec![
        CExpression::Value(left.clone()),
        CExpression::Value(right.clone()),
        CExpression::Value(choose_left),
    ];
    let premise = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let unavailable_frame_premise = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(right.clone())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(left.clone())),
    };
    let kernel_premise = lower_point_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &ProgramPointStates::new(),
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the exact theorem premise should lower");
    let application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: vec![
            ContractExpression::CFragment(CExpression::Value(left)),
            ContractExpression::CFragment(CExpression::Value(right)),
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
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel_premise.clone());
        let replay = TacticReplayState::default();
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&premise, &kernel_premise)
            .expect("the selected premise form should be recorded");
        let root = Proof::for_execution_frontier(
            "branch theorem search",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                surface_propositions,
                PersistentSequence::default(),
            ),
            pure_facts,
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "choose".to_string(),
                    claim: CProofClaim::Grouped,
                }),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
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
            then_arm
                .try_theorem_application(&missing_application)
                .expect("an unavailable exact theorem premise should be a bounded miss")
                .is_none(),
            "an unavailable theorem premise must not manufacture an arm descendant"
        );

        let before = fact_node_allocations();
        let branches = then_arm
            .try_theorem_application(&application)
            .expect("then arm theorem search should run")
            .expect("then arm theorem search should retain its checked step")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .try_theorem_application(&application)
            .expect("else arm theorem search should run")
            .expect("else arm theorem search should retain its checked step");
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
                [SimpleProofStep::ApplyTheoremUsing {
                    application: retained,
                    premises,
                }] if retained == &application && premises == std::slice::from_ref(&premise)
            ));
        }

        // The cross-arm nested-splice rejection is structural in the
        // sibling form: a scope join produces one direct successor of
        // the arm that opened it, so there is no operation that could
        // publish it into the sibling; the scope provenance regressions
        // pin that law.
        let before_nested = fact_node_allocations();
        let nested_branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .begin_have(premise.clone())
            .expect("the then arm should open a proposition proof")
            .apply_step(SimpleProofStep::Assumption)
            .expect("the root premise should close the then-arm proof")
            .join()
            .expect("the completed proof should advance the then arm")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .begin_have(premise.clone())
            .expect("the else arm should open a proposition proof")
            .apply_step(SimpleProofStep::Assumption)
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
                [SimpleProofStep::Have {
                    proposition: retained,
                    proof,
                }] if retained == &premise
                    && proof.steps() == [SimpleProofStep::Assumption]
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
                    [SimpleProofStep::Step]
                        | [SimpleProofStep::Step]
                        | [SimpleProofStep::Step, SimpleProofStep::Step]
                ),
                "{steps:#?}"
            );
        }
        let terminal = execute_branches
            .join_focused_execution_terminal(&record)
            .expect("the two checked return arms should join as terminal outcomes");
        assert!(matches!(
            terminal.certificate().steps(),
            [SimpleProofStep::If {
                then_proof,
                else_proof,
                ..
            }] if then_proof.steps().len() == 2 && else_proof.steps().len() == 2
        ));
        if size == 16 {
            let retained = terminal.clone();
            assert!(
                terminal
                    .apply_step_at(
                        SimpleProofStep::FrameUsing {
                            region: None,
                            premises: vec![unavailable_frame_premise.clone()],
                        },
                        1,
                        1,
                    )
                    .is_err(),
                "an unavailable frame premise must reject the checked descendant"
            );
            assert!(Arc::ptr_eq(&terminal.state, &retained.state));
            assert_eq!(terminal.certificate(), retained.certificate());
        }
        let framed = terminal
            .try_smart_frame_at(None, 1, 1)
            .expect("terminal frame search should run")
            .expect("the immutable effect should produce a checked frame descendant");
        execute_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before_execute,
        ));
        assert!(matches!(
            framed.certificate().steps(),
            [
                SimpleProofStep::If { .. },
                SimpleProofStep::FrameUsing {
                    region: None,
                    premises,
                },
            ] if premises.is_empty()
        ));
        assert!(root.certificate().steps().is_empty());

        // The framed function exit derives its typed outcome goal set:
        // one sibling goal per returning path in one proof, each owning
        // its path-local result and facts while borrowing the frontier
        // snapshot by identity. The ancestor keeps its single frontier.
        let before_outcomes = fact_node_allocations();
        let (outcomes, outcome_ids) = framed
            .focus_function_outcomes(Arc::new(Vec::new()))
            .expect("the framed terminal execution should expose typed outcome goals");
        outcome_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before_outcomes,
        ));
        assert_eq!(outcome_ids.len(), 2);
        assert_eq!(outcomes.goals().collect::<Vec<_>>(), outcome_ids);
        assert!(!outcomes.is_complete());
        assert_eq!(framed.goals().count(), 1);
        let then_outcome = outcomes
            .focus(outcome_ids[0])
            .expect("the first outcome goal is open");
        let else_outcome = outcomes
            .focus(outcome_ids[1])
            .expect("the second outcome goal is open");
        assert_ne!(
            then_outcome.outcome_result(),
            else_outcome.outcome_result(),
            "distinct return paths own distinct path-local results"
        );
        for outcome in [&then_outcome, &else_outcome] {
            assert!(Arc::ptr_eq(
                outcome
                    .goal_execution()
                    .expect("each outcome borrows the frontier snapshot"),
                framed
                    .goal_execution()
                    .expect("the framed frontier owns its snapshot"),
            ));
        }
        assert!(
            outcomes
                .focus_function_outcomes(Arc::new(Vec::new()))
                .is_err(),
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
fn point_apply_search_uses_indexes_and_retains_its_checked_successor() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test C function should parse");
    let state = CState::new();
    let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_100_000)));
    let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_100_001)));
    let arguments = vec![CExpression::Value(left.clone())];
    let premise = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let conclusion = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let program_point_states = ProgramPointStates::new();
    let kernel_premise = lower_point_proposition_with_assumptions(
        &premise,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &program_point_states,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the exact premise should lower");
    let kernel_conclusion = lower_point_proposition_with_assumptions(
        &conclusion,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &program_point_states,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the theorem conclusion should lower");
    let application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: vec![
            ContractExpression::CFragment(CExpression::Value(left)),
            ContractExpression::CFragment(CExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&premise, &kernel_premise)
        .expect("the selected premise form should be recorded");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(Proposition::And(
            Box::new(kernel_premise.clone()),
            Box::new(indexed_fact(size + 10_000)),
        ));
        let goal = Proposition::And(
            Box::new(kernel_conclusion.clone()),
            Box::new(kernel_premise.clone()),
        );
        let root = Proof::for_point_goal(
            "persistent point theorem search",
            0,
            &facts,
            goal,
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let extracted = root
            .apply_step(SimpleProofStep::Extract(premise.clone()))
            .expect("a checked predecessor should promote the indexed conjunct");
        assert!(
            extracted
                .try_theorem_application(&missing_application)
                .expect("missing point theorem search should be a bounded miss")
                .is_none(),
            "an unavailable point theorem premise must not manufacture a descendant"
        );
        let before_query = fact_node_allocations();
        let step = extracted
            .select_point_theorem_application_step(&application)
            .expect("smart search should select one explicit indexed premise");
        let query_allocations = fact_node_allocations() - before_query;
        assert_eq!(
            query_allocations, 0,
            "size {size} theorem selection must not rebuild persistent fact indexes"
        );
        assert_eq!(
            step,
            SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: vec![premise.clone()],
            }
        );
        let tactics = [
            ProofTactic::Extract(premise.clone()),
            ProofTactic::ApplyTheorem(application.clone()),
            ProofTactic::Simp,
        ];
        let before_apply = fact_node_allocations();
        let complete = root
            .try_linear_smart_script(&tactics)
            .expect("mixed linear search should not fail")
            .expect("extract, smart apply, and simp should close the goal");
        let allocations = fact_node_allocations() - before_apply;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} mixed point script allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps().first(),
            Some(&SimpleProofStep::Extract(premise.clone()))
        );
        assert_eq!(complete.certificate().steps().get(1), Some(&step));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn result_aware_point_apply_scales_with_unrelated_facts() {
    let click_file = crate::lang::click::parse(
        r#"
            theorem result_reflexive(value: int32) {
                ensures value == value by { normalize(); }
            }

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == result by {
                    apply(result_reflexive(result));
                    simp();
                }
                simp();
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
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(8_150_000)),
    ))];
    let result = CValue::Int32(Bitvector32Term::Variable(Variable(8_150_001)));
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let surface_propositions = SurfacePropositionMap::default();
    let kernel_goal = lower_point_proposition_with_assumptions(
        &have.proposition,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        Some(&result),
        &program_point_states,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the result-aware goal should lower");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_point_goal_with_requirements(
            "persistent result-aware theorem search",
            0,
            &facts,
            kernel_goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            None,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
            function_block.requires(),
            function_block.requirement_label_indices(),
        );
        let before = fact_node_allocations();
        let complete = root
            .try_linear_smart_script(have_tactics)
            .expect("result-aware theorem search should not fail")
            .expect("result-aware theorem application and simp should close the goal");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} result-aware point script allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(complete.is_complete());
        assert!(matches!(
            complete.certificate().steps().first(),
            Some(SimpleProofStep::ApplyTheoremUsing { application, premises })
                if application.name == "result_reflexive" && premises.is_empty()
        ));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn result_aware_point_frontier_apply_is_indexed_and_transactional() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 bounded(int32 upper) {
                ensures result <= upper;
            } by {
                execute();
                apply(int32_lt_implies_le(result, upper)) using {
                    result < upper;
                }
                simp();
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
    let (application, surface_premise) = tactics
        .iter()
        .find_map(|tactic| match tactic {
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => Some((application, premises.first()?)),
            _ => None,
        })
        .expect("grouped proof should contain an explicit theorem application");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 bounded(int32 upper) { return upper; }")
        .expect("test C function should parse");
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(8_155_001)),
    ))];
    let result = CValue::Int32(Bitvector32Term::Variable(Variable(8_155_000)));
    let state = CState::new();
    let program_point_states = ProgramPointStates::new();
    let kernel_premise = lower_point_proposition_with_assumptions(
        surface_premise,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        Some(&result),
        &program_point_states,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the result-aware theorem premise should lower");
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(surface_premise, &kernel_premise)
        .expect("the selected premise form should be recorded");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_premise.clone());
        let root = Proof::for_point_frontier(
            "persistent result-aware outcome apply",
            0,
            &facts,
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let missing = root
            .apply_step(SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: Vec::new(),
            })
            .err()
            .expect("ambient availability must not discharge an omitted premise");
        assert!(missing.message().contains("required exact fact"));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let before_query = fact_node_allocations();
        let step = root
            .select_point_theorem_application_step(application)
            .expect("the indexed result-aware premise should be selected");
        assert_eq!(fact_node_allocations() - before_query, 0);
        assert_eq!(
            step,
            SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: vec![surface_premise.clone()],
            }
        );
        let before_apply = fact_node_allocations();
        let applied = root
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
fn point_transport_can_follow_another_checked_step() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let source = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_160_000)),
        ))),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_160_001)),
        ))),
    };
    let extracted = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_160_002)),
        ))),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_160_003)),
        ))),
    };
    let missing = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_160_006)),
        ))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_160_007)),
        ))),
    };
    let program_point_states = ProgramPointStates::new();
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &[],
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
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
        let root = Proof::for_point_frontier(
            "nested result-aware point transport",
            0,
            &facts,
            parsed_function.parameters(),
            &[],
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let refined = root
            .apply_step(SimpleProofStep::Extract(extracted.clone()))
            .expect("the predecessor should advance the proof");
        let retained_refined = refined.clone();
        let rejected = refined.apply_step(SimpleProofStep::TransportUsing {
            source: source.clone(),
            target: missing.clone(),
            premises: Vec::new(),
        });
        assert!(rejected.is_err());
        assert!(Arc::ptr_eq(&refined.state, &retained_refined.state));

        let transport = SimpleProofStep::TransportUsing {
            source: source.clone(),
            target: source.clone(),
            premises: Vec::new(),
        };
        let before = fact_node_allocations();
        let transported = refined
            .apply_step(transport.clone())
            .expect("the exact ambient source should occupy its own checked slot");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 16 * logarithmic_height + 64;
        assert!(
            allocations <= allocation_bound,
            "size {size} point transport allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(
            transported.certificate().steps(),
            &[SimpleProofStep::Extract(extracted.clone()), transport,]
        );
        assert_eq!(transported.added_facts(), &[]);
        assert_eq!(root.certificate().steps(), &[]);
    }
}

#[test]
fn pure_signed_order_simp_builds_its_theorem_path_with_logarithmic_local_updates() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard order theorems should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = CMemory::new();
    let terms = [
        Bitvector32Term::Variable(Variable(8_150_000)),
        Bitvector32Term::Variable(Variable(8_150_001)),
        Bitvector32Term::Variable(Variable(8_150_002)),
        Bitvector32Term::Variable(Variable(8_150_003)),
    ];
    let expression = |term: &Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
    };
    let comparison = |left: usize, operator, right: usize| ClickProposition::Comparison {
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
    let lower = |surface: &ClickProposition| {
        lower_pure_theorem_proposition(
            "persistent signed-order simp",
            surface,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &memory,
            &predicate_environment,
            &click_function_environment,
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.extend(premises.iter().cloned());
        let theorem_context = PureTheoremContext {
            memory: memory.clone(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: surface_requirements.clone(),
        };
        let root = Proof::for_pure_goal(
            "persistent signed-order simp",
            &requires,
            goal.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the typed path should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} signed-order simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::Have { .. },
                SimpleProofStep::ApplyTheoremUsing { .. },
            ]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        // A nested smart `have` must not serialize the goal's ambient
        // copy as `assumption()`: the surface proposition may lower in a
        // different snapshot when expansion is verified from source.
        // Search through a context weakened by only that exact fact and
        // retain the same checked signed-order theorem path on Proof.
        let mut exact_requires = requires.clone();
        exact_requires.push(goal.clone());
        let exact_theorem_context = PureTheoremContext {
            memory: memory.clone(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: exact_requires.clone(),
            surface_requirements: surface_requirements.clone(),
        };
        let exact_root = Proof::for_pure_goal(
            "source-stable persistent signed-order have",
            &exact_requires,
            goal.clone(),
            &exact_theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let scope = exact_root
            .begin_have(surface_goal.clone())
            .expect("the signed-order have should open a nested proof");
        let before = fact_node_allocations();
        let selected = scope
            .try_simp_closure()
            .expect("nested smart search must not exceed its deadline")
            .expect("the exact goal should have an independent theorem path");
        let allocations = fact_node_allocations() - before;
        assert!(
            allocations <= allocation_bound,
            "size {size} exact-goal-excluding have allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(selected.body().is_complete());
        assert!(matches!(
            selected.body().certificate().steps(),
            [
                SimpleProofStep::Have { .. },
                SimpleProofStep::ApplyTheoremUsing { .. },
            ]
        ));
        assert!(exact_root.certificate().steps().is_empty());
    }
}

#[test]
fn pure_equality_refinement_simp_applies_one_rewrite_with_logarithmic_local_updates() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = CMemory::new();
    let value = Bitvector32Term::Variable(Variable(8_174_000));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let equality = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(Bitvector32Term::Constant(2)),
    };
    let goal_surface = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(Bitvector32Term::Subtract(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(2)),
        )),
    };
    let lower = |surface: &ClickProposition| {
        lower_pure_theorem_proposition(
            "persistent equality-refinement simp",
            surface,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &memory,
            &predicate_environment,
            &click_function_environment,
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
            memory: memory.clone(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: requires.clone(),
            surface_requirements: surface_requirements.clone(),
        };
        let root = Proof::for_pure_goal(
            "persistent equality-refinement simp",
            &requires,
            goal.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("one selected equality should refine and close the Proof");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 64 * logarithmic_height + 256;
        assert!(
            allocations <= allocation_bound,
            "size {size} equality-refinement simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn goal_term_equality_rewrite_ignores_unrelated_equality_buckets() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = CMemory::new();
    let selected_term = Bitvector32Term::Variable(Variable(8_174_050));
    let equality_fact = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(selected_term.clone()),
            Box::new(Bitvector32Term::Constant(2)),
        ),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Subtract(
                Box::new(selected_term.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let equality_surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            selected_term.clone(),
        ))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(2))),
    };
    let goal_surface = ClickProposition::Comparison {
        left: ContractExpression::Subtract(
            Box::new(ContractExpression::CFragment(CExpression::Value(
                CValue::Int32(selected_term.clone()),
            ))),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        ),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(1))),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(
                            9_000_000 + u64::from(index),
                        ))),
                        Box::new(Bitvector32Term::Constant(10_000 + index)),
                    ),
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
            memory: memory.clone(),
            values: BTreeMap::new(),
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
            &predicate_environment,
            &click_function_environment,
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
        let closed = root
            .try_indexed_goal_equality_rewrite_closure()
            .expect("the selected equality should rewrite and normalize the goal");
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize]
        ));
    }
}

#[test]
fn goal_term_equality_rewrite_chain_shrinks_independently_of_unrelated_buckets() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = CMemory::new();
    let left = Bitvector32Term::Variable(Variable(8_174_060));
    let right = Bitvector32Term::Variable(Variable(8_174_061));
    let zero = Bitvector32Term::Constant(0);
    let equality = |term: &Bitvector32Term| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(term.clone()), Box::new(zero.clone())),
            true,
        )
    };
    let surface_equality = |term: &Bitvector32Term| ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone()))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Add(
                Box::new(left.clone()),
                Box::new(right.clone()),
            )),
            Box::new(zero.clone()),
        ),
        true,
    );
    let goal_surface = ClickProposition::Comparison {
        left: ContractExpression::Add(
            Box::new(ContractExpression::CFragment(CExpression::Value(
                CValue::Int32(left.clone()),
            ))),
            Box::new(ContractExpression::CFragment(CExpression::Value(
                CValue::Int32(right.clone()),
            ))),
        ),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let selected = [equality(&left), equality(&right)];
    let surfaces = [surface_equality(&left), surface_equality(&right)];

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(
                            9_100_000 + u64::from(index),
                        ))),
                        Box::new(Bitvector32Term::Constant(20_000 + index)),
                    ),
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
            memory: memory.clone(),
            values: BTreeMap::new(),
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
            &predicate_environment,
            &click_function_environment,
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
        let closed = root
            .try_indexed_goal_equality_rewrite_closure()
            .expect("the two selected equalities should shrink and normalize the goal");
        let allocations = fact_node_allocations() - before;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} equality chain allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Normalize
            ]
        ));
    }
}

#[test]
fn point_predecessor_simp_builds_checked_scope_with_logarithmic_local_updates() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let value = Bitvector32Term::Variable(Variable(8_174_100));
    let upper = Bitvector32Term::Variable(Variable(8_174_101));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let equality = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(Bitvector32Term::Constant(1)),
    };
    let upper_bound = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(upper.clone()),
    };
    let goal_surface = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Subtract(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(1)),
        )),
        operator: ComparisonOperator::LessEqual,
        right: expression(upper),
    };
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed point proposition should lower")
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_equality.clone());
        facts.push(kernel_upper_bound.clone());
        let root = Proof::for_point_goal(
            "persistent point predecessor simp",
            0,
            &facts,
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the predecessor search should retain one structured descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} point predecessor simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::Have { .. },
                SimpleProofStep::ApplyTheoremUsing { .. }
            ]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_equality_simp_builds_its_recorded_path_with_logarithmic_local_updates() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let terms = [
        Bitvector32Term::Variable(Variable(8_175_000)),
        Bitvector32Term::Variable(Variable(8_175_001)),
        Bitvector32Term::Variable(Variable(8_175_002)),
        Bitvector32Term::Variable(Variable(8_175_003)),
    ];
    let expression = |term: &Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
    };
    let equal = |left: usize, right: usize| ClickProposition::Comparison {
        left: expression(&terms[left]),
        operator: ComparisonOperator::Equal,
        right: expression(&terms[right]),
    };
    let surfaces = vec![equal(1, 0), equal(1, 2), equal(2, 3)];
    let surface_goal = equal(0, 3);
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed equality should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = lower(&surface_goal);
    let mut surface_propositions = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("the exact point form should be indexed");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend(premises.iter().cloned());
        let root = Proof::for_point_goal(
            "persistent point equality simp",
            0,
            &facts,
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the typed equality path should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} point equality simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Normalize,
            ]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_arithmetic_rewrite_paths_ignore_unrelated_facts() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let left = Bitvector32Term::Variable(Variable(8_176_000));
    let right = Bitvector32Term::Variable(Variable(8_176_001));
    let one = Bitvector32Term::Constant(1);
    let expression = |term: &Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
    };
    let equality = |left: &Bitvector32Term, right: &Bitvector32Term| ClickProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::Equal,
        right: expression(right),
    };
    let surfaces = vec![equality(&left, &one), equality(&one, &right)];
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed equality should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Add(Box::new(left), Box::new(right))),
            Box::new(Bitvector32Term::Constant(2)),
        ),
        true,
    );
    let mut surface_propositions = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("the exact point form should be indexed");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend(premises.iter().cloned());
        let root = Proof::for_point_goal(
            "persistent point arithmetic rewrite simp",
            0,
            &facts,
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the retained equality paths should close the arithmetic goal");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} arithmetic rewrite simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Rewrite(_),
                SimpleProofStep::Normalize,
            ]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_order_simp_builds_its_theorem_path_with_logarithmic_local_updates() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard order theorems should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let terms = [
        Bitvector32Term::Variable(Variable(8_176_000)),
        Bitvector32Term::Variable(Variable(8_176_001)),
        Bitvector32Term::Variable(Variable(8_176_002)),
        Bitvector32Term::Variable(Variable(8_176_003)),
    ];
    let expression = |term: &Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
    };
    let comparison = |left: usize, operator, right: usize| ClickProposition::Comparison {
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
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed signed comparison should lower")
    };
    let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
    let goal = lower(&surface_goal);
    let mut surface_propositions = SurfacePropositionMap::default();
    for (kernel, surface) in premises.iter().zip(&surfaces) {
        surface_propositions
            .record_lowering(surface, kernel)
            .expect("the exact point form should be indexed");
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend(premises.iter().cloned());
        let root = Proof::for_point_goal(
            "persistent point order simp",
            0,
            &facts,
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the typed order path should build one checked point Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 128 * logarithmic_height + 512;
        assert!(
            allocations <= allocation_bound,
            "size {size} point order simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::Have { proof, .. },
                SimpleProofStep::ApplyTheoremUsing { .. },
            ] if matches!(
                proof.steps(),
                [SimpleProofStep::ApplyTheoremUsing { .. }]
            )
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn point_single_premise_arithmetic_simps_retain_indexed_theorem_steps() {
    #[derive(Clone, Copy)]
    enum ArithmeticProofShape {
        Direct,
        ComposedNegatedSuccessor,
        ChainedIncrementUpper,
    }

    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard increment theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let value = Bitvector32Term::Variable(Variable(8_177_000));
    let upper = Bitvector32Term::Variable(Variable(8_177_001));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let premise = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(upper.clone()),
    };
    let definedness_premise = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(Bitvector32Term::Constant(i32::MAX as u32)),
    };
    let positive_premise = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let strictly_positive_premise = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let successor_lower_premise = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(2)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let strong_constant_lower_premise = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(3)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let negated_successor_premise = ClickProposition::Not(Box::new(ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(Bitvector32Term::Constant(2)),
    }));
    let increment_constant_upper_premise = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(Bitvector32Term::Constant(3)),
    };
    let increment_constant_upper_intermediate = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(Bitvector32Term::Constant(5)),
    };
    let surface_bound_goal = ClickProposition::Comparison {
        left: ContractExpression::Add(
            Box::new(expression(value.clone())),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        ),
        operator: ComparisonOperator::LessEqual,
        right: expression(upper.clone()),
    };
    let surface_strict_goal = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::Add(
            Box::new(expression(value.clone())),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        ),
    };
    let surface_defined_goal = ClickProposition::Defined {
        expression: ContractExpression::Add(
            Box::new(expression(value.clone())),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        ),
    };
    let surface_one_plus_defined_goal = ClickProposition::Defined {
        expression: ContractExpression::Add(
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            Box::new(expression(value.clone())),
        ),
    };
    let surface_one_plus_strict_goal = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::Add(
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            Box::new(expression(value.clone())),
        ),
    };
    let surface_nonnegative_goal = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let surface_nonnegative_ge_goal = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(Bitvector32Term::Constant(0)),
    };
    let surface_successor_lower_goal = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(Bitvector32Term::Constant(1)),
    };
    let surface_adjacent_strict_goal = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(1)),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let surface_increment_constant_upper_goal = ClickProposition::Comparison {
        left: ContractExpression::Add(
            Box::new(expression(value.clone())),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        ),
        operator: ComparisonOperator::LessEqual,
        right: expression(Bitvector32Term::Constant(5)),
    };
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed increment proposition should lower")
    };
    let kernel_premise = lower(&premise);
    let kernel_definedness_premise = lower(&definedness_premise);
    let kernel_positive_premise = lower(&positive_premise);
    let kernel_strictly_positive_premise = lower(&strictly_positive_premise);
    let kernel_successor_lower_premise = lower(&successor_lower_premise);
    let kernel_strong_constant_lower_premise = lower(&strong_constant_lower_premise);
    let kernel_negated_successor_premise = lower(&negated_successor_premise);
    let kernel_increment_constant_upper_premise = lower(&increment_constant_upper_premise);
    let goals = [
        (
            lower(&surface_bound_goal),
            "int32_increment_upper_bound",
            "increment bound",
            &premise,
            &kernel_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_strict_goal),
            "int32_increment_strictly_increases",
            "strict increment",
            &premise,
            &kernel_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_defined_goal),
            "int32_increment_below_max_is_defined",
            "increment definedness",
            &definedness_premise,
            &kernel_definedness_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_one_plus_defined_goal),
            "int32_one_plus_below_max_is_defined",
            "one-plus definedness",
            &definedness_premise,
            &kernel_definedness_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_one_plus_strict_goal),
            "int32_one_plus_strictly_increases",
            "one-plus strict increase",
            &definedness_premise,
            &kernel_definedness_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_nonnegative_goal),
            "int32_positive_is_nonnegative",
            "positive to nonnegative",
            &positive_premise,
            &kernel_positive_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_nonnegative_ge_goal),
            "int32_strictly_positive_is_nonnegative",
            "strictly positive to nonnegative",
            &strictly_positive_premise,
            &kernel_strictly_positive_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_adjacent_strict_goal),
            "int32_successor_le_implies_lt",
            "adjacent strict lower bound",
            &successor_lower_premise,
            &kernel_successor_lower_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_nonnegative_goal),
            "int32_le_transitive",
            "constant lower-bound weakening",
            &strong_constant_lower_premise,
            &kernel_strong_constant_lower_premise,
            ArithmeticProofShape::Direct,
        ),
        (
            lower(&surface_successor_lower_goal),
            "int32_ge_transitive",
            "negated strict successor bound",
            &negated_successor_premise,
            &kernel_negated_successor_premise,
            ArithmeticProofShape::ComposedNegatedSuccessor,
        ),
        (
            lower(&surface_increment_constant_upper_goal),
            "int32_increment_upper_bound",
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
            &strictly_positive_premise,
            &kernel_strictly_positive_premise,
        )
        .expect("the exact strictly-positive premise should be indexed");
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

    for (goal, theorem_name, label, surface_premise, kernel_premise, shape) in goals {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(kernel_premise.clone());
            let root = Proof::for_point_goal(
                "persistent point increment-bound simp",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed increment rule should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = match shape {
                ArithmeticProofShape::Direct => 64 * logarithmic_height + 256,
                ArithmeticProofShape::ComposedNegatedSuccessor
                | ArithmeticProofShape::ChainedIncrementUpper => 96 * logarithmic_height + 384,
            };
            assert!(
                allocations <= allocation_bound,
                "size {size} point {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            match shape {
                ArithmeticProofShape::Direct => assert!(
                    matches!(
                        closed.certificate().steps(),
                        [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                            if application.name == theorem_name
                                && premises == std::slice::from_ref(surface_premise)
                    ),
                    "{label} retained unexpected point steps: {:#?}",
                    closed.certificate().steps()
                ),
                ArithmeticProofShape::ComposedNegatedSuccessor => assert!(matches!(
                    closed.certificate().steps(),
                    [
                        SimpleProofStep::Have { proof: first, .. },
                        SimpleProofStep::Have { proof: second, .. },
                        SimpleProofStep::ApplyTheoremUsing { application, .. },
                    ] if matches!(
                        first.steps(),
                        [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                            if application.name == "int32_not_lt_implies_ge"
                                && premises == std::slice::from_ref(surface_premise)
                    ) && matches!(second.steps(), [SimpleProofStep::Normalize])
                        && application.name == theorem_name
                )),
                ArithmeticProofShape::ChainedIncrementUpper => assert!(matches!(
                    closed.certificate().steps(),
                    [
                        SimpleProofStep::ApplyTheoremUsing {
                            application: first,
                            premises: first_premises,
                        },
                        SimpleProofStep::ApplyTheoremUsing {
                            application: second,
                            premises: second_premises,
                        },
                    ] if first.name == "int32_le_lt_transitive"
                        && first_premises == std::slice::from_ref(surface_premise)
                        && second.name == theorem_name
                        && second_premises
                            == std::slice::from_ref(&increment_constant_upper_intermediate)
                )),
            }
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                memory: state.memory().clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted increment-bound simp",
                &facts,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            assert!(
                pure_root.try_restricted_simp_closure(&[]).is_none(),
                "omitting the named premise must reject the restricted candidate"
            );
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            let before_restricted = fact_node_allocations();
            let pure_closed = pure_root
                .try_restricted_simp_closure(std::slice::from_ref(surface_premise))
                .unwrap_or_else(|| {
                    panic!("restricted simp should retain the checked typed {label} rule")
                });
            let restricted_allocations = fact_node_allocations() - before_restricted;
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {label} simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            match shape {
                ArithmeticProofShape::Direct => assert!(matches!(
                    pure_closed.certificate().steps(),
                    [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                        if application.name == theorem_name
                        && premises == std::slice::from_ref(surface_premise)
                )),
                ArithmeticProofShape::ComposedNegatedSuccessor => assert!(matches!(
                    pure_closed.certificate().steps(),
                    [
                        SimpleProofStep::Have { proof: first, .. },
                        SimpleProofStep::Have { proof: second, .. },
                        SimpleProofStep::ApplyTheoremUsing { application, .. },
                    ] if matches!(
                        first.steps(),
                        [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                            if application.name == "int32_not_lt_implies_ge"
                            && premises == std::slice::from_ref(surface_premise)
                    ) && matches!(second.steps(), [SimpleProofStep::Normalize])
                        && application.name == theorem_name
                )),
                ArithmeticProofShape::ChainedIncrementUpper => assert!(matches!(
                    pure_closed.certificate().steps(),
                    [
                        SimpleProofStep::ApplyTheoremUsing {
                            application: first,
                            premises: first_premises,
                        },
                        SimpleProofStep::ApplyTheoremUsing {
                            application: second,
                            premises: second_premises,
                        },
                    ] if first.name == "int32_le_lt_transitive"
                        && first_premises == std::slice::from_ref(surface_premise)
                        && second.name == theorem_name
                        && second_premises
                            == std::slice::from_ref(&increment_constant_upper_intermediate)
                )),
            }
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }
}

#[test]
fn branch_exported_premise_uses_one_selected_anchor_with_logarithmic_work() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard increment theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function = syntax::parse_function("int32 noop(int32 x) { return x; }")
        .expect("test C function should parse");
    let value = Bitvector32Term::Variable(Variable(8_177_900));
    let arguments = vec![CExpression::Value(CValue::Int32(value))];
    let state = CState::new();
    let point = ProgramPointRef {
        region: CodeRegionRef::Statement(0),
        kind: ProgramPointKind::Entry,
    };
    let mut program_point_states = ProgramPointStates::new();
    program_point_states.insert(point.clone(), state.clone());
    let variable = || ContractExpression::CFragment(CExpression::Variable("x".to_string()));
    let constant = |value| ContractExpression::CFragment(CExpression::Value(int32(value)));
    let lower_premise = ClickProposition::Comparison {
        left: variable(),
        operator: ComparisonOperator::GreaterEqual,
        right: constant(0),
    };
    let upper_premise = ClickProposition::Comparison {
        left: variable(),
        operator: ComparisonOperator::LessThan,
        right: constant(i32::MAX as u32),
    };
    let goal_surface = ClickProposition::Comparison {
        left: ContractExpression::Add(Box::new(variable()), Box::new(constant(1))),
        operator: ComparisonOperator::GreaterThan,
        right: constant(0),
    };
    let anchored_lower = surface_with_source_site(&lower_premise, &point)
        .expect("the branch-exported lower bound should admit a point form");
    let anchored_upper = surface_with_source_site(&upper_premise, &point)
        .expect("the continuation upper bound should admit a point form");
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the selected point proposition should lower")
    };
    let kernel_lower = lower(&anchored_lower);
    let kernel_upper = lower(&anchored_upper);
    let goal = lower(&goal_surface);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&anchored_upper, &kernel_upper)
        .expect("only the continuation premise should carry the common point anchor");
    let expected_premises = [anchored_lower, anchored_upper];

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_lower.clone(), kernel_upper.clone()]);
        let root = Proof::for_point_goal(
            "branch-exported premise outcome simp",
            0,
            &facts,
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the selected anchor should retain the two-premise theorem step");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} anchored branch outcome simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                if application.name == "int32_increment_strict_greater_lower_bound"
                    && premises.as_slice() == expected_premises
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn increment_bound_family_retains_two_indexed_theorem_premises() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard increment theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let lower = Bitvector32Term::Variable(Variable(8_178_000));
    let value = Bitvector32Term::Variable(Variable(8_178_001));
    let upper = Bitvector32Term::Variable(Variable(8_178_002));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let lower_premise = ClickProposition::Comparison {
        left: expression(lower.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let upper_premise = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(upper.clone()),
    };
    let increment = |term: Bitvector32Term| {
        ContractExpression::Add(
            Box::new(expression(term)),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        )
    };
    let surface_goals = [
        (
            ClickProposition::Comparison {
                left: expression(lower.clone()),
                operator: ComparisonOperator::LessEqual,
                right: increment(value.clone()),
            },
            "int32_increment_lower_bound",
            "less-equal lower bound",
        ),
        (
            ClickProposition::Comparison {
                left: increment(value.clone()),
                operator: ComparisonOperator::GreaterEqual,
                right: expression(lower.clone()),
            },
            "int32_increment_greater_equal_lower_bound",
            "greater-equal lower bound",
        ),
        (
            ClickProposition::Comparison {
                left: increment(value.clone()),
                operator: ComparisonOperator::GreaterThan,
                right: expression(lower.clone()),
            },
            "int32_increment_strict_greater_lower_bound",
            "strict-greater lower bound",
        ),
        (
            ClickProposition::Comparison {
                left: increment(lower.clone()),
                operator: ComparisonOperator::LessEqual,
                right: increment(value.clone()),
            },
            "int32_increment_preserves_order",
            "incremented order",
        ),
    ];
    let lower_surface = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed increment-lower-bound proposition should lower")
    };
    let kernel_lower = lower_surface(&lower_premise);
    let kernel_upper = lower_surface(&upper_premise);
    let goals = surface_goals
        .iter()
        .map(|(surface, theorem, label)| (lower_surface(surface), *theorem, *label))
        .collect::<Vec<_>>();
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&lower_premise, &kernel_lower)
        .expect("the exact lower premise should be indexed");
    surface_propositions
        .record_lowering(&upper_premise, &kernel_upper)
        .expect("the exact upper premise should be indexed");
    let selected_premises = [lower_premise.clone(), upper_premise.clone()];

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_lower.clone(), kernel_upper.clone()]);
        for (goal, theorem_name, label) in &goals {
            let root = Proof::for_point_goal(
                "persistent point increment-bound-family simp",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed two-premise rule should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                    if application.name == *theorem_name
                        && premises.as_slice() == selected_premises
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                memory: state.memory().clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted increment-bound-family simp",
                &facts,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted in [
                std::slice::from_ref(&lower_premise),
                std::slice::from_ref(&upper_premise),
            ] {
                assert!(
                    pure_root.try_restricted_simp_closure(omitted).is_none(),
                    "omitting either theorem premise must reject the restricted candidate"
                );
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = pure_root
                .try_restricted_simp_closure(&selected_premises)
                .expect("restricted simp should retain the checked two-premise rule");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {label} simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            assert!(matches!(
                pure_closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                    if application.name == *theorem_name
                    && premises.as_slice() == selected_premises
            ));
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }

    let strict_lower_premise = ClickProposition::Comparison {
        left: expression(lower.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let strict_goal_surface = ClickProposition::Comparison {
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_strict_lower.clone(), kernel_upper.clone()]);
        let root = Proof::for_point_goal(
            "persistent point strict increment-bound simp",
            0,
            &facts,
            strict_goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &strict_surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the strict-lower increment path should advance one Proof");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} point strict-lower simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [
                SimpleProofStep::ApplyTheoremUsing { application: first, premises: first_premises },
                SimpleProofStep::ApplyTheoremUsing { application: second, premises: second_premises },
            ] if first.name == "int32_lt_implies_le"
                && first_premises == std::slice::from_ref(&strict_lower_premise)
                && second.name == "int32_increment_strict_greater_lower_bound"
                && second_premises.len() == 2
                && second_premises[1] == upper_premise
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let theorem_context = PureTheoremContext {
            memory: state.memory().clone(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: strict_surface_propositions.clone(),
        };
        let pure_root = Proof::for_pure_goal(
            "persistent restricted strict increment-bound simp",
            &facts,
            strict_goal.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_pure_root = pure_root.clone();
        for omitted in [
            std::slice::from_ref(&strict_lower_premise),
            std::slice::from_ref(&upper_premise),
        ] {
            assert!(pure_root.try_restricted_simp_closure(omitted).is_none());
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
        }
        let before_restricted = fact_node_allocations();
        let pure_closed = pure_root
            .try_restricted_simp_closure(&strict_selected_premises)
            .expect("restricted strict-lower simp should advance one Proof");
        let restricted_allocations = fact_node_allocations() - before_restricted;
        assert!(
            restricted_allocations <= allocation_bound,
            "size {size} restricted strict-lower simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(pure_closed.is_complete());
        assert!(matches!(
            pure_closed.certificate().steps(),
            [
                SimpleProofStep::ApplyTheoremUsing { application: first, .. },
                SimpleProofStep::ApplyTheoremUsing { application: second, .. },
            ] if first.name == "int32_lt_implies_le"
                && second.name == "int32_increment_strict_greater_lower_bound"
        ));
        assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
        assert!(pure_root.certificate().steps().is_empty());
    }
}

#[test]
fn le_and_not_lt_equality_simp_retains_one_indexed_theorem_application() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard equality theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let left = Bitvector32Term::Variable(Variable(8_178_100));
    let right = Bitvector32Term::Variable(Variable(8_178_101));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let less_equal = ClickProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(right.clone()),
    };
    let not_less_than = ClickProposition::Not(Box::new(ClickProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(right.clone()),
    }));
    let equality = ClickProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::Equal,
        right: expression(right),
    };
    let lower_surface = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_less_equal.clone(), kernel_not_less_than.clone()]);
        let root = Proof::for_point_goal(
            "persistent point <=/not-< equality simp",
            0,
            &facts,
            kernel_equality.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the typed equality rule should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} point equality simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                if application.name == "int32_le_and_not_lt_implies_eq"
                    && premises.as_slice() == selected
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let restricted_kernels = selected
            .iter()
            .map(|surface| {
                lower_pure_theorem_proposition(
                    "persistent restricted <=/not-< equality simp",
                    surface,
                    &BTreeMap::new(),
                    &BTreeMap::new(),
                    state.memory(),
                    &predicate_environment,
                    &click_function_environment,
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
            memory: state.memory().clone(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: pure_facts.clone(),
            surface_requirements: surface_propositions.clone(),
        };
        let pure_root = Proof::for_pure_goal(
            "persistent restricted <=/not-< equality simp",
            &pure_facts,
            kernel_equality.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_pure_root = pure_root.clone();
        for omitted in [
            std::slice::from_ref(&less_equal),
            std::slice::from_ref(&not_less_than),
        ] {
            assert!(pure_root.try_restricted_simp_closure(omitted).is_none());
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
        }
        let restricted_derivation = plan_simp_certificate(
            &kernel_equality,
            &assumptions_from_propositions(&restricted_kernels),
        )
        .expect("the restricted equality facts should produce a derivation");
        let SimpEvidence::Derivation(restricted_derivation) = restricted_derivation else {
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
        let recorded = recorded_int32_le_and_not_lt_implies_equality_pairs(
            &restricted_derivation,
            &restricted_pairs,
        )
        .expect("the typed equality evidence should recover both Surface premises");
        let planned = plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
            &kernel_equality,
            &recorded,
            true,
        )
        .expect("the typed equality evidence should select the named theorem");
        let planned_certificate = ProofCertificate::from_proof_tactics(&planned)
            .expect("the named equality theorem should form a simple certificate");
        let planned_closed = pure_root
            .try_planned_linear_script(&planned_certificate.to_proof_tactics())
            .unwrap_or_else(|error| panic!("the named equality plan failed: {error:?}"))
            .expect("the named equality plan should close through checked Proof operations");
        assert!(planned_closed.is_complete());
        let pure_closed = pure_root
            .try_restricted_simp_closure(&selected)
            .expect("restricted simp should retain the checked equality theorem");
        assert!(matches!(
            pure_closed.certificate().steps(),
            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                if application.name == "int32_le_and_not_lt_implies_eq"
                && premises.as_slice() == selected
        ));
        assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
    }
}

#[test]
fn ge_and_not_gt_equality_simp_retains_one_indexed_theorem_application() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard equality theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let left = Bitvector32Term::Variable(Variable(8_178_102));
    let right = Bitvector32Term::Variable(Variable(8_178_103));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let greater_equal = ClickProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(right.clone()),
    };
    let not_greater_than = ClickProposition::Not(Box::new(ClickProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::GreaterThan,
        right: expression(right.clone()),
    }));
    let equality = ClickProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::Equal,
        right: expression(right),
    };
    let lower_surface = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([
            kernel_greater_equal.clone(),
            kernel_not_greater_than.clone(),
        ]);
        let root = Proof::for_point_goal(
            "persistent point >=/not-> equality simp",
            0,
            &facts,
            kernel_equality.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the typed >=/not-> rule should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} point >=/not-> equality simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                if application.name == "int32_ge_and_not_gt_implies_eq"
                    && premises.as_slice() == selected
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn le_and_neq_strict_simp_retains_one_indexed_theorem_application() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard strict-order theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let left = Bitvector32Term::Variable(Variable(8_178_104));
    let right = Bitvector32Term::Variable(Variable(8_178_105));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let less_equal = ClickProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(right.clone()),
    };
    let not_equal = ClickProposition::Not(Box::new(ClickProposition::Comparison {
        left: expression(left.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(right.clone()),
    }));
    let strict = ClickProposition::Comparison {
        left: expression(left),
        operator: ComparisonOperator::LessThan,
        right: expression(right),
    };
    let lower_surface = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.extend([kernel_less_equal.clone(), kernel_not_equal.clone()]);
        let root = Proof::for_point_goal(
            "persistent point <=/!= strict-order simp",
            0,
            &facts,
            kernel_strict.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the typed <=/!= rule should build one checked Proof descendant");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 96 * logarithmic_height + 384;
        assert!(
            allocations <= allocation_bound,
            "size {size} point <=/!= strict-order simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                if application.name == "int32_le_and_neq_implies_lt"
                    && premises.as_slice() == selected
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn symbolic_arithmetic_definedness_retains_two_indexed_theorem_premises() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard symbolic-add theorem should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let value = Bitvector32Term::Variable(Variable(8_178_100));
    let amount = Bitvector32Term::Variable(Variable(8_178_101));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let amount_nonnegative = ClickProposition::Comparison {
        left: expression(amount.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(Bitvector32Term::Constant(0)),
    };
    let headroom = ContractExpression::Subtract(
        Box::new(expression(Bitvector32Term::Constant(i32::MAX as u32))),
        Box::new(expression(amount.clone())),
    );
    let within_headroom = ClickProposition::Comparison {
        left: headroom,
        operator: ComparisonOperator::GreaterEqual,
        right: expression(value.clone()),
    };
    let within_value = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::GreaterEqual,
        right: expression(amount.clone()),
    };
    let surface_add_goal = ClickProposition::Defined {
        expression: ContractExpression::Add(
            Box::new(expression(value.clone())),
            Box::new(expression(amount.clone())),
        ),
    };
    let surface_subtract_goal = ClickProposition::Defined {
        expression: ContractExpression::Subtract(
            Box::new(expression(value.clone())),
            Box::new(expression(amount.clone())),
        ),
    };
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the symbolic arithmetic proposition should lower")
    };
    let kernel_nonnegative = lower(&amount_nonnegative);
    let kernel_headroom = lower(&within_headroom);
    let kernel_within_value = lower(&within_value);
    let cases = [
        (
            lower(&surface_add_goal),
            "int32_nonnegative_add_within_max_is_defined",
            [amount_nonnegative.clone(), within_headroom.clone()],
            [kernel_nonnegative.clone(), kernel_headroom.clone()],
            "symbolic-add",
        ),
        (
            lower(&surface_subtract_goal),
            "int32_nonnegative_subtract_within_value_is_defined",
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
            let root = Proof::for_point_goal(
                "persistent point symbolic arithmetic simp",
                0,
                &facts,
                kernel_goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect(
                    "the typed symbolic arithmetic rule should build one checked Proof descendant",
                );
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                        if application.name == *theorem_name
                            && premises.as_slice() == selected
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                memory: state.memory().clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted symbolic arithmetic simp",
                &facts,
                kernel_goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted in [
                std::slice::from_ref(&selected[0]),
                std::slice::from_ref(&selected[1]),
            ] {
                assert!(pure_root.try_restricted_simp_closure(omitted).is_none());
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = pure_root
                .try_restricted_simp_closure(selected)
                .expect("restricted simp should retain the symbolic arithmetic theorem");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {label} simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(matches!(
                pure_closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                    if application.name == *theorem_name
                        && premises.as_slice() == selected
            ));
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }
}

#[test]
fn selected_disjunction_simp_retains_checked_cases_and_scales() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let value = Bitvector32Term::Variable(Variable(8_178_900));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let equal_zero = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(Bitvector32Term::Constant(0)),
    };
    let equal_one = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(Bitvector32Term::Constant(1)),
    };
    let disjunction =
        ClickProposition::Or(Box::new(equal_zero.clone()), Box::new(equal_one.clone()));
    let surface_goal = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value),
    };
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed proposition should lower")
    };
    let kernel_disjunction = lower(&disjunction);
    let kernel_goal = lower(&surface_goal);
    let mut surface_propositions = SurfacePropositionMap::default();
    surface_propositions
        .record_lowering(&disjunction, &kernel_disjunction)
        .expect("the selected disjunction should be indexed");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(kernel_disjunction.clone());
        let root = Proof::for_point_goal(
            "persistent point disjunction simp",
            0,
            &facts,
            kernel_goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        assert_eq!(
            root.facts().assumptions().disjunction_fact_count(),
            1,
            "unrelated facts must not enter the disjunction candidate index"
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .try_simp_closure()
            .expect("smart search must not exceed its deadline")
            .expect("the selected disjunction should close both checked Proof arms");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 160 * logarithmic_height + 640;
        assert!(
            allocations <= allocation_bound,
            "size {size} disjunction simp allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(closed.is_complete());
        assert!(matches!(
            closed.certificate().steps(),
            [SimpleProofStep::Cases {
                disjunction: retained,
                left_proof,
                right_proof,
            }] if retained == &disjunction
                && matches!(
                    left_proof.steps(),
                    [SimpleProofStep::Rewrite(equality), SimpleProofStep::Normalize]
                        if equality == &equal_zero
                )
                && matches!(
                    right_proof.steps(),
                    [SimpleProofStep::Rewrite(equality), SimpleProofStep::Normalize]
                        if equality == &equal_one
                )
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn surface_structural_simp_retains_recursive_child_proofs_and_scales() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let left_value = Bitvector32Term::Variable(Variable(8_178_910));
    let right_value = Bitvector32Term::Variable(Variable(8_178_911));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let left_positive = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(left_value.clone()),
    };
    let right_positive = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(right_value.clone()),
    };
    let left_nonnegative = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(left_value.clone()),
    };
    let right_nonnegative = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(right_value.clone()),
    };
    let branch_condition = ClickProposition::Comparison {
        left: expression(left_value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(right_value),
    };
    let negative = ClickProposition::Comparison {
        left: expression(left_value.clone()),
        operator: ComparisonOperator::LessThan,
        right: expression(Bitvector32Term::Constant(0)),
    };
    let reflexive = ClickProposition::Comparison {
        left: expression(left_value.clone()),
        operator: ComparisonOperator::Equal,
        right: expression(left_value),
    };
    let conjunction = ClickProposition::And(
        Box::new(left_nonnegative.clone()),
        Box::new(right_nonnegative),
    );
    let disjunction = ClickProposition::Or(Box::new(left_nonnegative.clone()), Box::new(negative));
    let implication =
        ClickProposition::Implies(Box::new(reflexive), Box::new(left_positive.clone()));
    let lower = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let unrelated = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 256 * logarithmic_height + 1024;
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
            let root = Proof::for_point_surface_goal(
                "persistent surface structural simp",
                0,
                &facts,
                lower(surface_goal),
                surface_goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let Some(Goal::Proposition(root_goal)) = root.focused_goal() else {
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
                let arm = split_proof.focus(id).expect("both siblings are open");
                let Some(Goal::Proposition(arm_goal)) = arm.focused_goal() else {
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
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .unwrap_or_else(|| panic!("the {label} should retain its recursive proof"));
            let allocations = fact_node_allocations() - before;
            assert!(
                allocations <= allocation_bound,
                "size {size} {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            let retained_steps = closed.certificate();
            match label {
                "conjunction" => assert!(
                    matches!(
                        retained_steps.steps(),
                        [
                            SimpleProofStep::Have { proof: left, .. },
                            SimpleProofStep::Have { proof: right, .. },
                            SimpleProofStep::Split,
                        ] if matches!(
                            left.steps(),
                            [SimpleProofStep::ApplyTheoremUsing { .. }]
                        ) && matches!(
                            right.steps(),
                            [SimpleProofStep::ApplyTheoremUsing { .. }]
                        )
                    ),
                    "{retained_steps:#?}"
                ),
                "disjunction" => assert!(
                    matches!(
                        retained_steps.steps(),
                        [
                            SimpleProofStep::Have { proof, .. },
                            SimpleProofStep::Left,
                        ] if matches!(
                            proof.steps(),
                            [SimpleProofStep::ApplyTheoremUsing { .. }]
                        )
                    ),
                    "{retained_steps:#?}"
                ),
                "implication" => assert!(
                    matches!(
                        retained_steps.steps(),
                        [SimpleProofStep::Intro, SimpleProofStep::Assumption,]
                    ),
                    "{retained_steps:#?}"
                ),
                _ => unreachable!(),
            }
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }
}

#[test]
fn predecessor_simps_retain_indexed_named_rule_premises() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions = combined_theorem_definitions(&click_file)
        .expect("the standard predecessor theorems should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let parsed_function =
        syntax::parse_function("void noop() {}").expect("test C function should parse");
    let state = CState::new();
    let arguments = Vec::new();
    let program_point_states = ProgramPointStates::new();
    let value = Bitvector32Term::Variable(Variable(8_179_000));
    let bound = Bitvector32Term::Variable(Variable(8_179_001));
    let expression = |term: Bitvector32Term| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
    };
    let predecessor = || {
        ContractExpression::Subtract(
            Box::new(expression(value.clone())),
            Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
        )
    };
    let positive = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessThan,
        right: expression(value.clone()),
    };
    let nonnegative = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(0)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let bounded = ClickProposition::Comparison {
        left: expression(value.clone()),
        operator: ComparisonOperator::LessEqual,
        right: expression(bound.clone()),
    };
    let one_le = ClickProposition::Comparison {
        left: expression(Bitvector32Term::Constant(1)),
        operator: ComparisonOperator::LessEqual,
        right: expression(value.clone()),
    };
    let surface_goals = [
        (
            ClickProposition::Comparison {
                left: expression(Bitvector32Term::Constant(0)),
                operator: ComparisonOperator::LessEqual,
                right: predecessor(),
            },
            "int32_positive_predecessor_is_nonnegative",
            vec![positive.clone()],
            false,
        ),
        (
            ClickProposition::Comparison {
                left: predecessor(),
                operator: ComparisonOperator::LessThan,
                right: expression(value.clone()),
            },
            "int32_positive_predecessor_strictly_decreases",
            vec![positive.clone()],
            false,
        ),
        (
            ClickProposition::Comparison {
                left: predecessor(),
                operator: ComparisonOperator::LessEqual,
                right: expression(bound),
            },
            "int32_nonnegative_predecessor_upper_bound",
            vec![nonnegative.clone(), bounded.clone()],
            false,
        ),
        (
            ClickProposition::Comparison {
                left: expression(Bitvector32Term::Constant(0)),
                operator: ComparisonOperator::LessEqual,
                right: predecessor(),
            },
            "int32_positive_predecessor_is_nonnegative",
            vec![one_le.clone()],
            true,
        ),
        (
            ClickProposition::Comparison {
                left: predecessor(),
                operator: ComparisonOperator::LessThan,
                right: expression(value.clone()),
            },
            "int32_positive_predecessor_strictly_decreases",
            vec![one_le.clone()],
            true,
        ),
    ];
    let lower_surface = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the fixed predecessor proposition should lower")
    };
    let kernel_positive = lower_surface(&positive);
    let kernel_nonnegative = lower_surface(&nonnegative);
    let kernel_bounded = lower_surface(&bounded);
    let kernel_one_le = lower_surface(&one_le);
    let goals = surface_goals
        .iter()
        .map(|(surface, theorem, selected, nested)| {
            (lower_surface(surface), *theorem, selected.clone(), *nested)
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

    for size in [16_u32, 64, 256, 1024, 4096] {
        let unrelated_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        for (goal, theorem_name, selected, nested) in &goals {
            let mut facts = unrelated_facts.clone();
            facts.extend(selected.iter().map(&lower_surface));
            let root = Proof::for_point_goal(
                "persistent point predecessor simp",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .unwrap_or_else(|| {
                    panic!(
                        "the typed predecessor rule {theorem_name} (nested={nested}) should build a checked Proof descendant"
                    )
                });
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point {theorem_name} allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            if *nested {
                assert!(matches!(
                    closed.certificate().steps(),
                    [
                        SimpleProofStep::Have { proof, .. },
                        SimpleProofStep::ApplyTheoremUsing { application, premises },
                    ] if application.name == *theorem_name
                        && premises.len() == 1
                        && matches!(
                            proof.steps(),
                            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                                if application.name == "int32_successor_le_implies_lt"
                                && premises == selected
                        )
                ));
            } else {
                assert!(matches!(
                    closed.certificate().steps(),
                    [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                        if application.name == *theorem_name && premises == selected
                ));
            }
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                memory: state.memory().clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted predecessor simp",
                &facts,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
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
                    pure_root.try_restricted_simp_closure(&omitted).is_none(),
                    "omitting a theorem premise must reject the restricted candidate"
                );
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = pure_root
                .try_restricted_simp_closure(selected)
                .expect("restricted simp should retain the checked predecessor rule");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted {theorem_name} allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            if *nested {
                assert!(matches!(
                    pure_closed.certificate().steps(),
                    [
                        SimpleProofStep::Have { proof, .. },
                        SimpleProofStep::ApplyTheoremUsing { application, premises },
                    ] if application.name == *theorem_name
                        && premises.len() == 1
                        && matches!(
                            proof.steps(),
                            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                                if application.name == "int32_successor_le_implies_lt"
                                && premises == selected
                        )
                ));
            } else {
                assert!(matches!(
                    pure_closed.certificate().steps(),
                    [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                        if application.name == *theorem_name && premises == selected
                ));
            }
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }
}

#[test]
fn pure_apply_search_instantiates_requirements_and_retains_its_successor() {
    let click_file = crate::lang::click::parse("")
        .expect("an empty source should still admit the standard theorem prelude");
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_definitions =
        combined_theorem_definitions(&click_file).expect("standard theorem prelude should load");
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let memory = CMemory::new();
    let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_200_000)));
    let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_200_001)));
    let premise = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let conclusion = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(left.clone())),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::CFragment(CExpression::Value(right.clone())),
    };
    let kernel_premise = lower_pure_theorem_proposition(
        "persistent pure theorem search",
        &premise,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the exact pure premise should lower");
    let kernel_conclusion = lower_pure_theorem_proposition(
        "persistent pure theorem search",
        &conclusion,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &memory,
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the pure theorem conclusion should lower");
    let application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: vec![
            ContractExpression::CFragment(CExpression::Value(left)),
            ContractExpression::CFragment(CExpression::Value(right)),
        ],
    };
    let missing_application = TheoremApplication {
        name: "int32_lt_implies_le".to_string(),
        arguments: application.arguments.iter().cloned().rev().collect(),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
        requires.push(kernel_premise.clone());
        let theorem_context = PureTheoremContext {
            memory: memory.clone(),
            values: BTreeMap::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        assert!(
            root.try_theorem_application(&missing_application)
                .expect("missing pure theorem search should be a bounded miss")
                .is_none(),
            "an unavailable pure theorem premise must not manufacture a descendant"
        );
        let missing = root
            .select_pure_theorem_application_step(&missing_application)
            .err()
            .expect("an unavailable instantiated requirement must reject the candidate");
        assert!(missing.message().contains("required exact fact"));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let before_query = fact_node_allocations();
        let step = root
            .select_pure_theorem_application_step(&application)
            .expect("smart pure search should select the indexed source requirement");
        let query_allocations = fact_node_allocations() - before_query;
        assert_eq!(
            query_allocations, 0,
            "size {size} pure theorem selection must not rebuild persistent fact indexes"
        );
        assert_eq!(
            step,
            SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: vec![premise.clone()],
            }
        );
        let before_script = fact_node_allocations();
        let complete = root
            .try_linear_smart_script(&[
                ProofTactic::ApplyTheorem(application.clone()),
                ProofTactic::Simp,
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
        assert_eq!(complete.certificate().steps().first(), Some(&step));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
    }
}

#[test]
fn execution_unfold_forks_persistently_and_ignores_unrelated_facts() {
    let click_file = crate::lang::click::parse(
        r#"
            predicate selected(x: int32) { x == x }
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
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
    let function_environment = CExecutionEnvironment::new();
    let state = CState::new();
    let argument = CExpression::Value(CValue::Int32(Bitvector32Term::Constant(7)));
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let arguments = vec![argument.clone()];
    let surface = ClickProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: vec![ContractExpression::CFragment(argument)],
    };
    let predicate = Proposition::Predicate {
        name: "selected".to_string(),
        arguments: vec![
            Term::CState(state.clone()),
            Term::CValue(CValue::Int32(Bitvector32Term::Constant(7))),
        ],
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(predicate.clone());
        let replay = TacticReplayState::default();
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&surface, &predicate)
            .expect("the selected predicate form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent unfold",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let successor = root
            .apply_step(SimpleProofStep::UnfoldPredicate("selected".to_string()))
            .expect("the exact selected predicate should unfold");
        let allocations = fact_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 32 * logarithmic_height + 128;
        assert!(
            allocations <= allocation_bound,
            "size {size} unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
        );

        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert_eq!(root.facts().to_vec().len(), size as usize + 1);
        assert_eq!(root.certificate().steps(), &[]);
        assert_eq!(
            successor.certificate().steps(),
            &[SimpleProofStep::UnfoldPredicate("selected".to_string())]
        );
        assert!(successor.facts().to_vec().len() > root.facts().to_vec().len());
        let root_execution = root.execution().expect("root execution state");
        let successor_execution = successor.execution().expect("successor execution state");
        assert!(
            root_execution
                .state
                .shares_storage_with(&successor_execution.state),
            "unfold does not alter the C frontier"
        );
        assert!(
            root_execution
                .replay
                .proof_certificate_builder
                .shares_storage_with(&successor_execution.replay.proof_certificate_builder),
            "unfold does not copy unrelated certificate history"
        );
        assert!(
            root_execution
                .effect_facts
                .shares_storage_with(&successor_execution.effect_facts),
            "unfold does not copy unrelated effect history"
        );

        assert!(
            successor_execution
                .unfolded_predicates
                .contains(&"selected".to_string())
        );
        assert!(successor.facts().to_vec().len() > size as usize + 1);
    }
}

#[test]
fn execution_resource_observation_is_retained_transactional_and_logarithmic() {
    let click_file = crate::lang::click::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                views marker(x);
                immutable;
                ensures returns_x: result == x;
            } by {
                observe(marker(x));
                execute();
                frame();
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement.inner() {
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
    let function = parsed_function.to_kernel_function();
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let empty_state = CState::new();
    let lowered = lower_resource_clause(
        &resource,
        parsed_function.parameters(),
        &arguments,
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
                TacticReplayState::default(),
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let observed = root
            .apply_step(SimpleProofStep::ObserveResource(resource.clone()))
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
            &[SimpleProofStep::ObserveResource(resource.clone())]
        );
        assert!(!observed.added_facts().is_empty());
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(
            root.apply_step(SimpleProofStep::ObserveResource(missing))
                .is_err()
        );
        assert!(root.certificate().steps().is_empty());
        assert_eq!(root.facts().to_vec().len(), size as usize);
    }
}

#[test]
fn execution_resource_unfold_is_retained_transactional_and_logarithmic() {
    let click_file = crate::lang::click::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                owns marker(x);
                immutable;
                ensures returns_x: result == x;
            } by {
                unfold(marker(x));
                execute();
                frame();
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement.inner() {
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
    let function = parsed_function.to_kernel_function();
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let empty_state = CState::new();
    let lowered = lower_resource_clause(
        &resource,
        parsed_function.parameters(),
        &arguments,
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
                TacticReplayState::default(),
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let unfolded = root
            .apply_step(SimpleProofStep::UnfoldResource(resource.clone()))
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
            &[SimpleProofStep::UnfoldResource(resource.clone())]
        );
        assert!(!unfolded.added_facts().is_empty());
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(
            root.apply_step(SimpleProofStep::UnfoldResource(missing))
                .is_err()
        );
        assert!(root.certificate().steps().is_empty());
        assert_eq!(root.facts().to_vec().len(), size as usize);
    }
}

#[test]
fn execution_resource_fold_is_retained_transactional_and_logarithmic() {
    let click_file = crate::lang::click::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "identity.c";
            int32 identity(int32 x) {
                owns marker(x);
                immutable;
                ensures returns_x: result == x;
            } by {
                unfold(marker(x));
                fold(marker(x));
                execute();
                frame();
            }
        "#,
    )
    .expect("test resource and function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement.inner() {
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
    let function = parsed_function.to_kernel_function();
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let empty_state = CState::new();
    let lowered = lower_resource_clause(
        &resource,
        parsed_function.parameters(),
        &arguments,
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
                TacticReplayState::default(),
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
            ExecutionProofConstants::default(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let unfolded = root
            .apply_step(SimpleProofStep::UnfoldResource(resource.clone()))
            .expect("the owned marker resource should unfold before folding");
        let retained_unfolded = unfolded.clone();
        let before = fact_node_allocations();
        let folded = unfolded
            .apply_step(SimpleProofStep::FoldResource(resource.clone()))
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
                SimpleProofStep::UnfoldResource(resource.clone()),
                SimpleProofStep::FoldResource(resource.clone()),
            ]
        );
        assert!(folded.added_facts().is_empty());
        assert!(Arc::ptr_eq(&unfolded.state, &retained_unfolded.state));

        let mut missing = resource.clone();
        let ResourceClause::Declared { name, .. } = &mut missing else {
            panic!("the marker resource should be declared");
        };
        *name = "missing_marker".to_string();
        assert!(
            unfolded
                .apply_step(SimpleProofStep::FoldResource(missing))
                .is_err()
        );
        assert_eq!(
            unfolded.certificate().steps(),
            &[SimpleProofStep::UnfoldResource(resource.clone())]
        );
    }
}

#[test]
fn execution_open_scope_owns_entry_body_and_close_transactionally() {
    let click_file = crate::lang::click::parse(
        r#"
            resource marker(x: int32) {
                fact x == x;
            }
            verifying "two_steps.c";
            int32 two_steps(int32 x) {
                owns marker(x);
                immutable;
                ensures returns_x: result == x;
            } by {
                open(marker(x)) { step(); }
                step();
                frame();
            }
        "#,
    )
    .expect("test resource scope should parse");
    let function_block = &click_file.function_blocks()[0];
    let resource = function_block
        .requires()
        .iter()
        .find_map(|requirement| match requirement.inner() {
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
    let function = parsed_function.to_kernel_function();
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let empty_state = CState::new();
    let lowered = lower_resource_clause(
        &resource,
        parsed_function.parameters(),
        &arguments,
        empty_state.memory(),
    )
    .expect("the owned marker resource should lower");
    let state =
        empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));
    let reflexive = ClickProposition::Comparison {
        left: ContractExpression::CBinding("x".to_string()),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CBinding("x".to_string()),
    };
    let _exposed_reflexive = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
    };

    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = Proof::for_execution_frontier(
            "persistent open scope",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                TacticReplayState::default(),
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let scope = root
            .begin_open(resource.clone(), 0)
            .expect("the held marker should open");
        let rejected = scope
            .begin_have(reflexive.clone())
            .expect("the open scope should begin a rejected proposition subproof");
        assert!(rejected.apply_step(SimpleProofStep::Step).is_err());
        assert!(rejected.body().certificate().steps().is_empty());
        let nested = scope
            .begin_have(reflexive.clone())
            .expect("the open scope should begin a proposition subproof")
            .apply_step(SimpleProofStep::Assumption)
            .expect("the exposed marker fact should close the nested proof");
        let scope = scope
            .join_nested(nested)
            .expect("the checked have should advance the open scope");
        let scope = scope
            .apply_step(SimpleProofStep::Step)
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
            &[SimpleProofStep::Open {
                resource: resource.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![
                    SimpleProofStep::Have {
                        proposition: reflexive.clone(),
                        proof: Box::new(ProofCertificate::from_steps(vec![
                            SimpleProofStep::Assumption,
                        ])),
                    },
                    SimpleProofStep::Step,
                ])),
            }]
        );
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let sibling_scope = root
            .begin_open(resource.clone(), 0)
            .expect("the retained root should open a sibling scope");
        let sibling_nested = sibling_scope
            .begin_have(reflexive.clone())
            .expect("the sibling should begin its own nested proof")
            .apply_step(SimpleProofStep::Assumption)
            .expect("the sibling nested proof should close");
        let unrelated_scope = root
            .begin_open(resource.clone(), 0)
            .expect("the retained root should open an unrelated scope");
        assert!(unrelated_scope.join_nested(sibling_nested).is_err());
        assert!(unrelated_scope.body().certificate().steps().is_empty());
        assert!(
            closed
                .execution()
                .is_some_and(|execution| !execution.frontier.is_at_function_exit())
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
            .apply_step(SimpleProofStep::Step)
            .expect("the terminal scope should cross its assignment")
            .apply_step(SimpleProofStep::Step)
            .expect("the terminal scope should cross its return")
            .join()
            .expect("an exit-reaching open should defer its close");
        let terminal_execution = terminal
            .execution()
            .expect("the terminal open retains execution state");
        assert!(terminal_execution.frontier.is_at_function_exit());
        assert_eq!(terminal_execution.replay.post_execution_tactics.len(), 1);
        assert_eq!(
            terminal.certificate().steps(),
            &[SimpleProofStep::Open {
                resource: resource.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![
                    SimpleProofStep::Step,
                    SimpleProofStep::Step,
                ])),
            }]
        );
    }
}

#[test]
fn execution_transport_forks_without_copying_unrelated_state() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
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
    let function_environment = CExecutionEnvironment::new();
    let state = CState::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(7))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(7))),
    };
    let kernel = lower_point_proposition_with_assumptions(
        &surface,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &ProgramPointStates::new(),
        &predicate_environment,
        &click_function_environment,
    )
    .expect("constant equality should lower at the execution point");

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel.clone());
        let replay = TacticReplayState::default();
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&surface, &kernel)
            .expect("the source form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent transport",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let step = SimpleProofStep::TransportUsing {
            source: surface.clone(),
            target: surface.clone(),
            premises: vec![surface.clone()],
        };
        let successor = root
            .apply_step(step.clone())
            .expect("an exact identity transport should succeed");

        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert_eq!(root.certificate().steps(), &[]);
        assert_eq!(successor.certificate().steps(), &[step]);
        assert!(successor.added_facts().is_empty());
        let root_execution = root.execution().expect("root execution state");
        let successor_execution = successor.execution().expect("successor execution state");
        assert!(
            root_execution
                .state
                .shares_storage_with(&successor_execution.state),
            "transport does not alter the C state"
        );
        assert!(
            root_execution
                .replay
                .proof_certificate_builder
                .shares_storage_with(&successor_execution.replay.proof_certificate_builder),
            "transport does not copy unrelated certificate history"
        );
        assert!(
            root_execution
                .effect_facts
                .shares_storage_with(&successor_execution.effect_facts),
            "transport does not copy unrelated effect history"
        );
        assert_eq!(
            root_execution.surface_propositions, successor_execution.surface_propositions,
            "an identity transport does not change the recorded surface lowerings"
        );
    }
}

#[test]
fn execution_transport_search_returns_checked_successors_and_scales() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 choose_second(int32 first, int32 second) {
                ensures returns_second: result == second by { assumption(); }
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
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let state = CState::new();
    let arguments = vec![CExpression::Value(int32(3)), CExpression::Value(int32(5))];
    let term = |variable| {
        ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(variable)),
        )))
    };
    let source = ClickProposition::Comparison {
        left: term(8_170_000),
        operator: ComparisonOperator::LessThan,
        right: term(8_170_001),
    };
    let missing = ClickProposition::Comparison {
        left: term(8_170_002),
        operator: ComparisonOperator::Equal,
        right: term(8_170_003),
    };
    let kernel_source = lower_point_proposition_with_assumptions(
        &source,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &ProgramPointStates::new(),
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the exact transport source should lower");

    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(kernel_source.clone());
        let replay = TacticReplayState::default();
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&source, &kernel_source)
            .expect("the selected source form should be recorded");
        let root = Proof::for_execution_frontier(
            "persistent transport search",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let progressed = root
            .apply_step(SimpleProofStep::Step)
            .expect("the meaningful assignment should advance the execution Proof");
        if size == 16 {
            let retained = progressed.clone();
            let rejected = progressed
                .try_execution_fact_transport(&source, &missing)
                .expect("a bounded rejected transport search should remain prompt");
            assert!(
                rejected.is_none(),
                "an unrelated target must not be manufactured by transport search"
            );
            assert!(Arc::ptr_eq(&progressed.state, &retained.state));
            assert!(matches!(
                progressed.certificate().steps(),
                [SimpleProofStep::Step]
            ));
        }

        let before = fact_node_allocations();
        let transported = progressed
            .try_execution_fact_transport(&source, &source)
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
                SimpleProofStep::Step,
                SimpleProofStep::TransportUsing {
                    source: retained_source,
                    target,
                    premises,
                },
            ] if retained_source == &source
                && target == &source
                && premises == std::slice::from_ref(&source)
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
fn smart_local_assignment_selection_ignores_unrelated_proof_facts() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 set_one(int32 x) {
                ensures returns_one: result == 1 by { assumption(); }
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
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let mut samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());

    for size in [16_u32, 64, 256, 1024, 4096] {
        let replay = TacticReplayState::default();
        let root = Proof::for_execution_frontier(
            "indexed local assignment",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let selected = root
            .try_indexed_statement_step()
            .expect("indexed assignment selection should remain available")
            .expect("unrelated facts should not force mutable planning");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        assert!(matches!(
            selected.certificate().steps(),
            [SimpleProofStep::Step]
        ));
        assert_eq!(selected.facts().to_vec(), root.facts().to_vec());
        assert!(
            !selected
                .execution()
                .expect("assignment successor retains execution")
                .frontier
                .is_at_function_exit()
        );
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let logarithmic_bound = base_allocations + 8 * (height - base_height);
        assert!(
            allocations <= logarithmic_bound,
            "size {size} assignment selection allocated {allocations} persistent nodes (bound {logarithmic_bound})"
        );
    }
}

#[test]
fn smart_store_selection_uses_only_statement_name_indexes() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 write_in_bounds(int32 p[], int32 i, int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires i >= 0;
                requires i < n;
                requires loadable(p[0..n]);
                consumes p[0..n];
                mutable p[0..n] by { execute(); frame(); }
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
    let function_environment = CExecutionEnvironment::new();
    let (state, arguments, base_facts, base_surfaces) = initial_claim_context(
        function_block,
        &parsed_function,
        &resource_environment,
        &predicate_environment,
        &click_function_environment,
        "indexed store selection",
    )
    .expect("the resource-backed claim context should initialize");
    let mut samples = Vec::new();

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = base_facts.clone();
        let mut surface_propositions = base_surfaces.clone();
        for index in 0..size {
            let fact = indexed_fact(index + 10_000);
            let surface = ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Variable(format!(
                    "unrelated_{index}"
                ))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(0))),
            };
            surface_propositions
                .record_lowering(&surface, &fact)
                .expect("the unrelated surface fact should be indexed");
            pure_facts.push(fact);
        }
        let replay = TacticReplayState::default();
        let root = Proof::for_execution_frontier(
            "indexed store selection",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let selected = root
            .try_indexed_execute_step()
            .expect("indexed store selection should remain available")
            .expect("the statement-local bounds and resource should prove the store");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let certificate = selected.certificate();
        // A bare `step()` names no premise: the statement runs in the
        // whole context and selection cannot leak an unrelated fact.
        let [SimpleProofStep::Step] = certificate.steps() else {
            panic!(
                "the selected store should retain one bare statement step: {:#?}",
                certificate.steps()
            );
        };
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let logarithmic_bound = base_allocations + 24 * (height - base_height);
        assert!(
            allocations <= logarithmic_bound,
            "size {size} indexed store selection allocated {allocations} persistent nodes (bound {logarithmic_bound})"
        );
    }
}

#[test]
fn checked_statement_step_ignores_unrelated_proof_facts() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 constant(int32 x) {
                ensures returns_one: result == 1 by { assumption(); }
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
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut samples = Vec::new();

    for size in [16_u32, 64, 256, 1024, 4096] {
        let replay = TacticReplayState::default();
        let root = Proof::for_execution_frontier(
            "persistent statement step",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let retained_root = root.clone();
        // A bare step runs in the whole context: unrelated ambient facts
        // neither block it nor enter its certificate.
        let stepped = root
            .try_indexed_statement_step()
            .expect("the bare statement step should remain available")
            .expect("unrelated ambient facts must not block the bare step");
        assert!(matches!(
            stepped.certificate().steps(),
            [SimpleProofStep::Step]
        ));
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        let marked = root
            .apply_step(SimpleProofStep::Mark("candidate".to_string()))
            .expect("a fresh proof mark should produce a checked descendant");
        assert!(matches!(
            marked.certificate().steps(),
            [SimpleProofStep::Mark(name)] if name == "candidate"
        ));
        let duplicate = marked
            .apply_step(SimpleProofStep::Mark("candidate".to_string()))
            .err()
            .expect("a duplicate mark must reject the candidate");
        assert!(duplicate.message().contains("duplicate proof mark"));
        assert!(matches!(
            marked.certificate().steps(),
            [SimpleProofStep::Mark(name)] if name == "candidate"
        ));
        let before = fact_node_allocations();
        let completed = root
            .apply_step(SimpleProofStep::Step)
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
                .frontier
                .is_at_function_exit()
        );
        assert!(matches!(
            completed.certificate().steps(),
            [SimpleProofStep::Step]
        ));
        let alternative = root
            .apply_step(SimpleProofStep::Step)
            .expect("the retained ancestor should support another checked descendant");
        assert_eq!(alternative.certificate(), completed.certificate());
        let root_execution = root.execution().expect("root execution state");
        let completed_execution = completed
            .execution()
            .expect("statement successor retains execution state");
        assert!(
            root_execution
                .state
                .shares_nonlocal_storage_with(&completed_execution.state),
            "a return step should not copy unchanged memory, resources, or populations"
        );
        assert!(completed.is_at_function_exit());
        assert!(matches!(
            completed.certificate().steps(),
            [SimpleProofStep::Step]
        ));
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
fn close_invariants_is_a_transactional_constant_local_proof_step() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 loop_region(int32 x) {
                ensures unchanged: result == x by { assumption(); }
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
    let function_environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());

    for size in [16_u32, 64, 256, 1024, 4096] {
        let make_root = |loop_invariant_region: bool| {
            let replay = TacticReplayState::default();
            let mut frontier = ExecutionFrontier::default();
            if loop_invariant_region {
                frontier.region = ExecutionRegionKind::LoopBody;
            }
            Proof::for_execution_frontier(
                "persistent close invariants",
                0,
                ExecutionProofState::at_entry(
                    CState::new(),
                    replay,
                    frontier,
                    ProgramPointStates::new(),
                    SurfacePropositionMap::default(),
                    PersistentSequence::default(),
                ),
                (0..size).map(indexed_fact).collect(),
                ExecutionProofConstants::default(),
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            )
        };

        let outside_loop = make_root(false);
        assert!(
            outside_loop
                .apply_step(SimpleProofStep::CloseInvariants)
                .is_err(),
            "the step is restricted to loop-region proofs"
        );
        assert!(outside_loop.certificate().steps().is_empty());

        let root = make_root(true);
        let retained_root = root.clone();
        let before = fact_node_allocations();
        let closed = root
            .apply_step(SimpleProofStep::CloseInvariants)
            .expect("the first close should produce a checked descendant");
        // The one permitted node rewrites the sole goal's execution
        // snapshot in the persistent goal collection; the bound stays
        // independent of ambient fact count.
        assert!(fact_node_allocations() - before <= 1);
        assert!(Arc::ptr_eq(&root.state, &retained_root.state));
        assert!(root.certificate().steps().is_empty());
        assert_eq!(
            closed.certificate().steps(),
            &[SimpleProofStep::CloseInvariants]
        );
        let execution = closed
            .execution()
            .expect("the successor retains execution state");
        assert!(execution.region_invariants_closed);
        assert!(
            execution.invariant_closer_step.is_none(),
            "source timing metadata is attached only at the replay adapter boundary"
        );
        assert!(closed.apply_step(SimpleProofStep::CloseInvariants).is_err());
        assert_eq!(
            closed.certificate().steps(),
            &[SimpleProofStep::CloseInvariants]
        );
    }
}

#[test]
fn proof_condition_split_filters_conflicts_without_rebuilding_facts() {
    let symbolic = Variable(50_000);
    let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(symbolic)));
    let condition = CExpression::LessThan(
        Box::new(CExpression::Variable("x".to_string())),
        Box::new(CExpression::Value(int32(0))),
    );
    let empty = ProofFacts::default();
    let unconstrained = certified_proof_condition_transitions(
        &state,
        &empty,
        &condition,
        "persistent condition split",
    )
    .expect("a symbolic comparison should expose both paths");
    assert_eq!(unconstrained.len(), 2);
    let rejected_path_fact = unconstrained[0]
        .path_facts
        .first()
        .expect("a symbolic branch path should carry its condition fact")
        .clone();
    let selecting_fact = opposite_atomic_fact(&rejected_path_fact);

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
        available.push(selecting_fact.clone());
        let facts = ProofFacts::from_ordered(&available);
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
            Proposition::CConditionEvaluates { .. }
        ));
        assert_eq!(facts.to_vec().len(), size as usize + 1);
    }
}

#[test]
fn execution_proof_if_split_is_logarithmic_in_unrelated_facts() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 identity(int32 x) {
                immutable;
                ensures result == x;
            } by {
                assumption();
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
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(71_000)),
    ))];
    let function_environment = CExecutionEnvironment::new();
    let condition = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };

    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let replay = TacticReplayState::default();
        let root = Proof::for_execution_frontier(
            "execution proof if scaling",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        )
        .apply_step(SimpleProofStep::Step)
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

        let completed = split
            .focus_execution_if_arm(&record, true)
            .expect("the then sibling should remain open")
            .apply_step(SimpleProofStep::Step)
            .expect("the then assignment should check")
            .apply_step(SimpleProofStep::Step)
            .expect("the then return should check")
            .focus_execution_if_arm(&record, false)
            .expect("the else sibling should remain open")
            .apply_step(SimpleProofStep::Step)
            .expect("the else assignment should check")
            .apply_step(SimpleProofStep::Step)
            .expect("the else return should check")
            .join_focused_execution_if_terminal(&record)
            .expect("the two terminal proof cases should join");
        assert!(completed.is_at_function_exit());
        assert!(matches!(
            completed.certificate().steps().last(),
            Some(SimpleProofStep::If { .. })
        ));
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} execution proof-if split allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
fn execution_proof_cases_split_is_logarithmic_in_unrelated_facts() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 identity(int32 x) {
                immutable;
                ensures result == x;
            } by {
                assumption();
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
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(72_000)),
    ))];
    let function_environment = CExecutionEnvironment::new();
    let nonnegative = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let negative = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let disjunction =
        ClickProposition::Or(Box::new(nonnegative.clone()), Box::new(negative.clone()));
    let state = CState::new();
    let lowered_disjunction = lower_point_proposition_with_assumptions(
        &disjunction,
        &PureFactContext::new(),
        parsed_function.parameters(),
        &arguments,
        &state,
        &state,
        None,
        &ProgramPointStates::new(),
        &predicate_environment,
        &click_function_environment,
    )
    .expect("the exact cases disjunction should lower");
    let Proposition::Or(expected_left, expected_right) = lowered_disjunction.clone() else {
        panic!("the cases proposition should lower to a disjunction");
    };

    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        pure_facts.push(lowered_disjunction.clone());
        let replay = TacticReplayState::default();
        let root = Proof::for_execution_frontier(
            "execution proof cases scaling",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                replay,
                ExecutionFrontier::default(),
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let before = fact_node_allocations();
        let (split, record) = root
            .split_focused_execution_cases(disjunction.clone())
            .expect("exact cases should open two execution siblings");
        let allocations = fact_node_allocations() - before;
        samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            allocations,
        ));
        let left = split
            .focus_execution_cases_arm(&record, true)
            .expect("the left cases sibling should focus");
        assert_eq!(left.added_facts(), std::slice::from_ref(&*expected_left));
        let right = left
            .focus_execution_cases_arm(&record, false)
            .expect("the right cases sibling should focus");
        assert_eq!(right.added_facts(), std::slice::from_ref(&*expected_right));
        assert!(root.certificate().steps().is_empty());
    }
    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} execution cases split allocated {allocations} persistent nodes (bound {bound})"
        );
    }
}

#[test]
fn empty_execution_branch_joins_checked_proof_arms_at_the_shared_frontier() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 identity(int32 x) {
                ensures returns_x: result == x by { assumption(); }
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
    let argument = CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(60_000))));
    let arguments = vec![argument];
    let function_environment = CExecutionEnvironment::new();
    let mut allocation_samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut statement_delta: Option<Vec<Proposition>> = None;
    for size in [16_u32, 64, 256, 1024, 4096] {
        let replay = TacticReplayState::default();
        let mut frontier = ExecutionFrontier::default();
        frontier.next_statement_index = 0;
        let root = Proof::for_execution_frontier(
            "empty branch proof",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                frontier,
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
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
            [SimpleProofStep::Branch {
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
                .program_point_states
                .get(&ProgramPointRef {
                    region: CodeRegionRef::Statement(0),
                    kind: ProgramPointKind::Exit,
                })
                .is_some()
        );
        assert_eq!(execution.branch_path.len(), 0);
        let completed = joined
            .apply_step(SimpleProofStep::Step)
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
                .frontier
                .is_at_function_exit()
        );
    }
    let (_, base_height, base_allocations) = allocation_samples[0];
    assert!(base_allocations <= 160);
    for (size, height, allocations) in allocation_samples {
        let allocation_bound = base_allocations + 32 * (height - base_height);
        assert!(
            allocations <= allocation_bound,
            "size {size} checked execution branch allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
        );
    }
}

#[test]
fn nonempty_execution_branch_retains_checked_arm_steps_at_the_join() {
    let click_file = crate::lang::click::parse(
        r#"
            theorem int32_reflexive(value: int32) {
                ensures value == value by { normalize(); }
            }

            int32 constant(int32 x) {
                immutable;
                ensures returns_one: result == 1 by { assumption(); }
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
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(70_000)),
    ))];
    let application = TheoremApplication {
        name: "int32_reflexive".to_string(),
        arguments: vec![ContractExpression::CFragment(arguments[0].clone())],
    };
    let reflexive = ClickProposition::Comparison {
        left: application.arguments[0].clone(),
        operator: ComparisonOperator::Equal,
        right: application.arguments[0].clone(),
    };
    let missing_application = TheoremApplication {
        name: "missing".to_string(),
        arguments: application.arguments.clone(),
    };
    let function_environment = CExecutionEnvironment::new();
    let mut allocation_samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    for size in [16_u32, 64, 256, 1024, 4096] {
        let replay = TacticReplayState::default();
        let mut frontier = ExecutionFrontier::default();
        frontier.next_statement_index = 0;
        let root = Proof::for_execution_frontier(
            "nonempty branch proof",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                frontier,
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "constant".to_string(),
                    claim: CProofClaim::Grouped,
                }),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open two sibling arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("else assignment should check");
        let overshoot_step = SimpleProofStep::Step;
        let then_arm = branches
            .focus_split_arm(&record, true)
            .expect("the then sibling stays open until the join");
        let Err(overshoot) = then_arm.apply_step(overshoot_step) else {
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
            [SimpleProofStep::Branch {
                ensuring: None,
                then_proof,
                else_proof,
            }] if matches!(then_proof.steps(), [SimpleProofStep::Step])
                && matches!(else_proof.steps(), [SimpleProofStep::Step])
        ));
        if size == 16 {
            assert!(
                joined
                    .try_theorem_application(&missing_application)
                    .expect("missing theorem search should remain a bounded miss")
                    .is_none(),
                "a missing theorem must not manufacture a descendant"
            );
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch { .. }]
            ));
        }
        let applied = joined
            .try_theorem_application(&application)
            .expect("common theorem search should run")
            .expect("the reflexive theorem should produce a checked descendant");
        assert!(matches!(
            applied.certificate().steps(),
            [
                SimpleProofStep::Branch { .. },
                SimpleProofStep::ApplyTheoremUsing {
                    application: retained,
                    premises,
                },
            ] if retained == &application && premises.is_empty()
        ));
        let scope = applied
            .begin_have(reflexive.clone())
            .expect("the joined proof should open a common nested proposition");
        // The nested proposition goal borrows the frontier's execution
        // snapshot by identity: its path-local lowering context is
        // shared, never cloned, and can never republish a frontier.
        assert!(Arc::ptr_eq(
            scope
                .body
                .goal_execution()
                .expect("the nested goal borrows its lowering context"),
            applied
                .goal_execution()
                .expect("the joined frontier owns its snapshot"),
        ));
        let refined = scope
            .apply_step(SimpleProofStep::Assumption)
            .expect("the theorem conclusion should close the nested proposition")
            .join()
            .expect("the completed nested proposition should rejoin its root Proof");
        assert!(matches!(
            refined.certificate().steps(),
            [
                SimpleProofStep::Branch { .. },
                SimpleProofStep::ApplyTheoremUsing { .. },
                SimpleProofStep::Have {
                    proposition,
                    proof,
                },
            ] if proposition == &reflexive
                && proof.steps() == [SimpleProofStep::Assumption]
        ));
        let completed = refined
            .apply_step(SimpleProofStep::Step)
            .expect("the joined continuation should execute its return");
        assert!(
            completed
                .execution()
                .expect("completed proof retains execution state")
                .frontier
                .is_at_function_exit()
        );
        let framed = completed
            .try_smart_frame_at(None, 2, 2)
            .expect("common terminal frame search should run")
            .expect("the immutable effect should produce a checked descendant");
        allocation_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            framed.certificate().steps(),
            [
                SimpleProofStep::Branch { .. },
                SimpleProofStep::ApplyTheoremUsing { .. },
                SimpleProofStep::Have { .. },
                SimpleProofStep::Step,
                SimpleProofStep::FrameUsing {
                    region: None,
                    premises,
                },
            ] if premises.is_empty()
        ));

        // The in-`Proof` execution join: an arm still at branch entry
        // has not reached the shared continuation, a foreign split's
        // record fails marker identity, and the genuine join partitions
        // the interleaved sibling steps by attribution and resumes the
        // parent obligation under its original id.
        let parent_id = root.focused;
        let (split_proof, record) = root
            .split_focused_execution_branch()
            .expect("the symbolic condition should split in-proof");
        let sibling_ids: Vec<GoalId> = split_proof.goals().collect();
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
            .apply_step(SimpleProofStep::Step)
            .expect("the then sibling advances in place");
        let both_stepped = then_stepped
            .focus(sibling_ids[1])
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("the else sibling advances in place");
        let (_, foreign_record) = root
            .split_focused_execution_branch()
            .expect("a second split of the same root should open both arms");
        assert_eq!(foreign_record.ids, record.ids);
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
        assert_eq!(sibling_joined.focused, parent_id);
        let continuation_ids: Vec<GoalId> = sibling_joined.goals().collect();
        assert_eq!(continuation_ids, [parent_id]);
        assert!(matches!(
            sibling_joined.certificate().steps(),
            [SimpleProofStep::Branch {
                ensuring: None,
                then_proof,
                else_proof,
            }] if matches!(then_proof.steps(), [SimpleProofStep::Step])
                && matches!(else_proof.steps(), [SimpleProofStep::Step])
        ));
        let sibling_completed = sibling_joined
            .apply_step(SimpleProofStep::Step)
            .expect("the joined sibling frontier should execute its return");
        assert!(
            sibling_completed
                .execution()
                .expect("completed sibling join retains execution")
                .frontier
                .is_at_function_exit()
        );
        // The failed foreign join left the sibling state untouched.
        assert!(both_stepped.state.goals.get(sibling_ids[0]).is_some());
        assert!(both_stepped.state.goals.get(sibling_ids[1]).is_some());
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
fn branch_interface_is_checked_per_arm_and_scales_with_its_delta() {
    let click_file = crate::lang::click::parse(
        r#"
            abstract resource marker();
            abstract resource permit();

            resource ready() {
                contains permit();
            }

            int32 nonnegative(int32 x) {
                ensures nonnegative_result: result >= 0 by { assumption(); }
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
    let function = parsed_function.to_kernel_function();
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(72_000)),
    ))];
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let variable =
        |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
    let value = |constant| ContractExpression::CFragment(CExpression::Value(int32(constant)));
    let nonnegative = ClickProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::GreaterEqual,
        right: value(0),
    };
    let negative = ClickProposition::Comparison {
        left: variable("x"),
        operator: ComparisonOperator::LessThan,
        right: value(0),
    };
    let make_root = |size: u32, state: CState| {
        let replay = TacticReplayState::default();
        let mut frontier = ExecutionFrontier::default();
        frontier.next_statement_index = 0;
        Proof::for_execution_frontier(
            "branch interface proof",
            0,
            ExecutionProofState::at_entry(
                state,
                replay,
                frontier,
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        )
    };

    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let root = make_root(size, CState::new());
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open both interface arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
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
            [SimpleProofStep::Branch {
                ensuring: Some(assertions),
                then_proof,
                else_proof,
            }] if assertions == std::slice::from_ref(&ProofAssertion::Fact(nonnegative.clone()))
                && matches!(then_proof.steps(), [SimpleProofStep::Step])
                && matches!(else_proof.steps(), [SimpleProofStep::Step])
        ));
        assert!(
            joined
                .added_facts()
                .iter()
                .all(|fact| !(0..size).any(|index| *fact == indexed_fact(index))),
            "the interface node must not copy ambient facts into its delta"
        );
        let completed = joined
            .apply_step(SimpleProofStep::Step)
            .expect("the abstract joined frontier should execute its return");
        assert!(
            completed
                .execution()
                .expect("completed interface proof retains execution")
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

    let root = make_root(16, CState::new());
    let retained = root.clone();
    let (split, record) = root
        .split_focused_execution_branch()
        .expect("rejection test should open both arms");
    let error = split
        .focus_split_arm(&record, true)
        .expect("the then sibling is open")
        .apply_step(SimpleProofStep::Step)
        .expect("then assignment should check")
        .focus_split_arm(&record, false)
        .expect("the else sibling is open")
        .apply_step(SimpleProofStep::Step)
        .expect("else assignment should check")
        .join_focused_execution_interface(&record, vec![ProofAssertion::Fact(negative)])
        .err()
        .expect("each arm must independently establish the interface");
    assert!(error.message().contains("did not establish fact"));
    assert!(Arc::ptr_eq(&root.state, &retained.state));
    assert!(root.certificate().steps().is_empty());

    // The container's spliced-arm identity regression is superseded by
    // the split-identity regression below: a foreign split of the same
    // root collides numerically and is rejected by marker identity.

    // The in-`Proof` execution split: both feasible arms become sibling
    // frontier goals in one state, each advancing by focus on one
    // lineage, with `introduced_since` recovering each arm's fact delta
    // from its recorded split-time base even after interleaved steps.
    let root = make_root(16, CState::new());
    let (split_proof, record) = root
        .split_focused_execution_branch()
        .expect("the symbolic condition should split in-proof");
    let sibling_ids: Vec<GoalId> = split_proof.goals().collect();
    assert_eq!(sibling_ids.len(), 2);
    assert_eq!(record.ids, [Some(sibling_ids[0]), Some(sibling_ids[1])]);
    assert!(record.condition_theorems.iter().all(Option::is_some));
    let then_stepped = split_proof
        .apply_step(SimpleProofStep::Step)
        .expect("the then sibling advances in place");
    assert!(then_stepped.state.goals.get(sibling_ids[1]).is_some());
    let both_stepped = then_stepped
        .focus(sibling_ids[1])
        .expect("the else sibling is open")
        .apply_step(SimpleProofStep::Step)
        .expect("the else sibling advances in place");
    for (index, id) in sibling_ids.iter().enumerate() {
        let arm = both_stepped.focus(*id).expect("both siblings remain open");
        let base = record.base_facts[index]
            .as_ref()
            .expect("both feasible arms recorded their bases");
        assert!(
            arm.facts().introduced_since(base).is_some(),
            "arm {index} must still descend from its recorded split base"
        );
    }
    assert!(root.certificate().steps().is_empty());
    assert_eq!(root.goals().count(), 1);

    // The in-`Proof` interface join: both siblings advance on one
    // lineage with distinct concrete states, abstract through the same
    // explicit interface, and resume the parent obligation with the
    // agreed abstract continuation.
    let parent_id = root.focused;
    let interface = vec![ProofAssertion::Fact(nonnegative.clone())];
    let joined = both_stepped
        .join_focused_execution_interface(&record, interface.clone())
        .expect("both siblings should abstract through the shared interface");
    assert_eq!(joined.focused, parent_id);
    let joined_ids: Vec<GoalId> = joined.goals().collect();
    assert_eq!(joined_ids, [parent_id]);
    assert!(matches!(
        joined.certificate().steps(),
        [SimpleProofStep::Branch {
            ensuring: Some(retained),
            then_proof,
            else_proof,
        }] if retained == interface.as_slice()
            && matches!(then_proof.steps(), [SimpleProofStep::Step])
            && matches!(else_proof.steps(), [SimpleProofStep::Step])
    ));
    let completed = joined
        .apply_step(SimpleProofStep::Step)
        .expect("the abstract sibling continuation should execute its return");
    assert!(
        completed
            .execution()
            .expect("the completed sibling interface proof retains execution")
            .frontier
            .is_at_function_exit()
    );
    // A failed sibling interface join is transactional.
    let negative_retained = ClickProposition::Comparison {
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
    assert!(both_stepped.state.goals.get(sibling_ids[0]).is_some());
    assert!(both_stepped.state.goals.get(sibling_ids[1]).is_some());

    let marker_clause = ResourceClause::Declared {
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Token,
        name: "marker".to_string(),
        arguments: Vec::new(),
        parameter_types: Vec::new(),
    };
    let marker_fact = CResourceFact::own_token("marker".to_string(), Vec::new());
    let mut ownership_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
            }))
            .unchecked_with_fact(marker_fact.clone());
        let (split, record) = make_root(16, CState::new().with_resource_context(resources))
            .split_focused_execution_branch()
            .expect("the owned-interface condition should expose both arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("owned-interface then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
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
            [SimpleProofStep::Branch {
                ensuring: Some(retained),
                ..
            }] if retained == assertions.as_slice()
        ));
        joined
            .apply_step(SimpleProofStep::Step)
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
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Composite,
        name: "ready".to_string(),
        arguments: Vec::new(),
        parameter_types: Vec::new(),
    };
    let permit_fact = CResourceFact::own_token("permit".to_string(), Vec::new());
    let mut changed_snapshot_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
            }))
            .unchecked_with_fact(permit_fact.clone());
        let (split, record) = make_root(16, CState::new().with_resource_context(resources))
            .split_focused_execution_branch()
            .expect("the transformed-interface condition should expose both arms");
        assert!(
            record.supports_interface_branch(),
            "a structural preflight must not require a resource folded later in the arms"
        );
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("transformed-interface then assignment should check")
            .apply_step(SimpleProofStep::FoldResource(ready_clause.clone()))
            .expect("then arm should fold its ready resource")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("transformed-interface else assignment should check")
            .apply_step(SimpleProofStep::FoldResource(ready_clause.clone()))
            .expect("else arm should independently fold its ready resource");
        let arm_execution = |take_then: bool| {
            let id = record.arm_id(take_then).expect("both arms are feasible");
            let Some(Goal::Frontier(frontier)) = branches.state.goals.get(id) else {
                panic!("both arms should remain open execution frontiers");
            };
            frontier
                .context
                .execution
                .as_deref()
                .expect("both arms should retain execution")
        };
        assert!(
            !arm_execution(true)
                .state
                .resources()
                .shares_storage_with(arm_execution(false).state.resources())
        );

        let assertions = vec![ProofAssertion::Resource(ready_clause.clone())];
        let before = fact_node_allocations();
        let joined = branches
            .join_focused_execution_interface(&record, assertions)
            .expect("independently folded resource snapshots should rejoin");
        changed_snapshot_samples.push((
            size,
            (u32::BITS - size.leading_zeros()) as usize,
            fact_node_allocations() - before,
        ));
        assert!(matches!(
            joined.certificate().steps(),
            [SimpleProofStep::Branch {
                then_proof,
                else_proof,
                ..
            }] if matches!(
                then_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::FoldResource(_)]
            ) && matches!(
                else_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::FoldResource(_)]
            )
        ));
        joined
            .apply_step(SimpleProofStep::Step)
            .expect("the transformed owned interface should retain its return frontier");
    }
    let (_, base_height, base_allocations) = changed_snapshot_samples[0];
    for (size, height, allocations) in changed_snapshot_samples {
        let bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} changed-resource Proof join allocated {allocations} persistent nodes (bound {bound})"
        );
    }

    let represented_quantity = CResourceFact::own_quantity(
        CResource::Token {
            name: "marker".to_string(),
            arguments: Vec::new(),
        },
        Bitvector32Term::Constant(2),
    );
    let mut normalized_quantity_samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_token(format!("quantity_unrelated_{index}"), Vec::new())
            }))
            .unchecked_with_fact(represented_quantity.clone());
        let (split, record) = make_root(16, CState::new().with_resource_context(resources))
            .split_focused_execution_branch()
            .expect("the normalized-ownership probe should expose both arms");
        let branches = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("normalized-ownership then assignment should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
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
        CState::new().with_resource_context(
            ResourceContext::new().unchecked_with_fact(represented_quantity),
        ),
    );
    let (invalid_split, invalid_record) = invalid_root
        .split_focused_execution_branch()
        .expect("the rejected quantity probe should expose both arms");
    let invalid_branches = invalid_split
        .focus_split_arm(&invalid_record, true)
        .expect("the then sibling is open")
        .apply_step(SimpleProofStep::Step)
        .expect("rejected quantity then assignment should check")
        .focus_split_arm(&invalid_record, false)
        .expect("the else sibling is open")
        .apply_step(SimpleProofStep::Step)
        .expect("rejected quantity else assignment should check");
    let quantity_three = ResourceClause::Quantified {
        quantity: ContractExpression::CFragment(CExpression::Value(int32(3))),
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
fn nested_end_of_arm_interface_derives_its_enclosing_continuation() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 nested(int32 x, int32 flag) {
                ensures nonnegative_result: result >= 0 by { assumption(); }
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
        CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(73_000)))),
        CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(73_001)))),
    ];
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let nonnegative = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let make_root = |size: u32| {
        let replay = TacticReplayState::default();
        let mut frontier = ExecutionFrontier::default();
        frontier.next_statement_index = 0;
        Proof::for_execution_frontier(
            "nested branch interface proof",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                frontier,
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        )
    };

    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
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
            .apply_step(SimpleProofStep::Step)
            .expect("nested then assignment should check")
            .focus_split_arm(&nested_record, false)
            .expect("the nested else sibling is open")
            .apply_step(SimpleProofStep::Step)
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
                .program_point_states
                .get(&ProgramPointRef {
                    region: CodeRegionRef::Statement(nested_statement),
                    kind: ProgramPointKind::Exit,
                })
                .is_some()
        );
        assert!(
            execution.frontier.is_at_region_boundary(),
            "the nested join ends the outer arm's own region"
        );
        let joined = joined
            .continue_arm_into_parent_frontier(&outer_record)
            .expect("the outer split record derives the enclosing continuation");
        assert!(matches!(
            joined.certificate().steps(),
            [SimpleProofStep::Branch {
                ensuring: Some(assertions),
                ..
            }] if assertions == std::slice::from_ref(&ProofAssertion::Fact(nonnegative.clone()))
        ));
        let completed = joined
            .apply_step(SimpleProofStep::Step)
            .expect("derived enclosing continuation should execute the return");
        assert!(
            completed
                .execution()
                .expect("completed nested proof retains execution")
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
fn decided_execution_branch_retains_one_checked_path_without_copying_context() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 selected(int32 x) {
                ensures returns_one: result == 1 by { assumption(); }
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
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(75_000)),
    ))];
    let function_environment = CExecutionEnvironment::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let make_root = |facts: Vec<Proposition>| {
        let replay = TacticReplayState::default();
        let mut frontier = ExecutionFrontier::default();
        frontier.next_statement_index = 0;
        Proof::for_execution_frontier(
            "decided branch proof",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                frontier,
                ProgramPointStates::new(),
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
            &predicate_environment,
            &click_function_environment,
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
        let advanced = split
            .focus_split_arm(&record, true)
            .expect("the sole sibling is open")
            .try_indexed_execute_step()
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
            [SimpleProofStep::If {
                then_proof,
                else_proof,
                ..
            }] if matches!(
                then_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::Step]
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
        let completed = decided
            .try_indexed_execute_step()
            .expect("contextual return selection should remain bounded")
            .expect("the continuation return should check with retained branch facts");
        assert!(
            completed
                .execution()
                .expect("completed decided proof retains execution")
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
    let advanced = split
        .focus_split_arm(&record, false)
        .expect("the sole else sibling is open")
        .try_indexed_execute_step()
        .expect("else-arm smart selection should remain bounded")
        .expect("the else assignment should produce a checked successor");
    let decided = advanced
        .finish_focused_execution_decided(&record)
        .expect("the sole else arm should form a decided path");
    let certificate = decided.certificate();
    assert!(
        matches!(
        certificate.steps(),
        [SimpleProofStep::If {
            condition,
            then_proof,
            else_proof,
        }] if then_proof.steps().is_empty()
            && matches!(
                else_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::Step]
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
    let parent_id = root.focused;
    let (split_proof, record) = root
        .split_focused_execution_branch()
        .expect("the selecting fact should split to the sole then sibling");
    assert!(record.ids[0].is_some() && record.ids[1].is_none());
    assert_eq!(split_proof.goals().count(), 1);
    let advanced = split_proof
        .try_indexed_execute_step()
        .expect("sole-sibling selection should remain bounded")
        .expect("the assignment should produce a checked simple successor");
    let decided = advanced
        .finish_focused_execution_decided(&record)
        .expect("the sole checked sibling should form a decided path");
    assert_eq!(decided.focused, parent_id);
    let decided_ids: Vec<GoalId> = decided.goals().collect();
    assert_eq!(decided_ids, [parent_id]);
    assert!(matches!(
        decided.certificate().steps(),
        [SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        }] if matches!(
            then_proof.steps(),
            [SimpleProofStep::Step, SimpleProofStep::Step]
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
    let completed = decided
        .try_indexed_execute_step()
        .expect("contextual return selection should remain bounded")
        .expect("the continuation return should check with retained branch facts");
    assert!(
        completed
            .execution()
            .expect("the completed decided sibling proof retains execution")
            .frontier
            .is_at_function_exit()
    );
    // The decided interface finish mirrors the plain decided finish
    // through the interface entrypoint: an explicit interface on the
    // sole sibling records `Branch { ensuring, .. }` with the empty
    // impossible arm and resumes the parent id.
    let root = make_root(vec![selecting_fact.clone()]);
    let parent_id = root.focused;
    let (split_proof, record) = root
        .split_focused_execution_branch()
        .expect("the selecting fact should split to the sole then sibling");
    let advanced = split_proof
        .try_indexed_execute_step()
        .expect("sole-sibling selection should remain bounded")
        .expect("the assignment should produce a checked simple successor");
    let decided = advanced
        .join_focused_execution_interface(&record, Vec::new())
        .expect("the sole checked sibling should finish through the interface");
    assert_eq!(decided.focused, parent_id);
    let decided_ids: Vec<GoalId> = decided.goals().collect();
    assert_eq!(decided_ids, [parent_id]);
    assert!(matches!(
        decided.certificate().steps(),
        [SimpleProofStep::Branch {
            ensuring: Some(retained),
            then_proof,
            else_proof,
        }] if retained.is_empty()
            && matches!(then_proof.steps(), [SimpleProofStep::Step])
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
fn terminal_execution_branch_retains_distinct_outcomes_as_a_logical_if() {
    let click_file = crate::lang::click::parse(
        r#"
            int32 choose(int32 x) {
                ensures returns_one_or_two: result == 1 or result == 2 by { assumption(); }
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
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(80_000)),
    ))];
    let function_environment = CExecutionEnvironment::new();
    let mut allocation_samples = Vec::new();
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let mut expected_outcome_fact_sizes = None;
    for size in [16_u32, 64, 256, 1024, 4096] {
        let replay = TacticReplayState::default();
        let mut frontier = ExecutionFrontier::default();
        frontier.next_statement_index = 0;
        let root = Proof::for_execution_frontier(
            "terminal branch proof",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                replay,
                frontier,
                ProgramPointStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect(),
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
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("symbolic condition should open two sibling arms");
        let advanced = split
            .focus_split_arm(&record, true)
            .expect("the then sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("then return should check")
            .focus_split_arm(&record, false)
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("else return should check");
        assert!(advanced.split_arms_at_function_exit(&record));
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
            [SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            }] if matches!(
                then_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::Step]
            ) && matches!(
                else_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::Step]
            )
        ));
        assert!(root.certificate().steps().is_empty());
        let execution = joined
            .execution()
            .expect("terminal join should retain execution state");
        assert!(execution.frontier.is_at_function_exit());
        let outcome_paths = execution
            .frontier
            .execution()
            .expect("terminal join should retain outcomes")
            .paths();
        assert_eq!(outcome_paths.len(), 2);
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
        assert_eq!(execution.branch_path.len(), 0);

        // The in-`Proof` terminal join: both siblings return on their
        // own lineage and rejoin as a logical `If` whose outcome paths
        // stay separate, resuming the parent obligation at function
        // exit under its original id.
        let parent_id = root.focused;
        let (split_proof, record) = root
            .split_focused_execution_branch()
            .expect("the symbolic condition should split in-proof");
        let sibling_ids: Vec<GoalId> = split_proof.goals().collect();
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
            .apply_step(SimpleProofStep::Step)
            .expect("the then sibling returns in place")
            .focus(sibling_ids[1])
            .expect("the else sibling is open")
            .apply_step(SimpleProofStep::Step)
            .expect("the else sibling returns in place");
        let sibling_joined = both_returned
            .join_focused_execution_terminal(&record)
            .expect("both returned siblings form a terminal logical case split");
        assert_eq!(sibling_joined.focused, parent_id);
        let continuation_ids: Vec<GoalId> = sibling_joined.goals().collect();
        assert_eq!(continuation_ids, [parent_id]);
        assert!(matches!(
            sibling_joined.certificate().steps(),
            [SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            }] if matches!(
                then_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::Step]
            ) && matches!(
                else_proof.steps(),
                [SimpleProofStep::Step, SimpleProofStep::Step]
            )
        ));
        let sibling_execution = sibling_joined
            .execution()
            .expect("the sibling terminal join retains execution state");
        assert!(sibling_execution.frontier.is_at_function_exit());
        assert_eq!(
            sibling_execution
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
