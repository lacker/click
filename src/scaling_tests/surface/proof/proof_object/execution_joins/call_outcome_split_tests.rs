use super::*;
use crate::kernel::{
    FunctionContractClaim, ProgramStatement, Proposition, bool_value, program_call,
    program_function, program_if, program_parameter, program_return, program_seq, program_skip,
    program_try_catch_int32, prove_checked_program_function_execution_with_environment,
    prove_program_function_contract_execution_paths_with_checked_artifacts,
};

/// A caught-throw call splits into its returned and threw arms the way a C
/// `if` splits: the call runs in the proof's context, and each arm is the
/// proof's facts with what the call added. Splitting after `size`
/// unrelated facts copies none of them and costs no more at any size (the
/// first size also pays one-time warm-up); it once copied every fact into a
/// flat list and folded each one back, and its work grew from 600 to 7,296
/// units at 16 to 256 facts.
#[test]
fn call_outcome_split_does_not_copy_the_proofs_facts() {
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
    let helper_arguments = vec![ProgramExpression::Value(bool_value(MachineTerm::Variable(
        Variable(80_111),
    )))];
    let artifacts = prove_checked_program_function_execution_with_environment(
        ExecutionState::new().with_population_creation_tracking(),
        helper.clone(),
        helper_arguments.clone(),
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let certified = prove_program_function_contract_execution_paths_with_checked_artifacts(
        ExecutionState::new().with_population_creation_tracking(),
        helper.clone(),
        helper_arguments,
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
        &[artifacts],
    );
    let claims = crate::kernel::program_verified_function_contract_claims(&helper, &certified)
        .expect("helper body safety should certify");
    let helper_rule = program_verified_function_rule(helper.clone(), &claims)
        .expect("the checked helper should have a modular rule");
    let function_environment = ExecutionEnvironment::new()
        .with_function(helper)
        .with_verified_function_rule(helper_rule);
    let function = program_function(
        ProgramType::Int32,
        "caller",
        vec![
            program_parameter("construct", ProgramType::Bool),
            program_parameter("should_throw", ProgramType::Bool),
        ],
        program_seq(
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
        ),
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
    let click_file = crate::surface::parse(
        "int32 caller(bool construct, bool should_throw) { ensures result == result; }",
    )
    .unwrap();
    let function_block = &click_file.function_blocks()[0];
    let arguments = vec![
        ProgramExpression::Value(bool_value(MachineTerm::Variable(Variable(80_112)))),
        ProgramExpression::Value(bool_value(MachineTerm::Variable(Variable(80_113)))),
    ];
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let constants = ExecutionProofConstants {
        source_layout: SourceExecutionLayout::for_function(&parsed_function).unwrap(),
        ..ExecutionProofConstants::default()
    };
    let mut costs = Vec::new();
    for size in [16u64, 64, 256] {
        let facts = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(MachineTerm::Variable(Variable(81_000 + index))),
                        right: Box::new(MachineTerm::constant(index as u32)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        let root = Proof::for_execution_frontier(
            "call outcome split",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new().with_population_creation_tracking(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            facts.clone(),
            constants.clone(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resources,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let (branch, branch_record) = root
            .split_focused_execution_branch()
            .expect("the conditional should split");
        let at_call = branch.focus_split_arm(&branch_record, true).unwrap();
        let [copied_before, _] = crate::surface::pure_fact_list::fact_list_entry_counts();
        let (split, work) = crate::instrumentation::measure_deterministic_work(|| {
            at_call
                .split_focused_call_outcomes()
                .expect("the call split should be checked")
                .expect("the helper both returns and throws")
        });
        let [copied_after, _] = crate::surface::pure_fact_list::fact_list_entry_counts();
        let (outcomes, record) = split;
        let returned = outcomes.focus_split_arm(&record, true).unwrap();
        let threw = outcomes.focus_split_arm(&record, false).unwrap();
        for arm in [&returned, &threw] {
            assert!(
                facts.iter().all(|fact| arm.facts().contains(fact)),
                "an arm lost a fact of the proof: size={size}"
            );
        }
        costs.push((copied_after - copied_before, work));
    }
    assert!(
        costs
            .windows(2)
            .all(|pair| pair[1].0 <= pair[0].0 && pair[1].1 <= pair[0].1),
        "splitting a call's outcomes grows with the proof's facts: {costs:?}"
    );
}
