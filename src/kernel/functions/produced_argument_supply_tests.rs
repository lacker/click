use super::*;

fn output(index: u32) -> ResourceSpec {
    ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::variable("cells"),
        crate::kernel::program_expression::int32_literal(index),
        crate::kernel::program_expression::int32_literal(index + 1),
    ))
    .with_role(ResourceTransferRole::Produce)
    .with_state_source(ResourceStateSource::Post)
}

fn state(count: u32) -> ExecutionState {
    ExecutionState::new()
        .with_local(
            "cells",
            ProgramValue::pointer(Pointer {
                block: "produced-cells".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
        .with_memory(Memory::new().with_block("produced-cells", count * 4))
}

#[test]
fn output_supply_keeps_entry_and_guarded_clauses_out_of_post_reads() {
    let guard = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            1,
        )),
    };
    let function = program_function(ProgramType::Void, "outputs", vec![], program_skip())
        .with_resource_summary(
            vec![],
            vec![
                output(0),
                output(1).with_state_source(ResourceStateSource::Entry),
                output(2).with_guard(guard.clone()),
                ResourceSpec::owned_memory(
                    MemorySegment::new(
                        crate::kernel::program_expression::variable("cells"),
                        crate::kernel::program_expression::int32_literal(3),
                        crate::kernel::program_expression::int32_literal(4),
                    )
                    .with_guard(guard),
                )
                .with_role(ResourceTransferRole::Produce)
                .with_state_source(ResourceStateSource::Post),
            ],
        );
    let entry = state(4);
    let mut evaluation = entry.clone();
    let prepared = prepare_produced_argument_supply(
        &entry,
        &mut evaluation,
        function.contract_interface(),
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap();
    assert!(prepared[0].is_some());
    assert!(prepared[1].is_none());
    assert!(prepared[2].is_none());
    assert!(prepared[3].is_none());
    assert_eq!(evaluation.resources().facts().len(), 1);
    assert!(evaluation.resources().facts()[0].is_view());
    assert!(entry.resources().facts().is_empty());
}

#[test]
fn a_primitive_output_that_cannot_be_addressed_grants_no_authority() {
    let function = program_function(ProgramType::Void, "outputs", vec![], program_skip())
        .with_resource_summary(vec![], vec![output(0)]);
    // The address expression has no value, so the clause remains pending for
    // the ordinary return evaluator. Preparation must invent neither a value
    // nor read authority for it.
    let entry = ExecutionState::new();
    let mut evaluation = entry.clone();
    let prepared = prepare_produced_argument_supply(
        &entry,
        &mut evaluation,
        function.contract_interface(),
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap();
    assert_eq!(prepared, vec![None]);
    assert!(evaluation.resources().facts().is_empty());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/produced_argument_supply_tests.rs");
}
