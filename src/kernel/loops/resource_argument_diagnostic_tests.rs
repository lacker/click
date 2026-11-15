use super::*;

#[test]
fn missing_argument_read_retains_the_actual_state_and_permission() {
    let state = ExecutionState::new().with_local(
        "p",
        ProgramValue::pointer(Pointer::symbolic(Variable(985_910))),
    );
    let expression =
        crate::kernel::program_expression::load(crate::kernel::program_expression::variable("p"));
    let assumptions = PureFactContext::new();
    let mut budget = ExecutionBudget::default();
    let mut diagnostic = None;
    let captured = evaluate_resource_argument_value(
        &state,
        &expression,
        &assumptions,
        "resource `cell` argument 1",
        &mut budget,
        &mut diagnostic,
    )
    .unwrap();
    let ordinary = evaluate_loop_effect_segment_value(
        &state,
        &expression,
        &assumptions,
        "resource `cell` argument 1",
        &mut budget,
    )
    .unwrap();
    assert_eq!(captured, ordinary);
    assert!(captured.is_err());
    let Some(RuntimeError::ContractResourceDiagnostic {
        memory: Some(memory),
        required,
        held: None,
        ..
    }) = diagnostic
    else {
        panic!("the failed read must retain its operands")
    };
    assert_eq!(*memory, *state.memory());
    assert!(matches!(*required, ResourceFact::View(Resource::Memory(_))));
}
