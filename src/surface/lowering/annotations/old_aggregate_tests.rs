use super::*;

fn entry_state() -> ExecutionState {
    use crate::kernel::*;
    let source = Pointer {
        block: "local:caller".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let function = program_function(
        ProgramType::Void,
        "copy",
        vec![program_parameter_with_aggregate_layout(
            "input",
            ProgramType::VoidPointer,
            AggregateLayout::new(
                8,
                8,
                vec![AggregateField::new("data", 0, ProgramType::Int32Pointer)],
            ),
        )],
        program_return(program_void_value()),
    );
    program_function_entry_state(
        &ExecutionState::new().with_memory(Memory::new().with_block(source.block.clone(), 8)),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(source))],
    )
    .unwrap()
}

fn lower_name(
    state: &ExecutionState,
    name: &str,
    at_entry: bool,
) -> Result<SpecExpression, String> {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let retained_states = RecordedStates::new();
    let (lowerer, _) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        state,
        BTreeMap::new(),
        BTreeMap::new(),
        None,
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    lowerer.lower_program_binding_to_spec(
        name,
        &SpecElaborationContext {
            current_memory: SpecMemory::Fixed(state.memory().clone()),
            at_function_entry: at_entry,
            ..Default::default()
        },
    )
}

#[test]
fn old_aggregate_binding_uses_only_the_selected_entry_place() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = entry_state();
    assert_eq!(
        lower_name(&state, "input", true).unwrap(),
        SpecExpression::Value(ProgramValue::typed_pointer(
            state
                .locals()
                .aggregate_object_pointer("input")
                .unwrap()
                .clone(),
            ProgramType::UInt8Pointer
        ))
    );
    assert!(lower_name(&state, "later_local", true).is_err());
    assert!(lower_name(&state, "input", false).is_err());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/lowering/annotations/old_aggregate_tests.rs");
}
