use super::*;

fn schema() -> ResourceFieldSchema {
    ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap()
}
fn cell(identity: u64, argument: u32) -> ResourceInstance {
    ResourceInstance::new(
        Variable(identity),
        "cell".into(),
        vec![int32(argument).into()].into(),
        schema(),
        vec![int32(7).into()].into(),
    )
    .unwrap()
}
fn definition() -> CompositeResourceDefinition {
    let parameter = ResourceSpec::instance(
        Variable(90),
        "cell".into(),
        schema(),
        ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "cell".into(),
            vec![crate::kernel::program_expression::variable("p")],
            vec![ProgramType::Int32],
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap(),
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap()
    .with_source_arguments(vec!["p".into()]);
    CompositeResourceDefinition::new(
        "wrapper",
        vec![program_parameter("p", ProgramType::Int32)],
        None,
        false,
        vec![],
        vec![],
    )
    .with_instance_schema(Some(schema()))
    .with_resource_parameters(vec![parameter])
}
fn wrapper(reference: &ResourceInstance) -> ResourceInstance {
    ResourceInstance::new(
        Variable(20),
        "wrapper".into(),
        vec![int32(3).into()].into(),
        schema(),
        vec![int32(0).into()].into(),
    )
    .unwrap()
    .with_resource_arguments(vec![ResourceReference::from_instance(reference)])
}
#[test]
fn reference_only_wrapper_does_not_transfer_referenced_custody() {
    let child = cell(10, 3);
    let resource = wrapper(&child);
    let definition = definition();
    let folded = rewrite_resource_instance_selecting_children(
        &ExecutionState::new(),
        &resource,
        &definition,
        &[],
        &PureFactContext::new(),
        false,
        None,
    )
    .unwrap()
    .state;
    assert!(folded.resources.owned_instance(child.identity()).is_none());
    let opened = rewrite_resource_instance_selecting_children(
        &folded,
        &resource,
        &definition,
        &[],
        &PureFactContext::new(),
        true,
        None,
    )
    .unwrap()
    .state;
    assert!(opened.resources.owned_instance(child.identity()).is_none());
}
#[test]
fn reference_type_cannot_be_retargeted_by_wrapper_arguments() {
    let resource = wrapper(&cell(10, 4));
    let error = rewrite_resource_instance_selecting_children(
        &ExecutionState::new(),
        &resource,
        &definition(),
        &[],
        &PureFactContext::new(),
        false,
        None,
    )
    .unwrap_err();
    assert_eq!(error.describe(), "Requires cell: cell(p)");
}

#[test]
fn replacement_reference_cannot_open_an_owned_wrapper() {
    let resource = wrapper(&cell(10, 3));
    let definition = definition();
    let state = rewrite_resource_instance_selecting_children(
        &ExecutionState::new(),
        &resource,
        &definition,
        &[],
        &PureFactContext::new(),
        false,
        None,
    )
    .unwrap()
    .state;
    let forged = wrapper(&cell(11, 3));
    assert!(
        rewrite_resource_instance_selecting_children(
            &state,
            &forged,
            &definition,
            &[],
            &PureFactContext::new(),
            true,
            None
        )
        .is_err()
    );
}

fn owning_definition() -> CompositeResourceDefinition {
    definition().with_children(vec![ResourceChildSpec {
        name: "cell".into(),
        resource: "cell".into(),
        binding: Variable(90),
        arguments: vec![SpecExpression::ProgramExpression(
            crate::kernel::program_expression::variable("p"),
        )],
        field_bindings: vec![ResourceChildField::Parent(0)],
    }])
}
fn child_definition() -> CompositeResourceDefinition {
    CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32)],
        None,
        false,
        vec![],
        vec![],
    )
    .with_instance_schema(Some(schema()))
}
#[test]
fn owned_reference_uses_checked_child_custody_and_current_model() {
    let child = cell(10, 3);
    let mut resource = wrapper(&child);
    resource.fields = child.fields.clone();
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(child.clone()))),
    );
    let definition = owning_definition();
    let definitions = vec![child_definition(), definition.clone()];
    let folded = rewrite_resource_instance_selecting_children(
        &state,
        &resource,
        &definition,
        &definitions,
        &PureFactContext::new(),
        false,
        None,
    )
    .unwrap()
    .state;
    assert!(folded.resources.owned_instance(child.identity()).is_none());
    let opened = rewrite_resource_instance_selecting_children(
        &folded,
        &resource,
        &definition,
        &definitions,
        &PureFactContext::new(),
        true,
        None,
    )
    .unwrap()
    .state;
    assert_eq!(
        opened.resources.owned_instance(child.identity()),
        Some(&child)
    );
    assert!(
        rewrite_resource_instance_selecting_children(
            &ExecutionState::new(),
            &resource,
            &definition,
            &definitions,
            &PureFactContext::new(),
            false,
            None
        )
        .is_err()
    );
}
#[test]
fn owned_reference_rejects_substituting_a_different_child_occurrence() {
    let child = cell(10, 3);
    let mut resource = wrapper(&child);
    resource.fields = child.fields.clone();
    let other = cell(11, 3);
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own(Resource::Instance(other))),
    );
    let definition = owning_definition();
    let definitions = vec![child_definition(), definition.clone()];
    assert!(
        rewrite_resource_instance_selecting_children(
            &state,
            &resource,
            &definition,
            &definitions,
            &PureFactContext::new(),
            false,
            Some(&[("cell".into(), Variable(11))])
        )
        .is_err()
    );
}

#[test]
fn reference_does_not_restore_fields_observed_when_it_was_captured() {
    let old = cell(10, 3);
    let mut current = old.clone();
    current.fields = vec![int32(9).into()].into();
    let mut resource = wrapper(&old);
    resource.fields = current.fields.clone();
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(current.clone()))),
    );
    let definition = owning_definition();
    let definitions = vec![child_definition(), definition.clone()];
    let folded = rewrite_resource_instance_selecting_children(
        &state,
        &resource,
        &definition,
        &definitions,
        &PureFactContext::new(),
        false,
        None,
    )
    .unwrap()
    .state;
    let opened = rewrite_resource_instance_selecting_children(
        &folded,
        &resource,
        &definition,
        &definitions,
        &PureFactContext::new(),
        true,
        None,
    )
    .unwrap()
    .state;
    assert_eq!(
        opened.resources.owned_instance(current.identity()),
        Some(&current)
    );
}

#[test]
fn section_reference_lookup_does_not_duplicate_existing_owned_instances() {
    let child = cell(10, 3);
    let record = wrapper(&child);
    let state =
        ExecutionState::new().with_resource_context(ResourceContext::new().unchecked_with_facts([
            ResourceFact::own(Resource::Instance(child.clone())),
            ResourceFact::own(Resource::Instance(record.clone())),
        ]));
    let named_spec = |instance: &ResourceInstance, references: Vec<Variable>| {
        ResourceSpec::instance(
            instance.identity(),
            instance.name().into(),
            instance.schema().clone(),
            ResourceSpec::declared(
                ResourceFamily::Composite,
                ResourceAccessMode::Own,
                instance.name().into(),
                vec![crate::kernel::program_expression::int32_literal(3)],
                vec![ProgramType::Int32],
                ResourceTransferRole::Borrow,
                ResourceStateSource::Current,
            )
            .unwrap()
            .with_resource_arguments(references),
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap()
    };
    let specs = vec![
        named_spec(&child, vec![]),
        named_spec(&record, vec![child.identity()]),
    ];
    let mut budget = ExecutionBudget::beside_live_state();
    let result = evaluate_function_resource_context_with_metadata(
        &state,
        &specs,
        &[],
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap()
    .unwrap();
    assert_eq!(result.0.owned_instance(child.identity()), Some(&child));
    assert_eq!(result.0.owned_instance(record.identity()), Some(&record));
    let function = program_function(
        ProgramType::Int32,
        "return_refs",
        vec![],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_resource_summary(vec![], specs.clone());
    let returned = evaluate_function_return_resource_context(
        &function,
        &[],
        &state,
        &state,
        specs.len(),
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap()
    .unwrap();
    assert_eq!(returned.owned_instance(record.identity()), Some(&record));
    // Deduplicating scratch lookup must not accept duplicate ownership clauses.
    let duplicate = vec![specs[0].clone(), specs[0].clone()];
    assert!(
        evaluate_function_resource_context_with_metadata(
            &state,
            &duplicate,
            &[],
            &PureFactContext::new(),
            &mut budget
        )
        .unwrap()
        .is_err()
    );
}
