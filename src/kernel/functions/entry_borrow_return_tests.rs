use super::*;

#[test]
fn returned_borrows_keep_checked_entry_arguments_when_clauses_are_reordered() {
    let field = |name: &str| {
        let address = Pointer {
            block: format!("parent:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::Value(ProgramValue::pointer(address))),
            value_type: ProgramType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        }
    };
    let clause = |name: &str| {
        ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "child_ref".into(),
            vec![field(name)],
            vec![ProgramType::Int32Pointer],
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap()
    };
    let left = clause("left");
    let right = clause("right");
    let function = program_function(ProgramType::Void, "borrow", Vec::new(), program_skip())
        .with_resource_summary(vec![left.clone(), right.clone()], vec![right, left]);
    let children = ["child:left", "child:right"].map(|name| {
        ResourceFact::own_composite(
            "child_ref".into(),
            vec![ProgramValue::pointer(Pointer {
                block: name.into(),
                offset: PointerOffsetTerm::Constant(0),
            })],
        )
    });
    let checked = children
        .iter()
        .enumerate()
        .map(|(index, fact)| CheckedResourceFact {
            fact: fact.clone(),
            role: ResourceTransferRole::Borrow,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: Some(index),
            selected_mutex_source: None,
        })
        .collect::<Vec<_>>();
    // Neither field has a materialized cell. Re-evaluating either return
    // clause would fail, even though its exact borrowed owner was checked.
    let state = ExecutionState::new();
    let returned = evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        &checked,
        &[],
        &state,
        &state,
        2,
        &[],
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        returned.facts(),
        &[children[1].clone(), children[0].clone()]
    );
}
