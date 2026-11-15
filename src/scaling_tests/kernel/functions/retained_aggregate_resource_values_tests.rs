// Scaling tests of `src/kernel/functions.rs` (module `retained_aggregate_resource_values_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn retained_resource_fields_preserve_lvalues_and_scale_with_expression() {
    let slot = Pointer {
        block: "local:frame:0:input".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointee = Pointer {
        block: "pointee".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = ProgramValue::typed_pointer(pointee, ProgramType::Int32Pointer);
    let layout = AggregateLayout::new(
        8,
        8,
        vec![AggregateField::new("data", 0, ProgramType::Int32Pointer)],
    );
    let field = ProgramExpression::TypedLoad {
        pointer: Box::new(ProgramExpression::Variable("input".into())),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let mut work = Vec::new();
    for size in [8, 32, 128, 512] {
        // Compare cold sessions at every size; retained pointer reads
        // otherwise reuse observations recorded by the first sample.
        let _session = crate::kernel::VerificationSession::enter();
        let mut entry = ExecutionState::new().with_memory(
            Memory::new()
                .with_block(slot.block.clone(), 8)
                .store(slot.clone(), value.clone()),
        );
        entry
            .locals
            .set_aggregate_object_at("input".to_string(), layout.clone(), slot.clone());
        for i in 0..size {
            entry = entry.with_local(format!("unrelated_{i}"), int32(i));
        }
        let state = entry
            .clone()
            .with_memory(entry.memory.clone().without_local_block(&slot.block));
        let resolve = |expression: &mut ProgramExpression| {
            resolve_retained_aggregate_fields(
                &entry,
                &state,
                expression,
                true,
                &PureFactContext::new(),
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap();
        };
        let mut expression = field.clone();
        let (_, measured) =
            crate::instrumentation::measure_deterministic_work(|| resolve(&mut expression));
        work.push(measured);
        // The retained field keeps its entry-read name; the graph relates
        // its complete value to the pointer stored at that state.
        let retained = |expression: &ProgramExpression| match expression {
            ProgramExpression::Value(ProgramValue::Pointer(read)) => {
                let ProgramValue::Pointer(stored) = &value else {
                    unreachable!()
                };
                read.pointer() != stored.pointer()
                    && PureFactContext::new().equality_graph.knows_condition(
                        &ConditionTerm::PointerValueEqual(
                            Box::new(read.clone()),
                            Box::new(stored.clone()),
                        ),
                        true,
                    )
            }
            _ => false,
        };
        assert!(retained(&expression), "{expression:?}");
        let address = ProgramExpression::AddressOf(Box::new(field.clone()));
        let mut expression = address.clone();
        resolve(&mut expression);
        assert_eq!(
            expression, address,
            "an address must not become a retained value"
        );
        let mut expression = ProgramExpression::Load(Box::new(field.clone()));
        resolve(&mut expression);
        assert!(
            matches!(&expression, ProgramExpression::Load(inner) if retained(inner)),
            "{expression:?}"
        );
        assert!(!state.memory.has_block(&slot.block));
        assert!(state.resources().facts().is_empty());
    }
    assert!(work.windows(2).all(|pair| pair[0] == pair[1]), "{work:?}");
}
