// Scaling tests of `src/surface/proof/theorem_application.rs` (module `observed_integer_argument_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_theorem_argument_capture_scales_with_unused_bindings_and_applications() {
    let mut work_samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let source = "theorem reflexive(z: Integer) { ensures z == z by close(); }";
        let parsed = crate::surface::parser::parse_file_items(source).unwrap();
        let theorem = &parsed.theorem_definitions()[0];
        let application = TheoremApplication {
            name: "reflexive".into(),
            arguments: vec![ContractExpression::Call {
                name: "to_integer".into(),
                arguments: vec![ContractExpression::Binding("x".into())],
            }],
        };
        let mut state = ExecutionState::new().with_local("x", int32(7u32));
        let mut values = ProgramValueBindings::new();
        values.insert("x".into(), int32(7));
        for i in 0..size {
            let name = format!("unused_{i}");
            state = state.with_local(name.clone(), int32(i as u32));
            values.insert(name, int32(i as u32));
        }
        let array_refs = BTreeMap::new();
        let algebraic_values = BTreeMap::new();
        let integer_values = PersistentBinderMap::default();
        let retained_states = RecordedStates::default();
        let context = TheoremApplicationContext {
            parameters: ParameterBinding::default(),
            values: &values,
            array_refs: &array_refs,
            algebraic_values: &algebraic_values,
            pre_state: &state,
            post_state: &state,
            result: None,
            recorded_states: &retained_states,
            integer_values: &integer_values,
            pointer_element_widths: BTreeMap::new(),
        };
        let assumptions = PureFactContext::new();
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let spec_definitions = SpecDefinitions::new(&predicates, &functions);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            theorem_application_bindings(
                theorem,
                &application,
                &context,
                &assumptions,
                spec_definitions,
            )
        });
        let (_, _, _, bound) = result.unwrap();
        assert_eq!(
            bound.get("z"),
            Some(&crate::kernel::SpecIntegerExpression::Term(
                crate::kernel::IntegerTerm::constant_i64(7)
            ))
        );
        work_samples.push(work);
        let (result, repeated_work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                theorem_application_bindings(
                    theorem,
                    &application,
                    &context,
                    &assumptions,
                    spec_definitions,
                )?;
            }
            Ok::<_, String>(())
        });
        result.unwrap();
        assert_eq!(repeated_work, size * work);
    }
    assert!(
        work_samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{work_samples:?}"
    );
}
