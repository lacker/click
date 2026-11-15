use super::*;

// Prepare the original native function outside the constrained execution
// thread so this test isolates proof execution. The proof and all kernel
// state are constructed and executed on the two-megabyte thread.
#[test]
#[ignore = "nightly: deep focused execution on a constrained stack"]
fn focused_execute_handles_deep_branches_on_a_two_megabyte_stack() {
    for depth in [4, 32, 112, 256] {
        let parameters = (0..depth)
            .map(|i| format!("int32 a{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let mut c = format!("int32 caller({parameters}) {{ int32 s; s = 0; ");
        for i in 0..depth {
            c.push_str(&format!("if (a{i} > 0) {{ "));
        }
        c.push_str("s = 1;");
        c.extend(std::iter::repeat_n('}', depth));
        c.push_str("return s; }");
        let (parsed_function, function, layout) = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let parsed = syntax::parse_function(&c).unwrap();
                let function = parsed.to_kernel_function();
                let layout = SourceExecutionLayout::new(parsed.body());
                (parsed, function, layout)
            })
            .unwrap()
            .join()
            .unwrap();
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name(format!("focused-execute-{depth}"))
                .stack_size(2 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    let source = format!("int32 caller({parameters}) {{ ensures result >= 0; }}");
                    let click_file = crate::surface::parse(&source).unwrap();
                    let function_block = &click_file.function_blocks()[0];
                    let predicates = PredicateEnvironment::new(&[]);
                    let functions = ClickFunctionEnvironment::new(&[]);
                    let theorems = TheoremEnvironment::new(&[]);
                    let resources = ResourceEnvironment::new(&[]);
                    let environment = ExecutionEnvironment::new();
                    let arguments = (0..depth)
                        .map(|i| {
                            ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Variable(
                                Variable(771_000 + i as u64),
                            )))
                        })
                        .collect::<Vec<_>>();
                    let root = Proof::for_execution_frontier(
                        "deep focused execution",
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
                            source_layout: layout.clone(),
                            ..ExecutionProofConstants::default()
                        },
                        function_block,
                        &function,
                        &parsed_function,
                        &arguments,
                        &environment,
                        &resources,
                        SpecDefinitions::new(&predicates, &functions),
                        &theorems,
                    );
                    let executed = root
                        .try_focused_execute_to_exit()
                        .unwrap()
                        .expect("every original nested-if path reaches function exit");
                    assert!(executed.is_at_function_exit(), "depth {depth}");
                })
                .unwrap()
                .join()
                .unwrap();
        });
    }
}
