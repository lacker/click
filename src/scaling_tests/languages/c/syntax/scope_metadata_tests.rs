// Scaling tests of `src/languages/c/syntax.rs` (module `scope_metadata_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn explicit_embedded_layout_work_tracks_materialized_leaves() {
    for size in [8u32, 32, 128, 256] {
        let (layouts, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut layouts = BTreeMap::new();
            for index in 0..size {
                let mut fields = vec![("stamp".into(), InterfaceType::Int32, None, index * 4, 4)];
                if index != 0 {
                    fields.insert(
                        0,
                        (
                            "state".into(),
                            InterfaceType::Int32,
                            Some(format!("R{}", index - 1)),
                            0,
                            index * 4,
                        ),
                    );
                }
                let layout = RecordLayout::from_explicit_fields_with_structs(
                    fields,
                    (index + 1) * 4,
                    4,
                    &layouts,
                )
                .unwrap();
                assert_eq!(layout.aggregate_fields.len(), index as usize + 1);
                assert_eq!(
                    layout.aggregate_fields.last().unwrap().offset_bytes,
                    index * 4
                );
                layouts.insert(format!("R{index}"), layout);
            }
            layouts
        });
        assert_eq!(layouts.len(), size as usize);
        assert_eq!(work, (size * (size - 1) / 2) as usize);
    }
}

/// Every parsed function keeps the declarations visible at its definition.
/// Those states share one persistent map, so `n` functions after `n`
/// declarations hold one copy of them, not `n`. Interleaved declarations
/// still give each function exactly the ones declared before it.
#[test]
fn function_declaration_states_share_the_translation_unit_maps() {
    for size in [8usize, 32, 128, 512] {
        let mut source = String::new();
        for index in 0..size {
            source.push_str(&format!(
                "struct S{index} {{ int32 a; }};\nint32 g{index};\n"
            ));
        }
        for index in 0..size {
            source.push_str(&format!("int32 f{index}(int32 x) {{ return x; }}\n"));
        }
        let functions = parse_functions(&source).unwrap();
        assert_eq!(functions.len(), size);
        let (structs, globals) = (functions[0].structs(), functions[0].globals());
        assert_eq!((structs.len(), globals.len()), (size, size));
        for function in &functions {
            assert!(function.structs().ptr_eq(structs), "size {size}");
            assert!(function.globals().ptr_eq(globals), "size {size}");
        }

        let mut interleaved = String::new();
        for index in 0..size {
            interleaved.push_str(&format!(
                "struct S{index} {{ int32 a; }};\nint32 f{index}(int32 x) {{ return x; }}\n"
            ));
        }
        let functions = parse_functions(&interleaved).unwrap();
        for (index, function) in functions.iter().enumerate() {
            assert_eq!(function.structs().len(), index + 1, "size {size}");
        }
    }
}

#[test]
fn nested_conditionals_parse_and_lower_on_a_two_megabyte_stack() {
    let mut samples = Vec::new();
    for depth in [4usize, 16, 64, 112, 256] {
        let work = std::thread::Builder::new()
            .name(format!("conditional-frontend-{depth}"))
            .stack_size(2 * 1024 * 1024)
            .spawn(move || {
                let parameters = (0..depth)
                    .map(|i| format!("int32 a{i}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let mut source = format!("int32 caller({parameters}) {{\nint32 s;\ns = 0;\n");
                for i in 0..depth {
                    source.push_str(&format!("if (a{i} > 0) {{\n"));
                }
                source.push_str("s = 1;\n");
                for _ in 0..depth {
                    source.push_str("}\n");
                }
                source.push_str("return s;\n}");
                let ((parsed, lowered), work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        let parsed = parse_function(&source).unwrap();
                        let lowered = parsed.to_kernel_function();
                        (parsed, lowered)
                    });
                let mut pending = vec![lowered.body()];
                let mut branches = 0;
                while let Some(statement) = pending.pop() {
                    match statement {
                        crate::kernel::ProgramStatement::If {
                            then_branch,
                            else_branch,
                            ..
                        } => {
                            branches += 1;
                            pending.push(then_branch);
                            pending.push(else_branch);
                        }
                        crate::kernel::ProgramStatement::Seq(sequence) => {
                            pending.extend(sequence.iter().map(|statement| statement.as_ref()))
                        }
                        _ => {}
                    }
                }
                assert_eq!(branches, depth);
                assert_eq!(parsed.parameters().len(), depth);
                work
            })
            .unwrap()
            .join()
            .unwrap();
        samples.push((depth, work));
    }
    for pair in samples.windows(2) {
        let [(left_size, left_work), (right_size, right_work)] = pair else {
            unreachable!()
        };
        assert!(
            *right_work <= (right_size.div_ceil(*left_size) + 2) * left_work + 4096,
            "conditional frontend work: {samples:?}"
        );
    }
}
