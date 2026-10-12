use super::*;
use crate::surface::C0VerificationSession;

#[test]
fn rust_record_field_selection_shares_layout_and_decays_declared_array() {
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let names = (0..count).map(|i| format!("other{i}")).collect::<Vec<_>>();
        let mut declarations = vec![("words".into(), C0Type::UInt32Array(2), 0, 8)];
        declarations.extend(
            names
                .iter()
                .enumerate()
                .map(|(i, name)| (name.clone(), C0Type::Int32, 8 + i as u32 * 4, 4)),
        );
        let layouts = BTreeMap::from([(
            "Record".into(),
            C0StructLayout::from_explicit_fields(declarations, 8 + count * 4, 4).unwrap(),
        )]);
        let mut fields = BTreeMap::from([(("Record", "words"), (0, CType::UInt32Array(2)))]);
        fields.extend(
            names
                .iter()
                .enumerate()
                .map(|(i, name)| (("Record", name.as_str()), (8 + i as u32 * 4, CType::Int32))),
        );
        let records = BTreeMap::new();
        let functions = BTreeMap::new();
        let mut cx = Context {
            shared_array_iterators: BTreeMap::new(),
            shared_array_options: BTreeMap::new(),
            shared_scalar_slices: BTreeMap::new(),
            chunk_iterators: BTreeSet::new(),
            mir_chunk_iterators: BTreeSet::new(),
            chunk_options: BTreeSet::new(),
            local_arrays: BTreeSet::new(),
            owned_locals: BTreeSet::from(["object".into()]),
            slices: BTreeMap::new(),
            arrays: BTreeMap::new(),
            references: BTreeMap::new(),
            source: "fields.rs",
            function: "selected",
            fields: &fields,
            next_load: 0,
            next_temporary: 0,
            locals: BTreeSet::from(["object".into()]),
            return_type: C0Type::Void,
            layouts: &layouts,
            selected_layouts: BTreeMap::new(),
            records: &records,
            functions: &functions,
        };
        let place = E::Field {
            base: Box::new(E::Local {
                name: "object".into(),
            }),
            record: "Record".into(),
            field: "words".into(),
        };
        let CExpression::MemberAddress {
            selection: first, ..
        } = cx.address(&place).unwrap()
        else {
            panic!("native field must retain its declared selection");
        };
        let borrowed = cx
            .expr(&E::Borrow {
                place: Box::new(place.clone()),
                value_type: Type::Reference {
                    mutable: false,
                    pointee: Box::new(Type::Array {
                        element: Box::new(Type::U32),
                        length: 2,
                    }),
                },
            })
            .unwrap();
        let mut borrowed = &borrowed;
        while let CExpression::Cast { expression, .. } = borrowed {
            borrowed = expression;
        }
        assert!(matches!(borrowed,
            CExpression::TypedLoad { value_type: CType::UInt32Array(2), pointer, .. }
                if matches!(pointer.as_ref(), CExpression::MemberAddress { selection, .. }
                    if Arc::ptr_eq(&first.layout, &selection.layout))));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..64 {
                let (pointer, length, element) = cx.indexed_parts(&place).unwrap();
                assert_eq!(length, c_uint64_literal(2));
                assert_eq!(element, CType::UInt32);
                let CExpression::Cast {
                    expression,
                    target_type,
                    ..
                } = pointer
                else {
                    panic!("expected element-pointer qualification");
                };
                assert_eq!(target_type, CType::UInt32Pointer);
                let CExpression::TypedLoad {
                    pointer,
                    value_type,
                    ..
                } = *expression
                else {
                    panic!("array elements require declared array decay");
                };
                assert_eq!(value_type, CType::UInt32Array(2));
                let CExpression::MemberAddress { selection, .. } = *pointer else {
                    panic!("array decay must keep native member selection");
                };
                assert!(Arc::ptr_eq(&first.layout, &selection.layout));
                assert_eq!(selection.path(), &["words".to_owned()]);
            }
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn charon_array_reference_assignments_preserve_bounded_storage_and_proof_work() {
    fn shape(s: &CStatement) -> (usize, usize) {
        match s {
            CStatement::Seq(a, b) => {
                let a = shape(a);
                let b = shape(b);
                (1 + a.0 + b.0, a.1 + b.1)
            }
            CStatement::DeclareAggregate { layout, .. } => {
                assert!(
                    layout.fields().is_empty(),
                    "array storage must stay compact"
                );
                (1, 0)
            }
            CStatement::InitializeScalarArray { fresh: false, .. } => (1, 1),
            _ => (1, 0),
        }
    }
    let export = super::super::charon::decode(
        include_bytes!("../../../../design/charon-trial/array-values/bounds.ullbc"),
        "bounds.rs",
        include_bytes!("../../../../design/charon-trial/array-values/bounds.rs"),
    )
    .unwrap();
    let (functions, _) = lower(&export).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    for family in ["fill", "copy"] {
        let mut samples = Vec::new();
        for tag in ["small", "medium", "million"] {
            let _session = crate::kernel::VerificationSession::enter();
            let name = format!("{family}_{tag}");
            let function = functions
                .iter()
                .find(|f| f.name() == name)
                .unwrap()
                .to_kernel_function();
            let shape = shape(function.body());
            assert!(
                shape.1 >= 1,
                "must execute a checked reference region write"
            );
            let sidecar = format!(
                "verifying \"bounds.rs\"; fn {name}() -> u32 {{ ensures result == 7u32; }} by {{ execute(); simp(); }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            });
            verified.unwrap();
            samples.push((shape, work));
        }
        assert!(
            samples
                .iter()
                .all(|(shape, work)| *shape == samples[0].0 && *work <= samples[0].1 + 64),
            "{family}: {samples:?}"
        );
    }
}

#[test]
fn charon_external_array_operations_keep_lowering_and_proof_work_bounded() {
    let export = super::super::charon::decode(
        include_bytes!("../../../../design/charon-trial/array-values/external.ullbc"),
        "external.rs",
        include_bytes!("../../../../design/charon-trial/array-values/external.rs"),
    )
    .unwrap();
    let (functions, _) = lower(&export).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    fn statements(statement: &CStatement) -> usize {
        match statement {
            CStatement::Seq(a, b) => 1 + statements(a) + statements(b),
            _ => 1,
        }
    }
    for family in ["copy", "fill"] {
        let mut samples = Vec::new();
        for (tag, count) in [("small", 8), ("medium", 1024), ("million", 1_000_000)] {
            let _session = crate::kernel::VerificationSession::enter();
            let name = format!("{family}_{tag}");
            let function = functions
                .iter()
                .find(|f| f.name() == name)
                .unwrap()
                .to_kernel_function();
            let (parameters, contract) = if family == "copy" {
                (
                    format!("target: &mut [u32; {count}], source: &[u32; {count}]"),
                    format!(
                        "views source[0..{count}]; ensures target[0] == old(source[0]); ensures target[{}] == old(source[{}]);",
                        count - 1,
                        count - 1
                    ),
                )
            } else {
                (
                    format!("target: &mut [u32; {count}], value: u32"),
                    format!(
                        "ensures target[0] == value; ensures target[{}] == value;",
                        count - 1
                    ),
                )
            };
            let sidecar = format!(
                "verifying \"external.rs\"; fn {name}({parameters}) {{ owns target[0..{count}]; {contract} }} by {{ execute(); simp(); }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            });
            verified.unwrap();
            samples.push((statements(function.body()), work));
        }
        assert!(
            samples
                .iter()
                .all(|(shape, work)| *shape == samples[0].0 && *work <= samples[0].1 + 128),
            "{family}: {samples:?}"
        );
    }
}
