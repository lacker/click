use super::*;
use crate::surface::C0VerificationSession;

const ARTIFACT: &[u8] =
    include_bytes!("../../../../design/charon-trial/into-slices/iteration.ullbc");
const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/into-slices/iteration.rs");
const CLAIM: &str = include_str!("../../../../design/charon-trial/into-slices/iteration.click");

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn charon_slice_into_iter_preserves_actual_typed_state_and_checked_reads() {
    let export = decode(ARTIFACT, "iteration.rs", SOURCE).unwrap();
    for function in export
        .functions
        .iter()
        .filter(|f| f.name.starts_with("first_"))
    {
        let mir = function.mir.as_ref().unwrap();
        assert_eq!(
            mir.blocks
                .iter()
                .flat_map(|b| &b.statements)
                .filter(|s| matches!(s, S::SharedArrayInitialize { .. }))
                .count(),
            1
        );
        assert!(
            mir.locals
                .iter()
                .any(|local| matches!(local.value_type, Type::SharedArrayIterator { .. }))
        );
        assert!(
            !mir.locals
                .iter()
                .any(|local| local.name.contains("processed"))
        );
        assert!(mir.blocks.iter().any(|b| matches!(
            &b.terminator,
            T::If {
                condition: E::SharedArrayHasNext { .. },
                ..
            }
        )));
    }
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    C0VerificationSession::new_program_prepared(CLAIM, &prepared).unwrap();
    let empty = include_str!("../../../../design/charon-trial/into-slices/empty.click");
    C0VerificationSession::new_program_prepared(empty, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &empty.replace("result == 0u32", "result == 1u32"),
            &prepared
        )
        .is_err()
    );
    for bad in [
        CLAIM.replace(
            "ensures result == old(bytes[0]);",
            "ensures result != old(bytes[0]);",
        ),
        CLAIM.replace("views bytes[0..1];", ""),
        CLAIM.replace("views values[0..1];", ""),
    ] {
        assert_ne!(bad, CLAIM);
        assert!(C0VerificationSession::new_program_prepared(&bad, &prepared).is_err());
    }
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn charon_slice_into_iter_rejects_forged_identity_mutability_and_instantiation() {
    for mutation in 0..12 {
        let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let different_element = artifact
            .data
            .translated
            .fun_decls
            .iter()
            .find(|f| {
                f.item_meta.is_local
                    && matches!(
                        f.signature.output.kind(),
                        a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(
                            a::UIntTy::U32
                        )))
                    )
            })
            .unwrap()
            .signature
            .output
            .clone();
        let callee = artifact.data.translated.fun_decls.iter_mut()
            .find(|f| matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(name, _)) if name == "into_iter"))
            .unwrap();
        let callee_id = callee.def_id;
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            ..
        } = &callee.src
        else {
            panic!()
        };
        let trait_id = trait_ref.id;
        let impl_id = impl_ref.id;
        match mutation {
            0 => callee.item_meta.is_local = true,
            1 => callee.signature.is_unsafe = true,
            2 => callee.signature.inputs[0].with_kind_mut(|kind| {
                let a::TyKind::Ref(_, _, mutable) = kind else {
                    panic!()
                };
                *mutable = a::RefKind::Mut;
            }),
            3 => callee.signature.output = callee.signature.inputs[0].clone(),
            4 => {
                artifact.data.translated.trait_decls[trait_id]
                    .item_meta
                    .diagnostic_item = Some("Lookalike".into())
            }
            5 => artifact.data.translated.trait_impls[impl_id].is_negative = true,
            6 => {
                artifact.data.translated.trait_impls[impl_id]
                    .item_meta
                    .name
                    .name[0] = a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
                callee.item_meta.name.name[0] =
                    a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
            }
            7 => callee.generics.types.clear(),
            8 => artifact.data.translated.trait_impls[impl_id]
                .impl_trait
                .generics
                .types[0]
                .with_kind_mut(|kind| {
                    let a::TyKind::Ref(_, _, mutable) = kind else {
                        panic!()
                    };
                    *mutable = a::RefKind::Mut;
                }),
            9..=11 => {
                let mut changed = false;
                'functions: for f in artifact.data.translated.fun_decls.iter_mut() {
                    let a::Body::Unstructured(body) = &mut f.body else {
                        continue;
                    };
                    for block in body.body.iter_mut() {
                        let u::TerminatorKind::Call { call, .. } = &mut block.terminator.kind
                        else {
                            continue;
                        };
                        let a::FnOperand::Regular(ptr) = &mut call.func else {
                            continue;
                        };
                        let selected = match ptr.kind.as_ref() {
                            a::FnPtrKind::Fun(id) => *id == callee_id,
                            a::FnPtrKind::Trait(tr, _) => {
                                matches!(&tr.kind, a::TraitRefKind::TraitImpl(r) if r.id == impl_id)
                            }
                        };
                        if !selected {
                            continue;
                        }
                        match mutation {
                            9 => ptr.generics.types[0] = different_element.clone(),
                            10 => {
                                let (a::Operand::Copy(place) | a::Operand::Move(place)) =
                                    &mut call.args[0]
                                else {
                                    panic!()
                                };
                                place.ty.with_kind_mut(|kind| {
                                    let a::TyKind::Ref(_, _, mutable) = kind else {
                                        panic!()
                                    };
                                    *mutable = a::RefKind::Mut;
                                });
                            }
                            11 => call.safety = a::CallSafety::Unsafe,
                            _ => unreachable!(),
                        }
                        changed = true;
                        break 'functions;
                    }
                }
                assert!(changed);
            }
            _ => unreachable!(),
        }
        assert!(
            decode(
                &serde_json::to_vec(&artifact).unwrap(),
                "iteration.rs",
                SOURCE
            )
            .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn charon_slice_into_iter_reborrow_requires_matching_pointer_and_metadata() {
    let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
    let function = artifact.data.translated.fun_decls.iter_mut()
        .find(|f| f.item_meta.is_local && matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(name, _)) if name == "forward_signed"))
        .unwrap();
    let a::Body::Unstructured(body) = &mut function.body else {
        panic!()
    };
    let mut changed = false;
    for statement in body.body.iter_mut().flat_map(|b| &mut b.statements) {
        let u::StatementKind::Assign(target, a::Rvalue::Ref { ptr_metadata, .. }) =
            &mut statement.kind
        else {
            continue;
        };
        let (a::Operand::Copy(metadata) | a::Operand::Move(metadata)) = ptr_metadata else {
            panic!()
        };
        let a::PlaceKind::Projection(base, a::ProjectionElem::PtrMetadata) = &mut metadata.kind
        else {
            panic!()
        };
        **base = target.clone();
        changed = true;
        break;
    }
    assert!(changed);
    let error = decode(
        &serde_json::to_vec(&artifact).unwrap(),
        "iteration.rs",
        SOURCE,
    )
    .unwrap_err();
    assert!(
        error.contains("slice reborrow pointer/metadata/type mismatch"),
        "{error}"
    );
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn charon_slice_into_iter_work_does_not_depend_on_slice_extent() {
    let export = decode(ARTIFACT, "iteration.rs", SOURCE).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let mut previous = None;
    for length in [8, 128, 1024] {
        let sidecar = format!(
            "verifying \"iteration.rs\"; fn first_byte(bytes: &[u8]) -> u8 {{ requires bytes.len() == {length}u64; views bytes[0..{length}]; ensures result == old(bytes[0]); }} by {{ execute(); simp(); }}"
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&sidecar, &prepared)
        });
        result.unwrap();
        if let Some(previous) = previous {
            assert!(
                work <= previous + 1000,
                "extent {length}: {work}, previous {previous}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn charon_slice_into_iter_many_slice_parameters_lower_with_linear_charged_work() {
    for count in [8, 128, 1024] {
        let mut export = decode(ARTIFACT, "iteration.rs", SOURCE).unwrap();
        export.functions.retain(|f| f.name == "first_signed");
        let function = &mut export.functions[0];
        let parameter = function.parameters[0].clone();
        for index in 0..count {
            let mut parameter = parameter.clone();
            parameter.name = format!("extra_{index}");
            function.parameters.push(parameter);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::lowering::lower(&export)
        });
        let (functions, _) = result.unwrap();
        assert_eq!(functions[0].parameters().len(), 2 * (count + 1));
        assert!(work <= 4 * count + 1000, "{count} slice parameters: {work}");
    }
}
