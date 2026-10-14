use super::*;
use crate::surface::C0VerificationSession;

const ARTIFACT: &[u8] = include_bytes!("../../../../design/charon-trial/split-slices/split.ullbc");
const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/split-slices/split.rs");
const CLAIM: &str = include_str!("../../../../design/charon-trial/split-slices/split.click");

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn charon_split_at_preserves_both_shared_slices_and_original_proofs() {
    assert_eq!(
        SOURCE,
        include_bytes!("../../../../examples/rust-split-at/split.rs")
    );
    assert_eq!(
        CLAIM,
        include_str!("../../../../examples/rust-split-at/split.click")
    );
    let export = decode(ARTIFACT, "split.rs", SOURCE).unwrap();
    for f in &export.functions {
        let mir = f.mir.as_ref().unwrap();
        let split = mir
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find_map(|s| match s {
                S::SliceSplit { left, right, .. } => Some((left, right)),
                _ => None,
            })
            .unwrap();
        assert_ne!(split.0, split.1);
        for name in [split.0, split.1] {
            assert!(
                mir.locals.iter().any(
                    |p| p.name == *name && p.value_type == (Type::ByteSlice { mutable: false })
                )
            );
        }
    }
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    C0VerificationSession::new_program_prepared(CLAIM, &prepared).unwrap();
    for bad in [
        CLAIM.replace("requires mid <= bytes.len();", ""),
        CLAIM.replace("views bytes[0..bytes.len()];", ""),
        CLAIM.replace("ensures result == mid;", "ensures result != mid;"),
        CLAIM.replace(
            "ensures result == bytes[mid];",
            "ensures result != bytes[mid];",
        ),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&bad, &prepared).is_err(),
            "{bad}"
        );
    }
}

#[test]
fn charon_split_at_rejects_forged_declarations_and_tuple_projections() {
    for mutation in 0..13 {
        let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let krate = &mut artifact.data.translated;
        let id = krate.fun_decls.iter_indexed().find(|(_, f)| matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(name, _)) if name == "split_at")).unwrap().0;
        match mutation {
            0 => {
                krate.fun_decls[id].item_meta.name.name[0] =
                    a::PathElem::Ident("fake".into(), a::Disambiguator::ZERO)
            }
            1 => krate.fun_decls[id].signature.is_unsafe = true,
            2 => krate.fun_decls[id].signature.is_variadic = true,
            3 => krate.fun_decls[id].generics.types.clear(),
            4 => krate.fun_decls[id].signature.inputs.swap(0, 1),
            5 => krate.fun_decls[id].signature.output.with_kind_mut(|kind| {
                let a::TyKind::Adt(r) = kind else { panic!() };
                r.builtin = None;
            }),
            6 => krate.fun_decls[id].signature.output.with_kind_mut(|kind| {
                let a::TyKind::Adt(r) = kind else { panic!() };
                r.generics.types[1].with_kind_mut(|kind| {
                    let a::TyKind::Ref(_, _, mutability) = kind else {
                        panic!()
                    };
                    *mutability = a::RefKind::Mut;
                });
            }),
            7..=9 | 12 => {
                let a::Body::Unstructured(body) = &mut krate.fun_decls[a::FunDeclId::ZERO].body
                else {
                    panic!()
                };
                let u::TerminatorKind::Call { call, .. } =
                    &mut body.body[u::BlockId::ZERO].terminator.kind
                else {
                    panic!()
                };
                match mutation {
                    7 => call.safety = a::CallSafety::Unsafe,
                    8 => call.args.swap(0, 1),
                    12 => {
                        let a::FnOperand::Regular(ptr) = &mut call.func else {
                            panic!()
                        };
                        ptr.generics.regions.clear();
                    }
                    9 => {
                        let a::FnOperand::Regular(ptr) = &mut call.func else {
                            panic!()
                        };
                        ptr.generics.types.clear();
                    }
                    _ => unreachable!(),
                }
            }
            10..=11 => {
                let a::Body::Unstructured(body) = &mut krate.fun_decls[a::FunDeclId::ZERO].body
                else {
                    panic!()
                };
                let mut changed = false;
                for s in body.body.iter_mut().flat_map(|b| &mut b.statements) {
                    let u::StatementKind::Assign(_, a::Rvalue::Use(a::Operand::Copy(p), _)) =
                        &mut s.kind
                    else {
                        continue;
                    };
                    let a::PlaceKind::Projection(_, a::ProjectionElem::Field(_, field)) =
                        &mut p.kind
                    else {
                        continue;
                    };
                    if mutation == 10 {
                        *field = a::FieldId::from_usize(2);
                    } else {
                        p.ty.with_kind_mut(|kind| {
                            let a::TyKind::Ref(_, _, mutability) = kind else {
                                panic!()
                            };
                            *mutability = a::RefKind::Mut;
                        });
                    }
                    changed = true;
                    break;
                }
                assert!(changed);
            }
            _ => unreachable!(),
        }
        assert!(
            decode(&serde_json::to_vec(&artifact).unwrap(), "split.rs", SOURCE).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn charon_split_at_checked_byte_reads_do_not_enumerate_slice_extent() {
    let export = decode(ARTIFACT, "split.rs", SOURCE).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let mut previous = None;
    for length in [8, 128, 1024] {
        let sidecar = CLAIM.replace(
            "views bytes[0..bytes.len()];",
            &format!("requires bytes.len() == {length}u64; views bytes[0..bytes.len()];"),
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
