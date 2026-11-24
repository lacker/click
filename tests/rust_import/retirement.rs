use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_default_is_native_charon() {
    let p = Project::new(SOURCE);
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .all(|f| f.mir.is_some() && f.body.is_empty())
    );
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
}

#[test]
fn rust_default_conditional_solve_expansion_reverifies() {
    let p = gate_fixtures::project("basic", SOURCE);
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    let expanded =
        click::surface::expand_program_prepared_tactic_source_at(SIDECAR, &prepared, 5, 5).unwrap();
    ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn rust_import_pure_theorem_claim_labels_expand_and_reverify() {
    use click::surface::{ClickModuleSource, ClickProject};

    let p = gate_fixtures::project("basic", SOURCE);
    let prepared = p.prepared().unwrap();
    let source = format!(
        "{SIDECAR}\ntheorem mixed(n: int32) {{\n\
         ensures n == n by {{ close(); }}\n\
         ensures ordered: n <= n by {{ close(); }}\n\
         }}\n"
    );
    ProgramVerificationSession::new_program_prepared(&source, &prepared).unwrap();
    let project_for = |source: &str| {
        ClickProject::new(
            "borrow.click",
            [ClickModuleSource::new("borrow.click", source, [])],
        )
    };
    for label in ["mixed.ensures_0", "mixed.ordered"] {
        let expanded = click::surface::expand_program_prepared_claim_source_by_label(
            &source, &prepared, label,
        )
        .unwrap();
        assert_ne!(expanded, source);
        ProgramVerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
        let expanded = click::surface::expand_project_claim_source_by_label(
            &project_for(&source),
            &click::surface::ProgramInputs::program(&prepared),
            label,
        )
        .unwrap();
        ProgramVerificationSession::new_program_prepared_project(
            &project_for(&expanded),
            &prepared,
        )
        .unwrap();
    }
    let invalid = source.replace("ensures n == n", "ensures n == n + 1");
    assert!(
        click::surface::expand_program_prepared_claim_source_by_label(
            &invalid,
            &prepared,
            "mixed.ensures_0",
        )
        .is_err()
    );
    assert!(
        click::surface::expand_project_claim_source_by_label(
            &project_for(&invalid),
            &click::surface::ProgramInputs::program(&prepared),
            "mixed.ensures_0"
        )
        .is_err()
    );
}
