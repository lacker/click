//! The same logical span proof for both pinned standard libraries.

use std::{fs, path::Path};

use click::cli::read_click_project;
use click::languages::cpp::PreparedCppImport;
use click::surface::{
    ProgramInputs, expand_project_claim_source_by_label, verify_program_prepared_project,
    without_implicit_solve,
};

pub const CPP: &str = include_str!("../fixtures/span-by-value/span-probe.cpp");
const PROOF: &str = include_str!("../fixtures/span-by-value/span.click");

pub fn check(root: &Path, import: &PreparedCppImport) {
    let path = root.join("span.click");
    fs::write(&path, PROOF).unwrap();
    let mut project = read_click_project(&path, PROOF).unwrap();
    let inputs = ProgramInputs::program(import);
    for label in ["is_empty.contract", "probe.contract"] {
        let expanded = expand_project_claim_source_by_label(&project, &inputs, label)
            .unwrap_or_else(|error| panic!("{}", error.report()));
        for layout_access in [
            "__data_",
            "__size_",
            "_M_ptr",
            "_M_extent",
            "std_span_data(",
            "std_span_size(",
        ] {
            assert!(!expanded.contains(layout_access), "{expanded}");
        }
        project = project.with_entry_source(expanded);
    }
    without_implicit_solve(|| verify_program_prepared_project(&project, import))
        .unwrap_or_else(|error| panic!("{}", error.report()));

    for (changed, refusal) in [
        (
            PROOF.replace(
                "step(is_empty, { state: copied })",
                "step(is_empty, { state: input })",
            ),
            "named resource instance does not match",
        ),
        (
            PROOF.replace(
                "    step(is_empty, { state: copied });",
                r#"    step(is_empty, { state: copied });
    have exists (backing: int32*) { viewable(backing[0..1]) } by {
        witness(input.data);
        close();
    }"#,
            ),
            "current goal is a memory-viewability fact",
        ),
    ] {
        let project = read_click_project(&path, &changed).unwrap();
        let error = verify_program_prepared_project(&project, import)
            .expect_err("the span copy must not establish this claim");
        assert!(error.message().contains(refusal), "{}", error.report());
    }
}
