use super::*;

#[test]
fn post_execution_fold_body_proofs_expand_and_retain() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/fold_by_after_execute_checks_body.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c_claim_source(source, &sources, "probe", ContractProofClaim::Grouped).unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    let invalid = source.replace("by { close(); }", "by { have n < 0 by close(); close(); }");
    assert!(verify_c_sources(&invalid, &sources).is_err());
    let (session, _) = ProgramVerificationSession::new(source, &sources).unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.find("ensures result").unwrap());
    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    let position = expansion::position_at_offset(&invalid, invalid.find("ensures result").unwrap());
    assert!(
        session
            .verify_at(&invalid, position.line, position.column)
            .is_err()
    );
}
