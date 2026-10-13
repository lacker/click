use super::*;

fn project(name: &str) -> Project {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/into-slices");
    let p = Project::new("");
    for (destination, original) in [
        (format!("{name}.rs"), format!("{name}.rs")),
        (format!("{name}.ullbc"), format!("{name}.ullbc")),
        ("borrow.click".into(), format!("{name}.click")),
        (
            "borrow.click.import.json".into(),
            format!("{name}.click.import.json"),
        ),
        (
            "borrow.click.import.json.lock".into(),
            format!("{name}.click.import.json.lock"),
        ),
    ] {
        fs::write(
            p.root.join(destination),
            fs::read(root.join(original)).unwrap(),
        )
        .unwrap();
    }
    p
}

#[test]
fn charon_slice_into_iter_imports_unchanged_sum_and_tracks_the_remaining_proof_gap() {
    assert_eq!(
        include_str!("../../design/charon-trial/into-slices/sum.rs"),
        include_str!("../../examples/rust-iterators/sum.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/into-slices/sum.click"),
        include_str!("../../design/charon-trial/iterator-proof/rust-iterators/frozen.click")
    );
    let p = project("sum");
    let prepared = load_import(&p.config()).unwrap();
    let error = C0VerificationSession::new_program_prepared(
        &super::parity::frozen_proof_input(
            &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
        ),
        &prepared,
    )
    .err()
    .unwrap();
    assert!(
        error
            .message()
            .contains("unbound variable `__rust_iter_3_5_remaining`"),
        "{error:?}"
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_slice_into_iter_tools_agree_on_typed_reads_empty_inputs_and_expansion() {
    let p = project("iteration");
    let prepared = load_import(&p.config()).unwrap();
    let empty = include_str!("../../design/charon-trial/into-slices/empty.click");
    C0VerificationSession::new_program_prepared(empty, &prepared).unwrap();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "first_byte.contract",
        "first_signed.contract",
        "first_unsigned.contract",
        "forward_signed.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_slice_into_iter_live_refresh_and_rejected_mutable_or_owned_shapes() {
    for name in ["sum", "iteration"] {
        let p = project(name);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
        config["exporter"] = serde_json::json!(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
        );
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        if name == "sum" {
            let error = C0VerificationSession::new_program_prepared(
                &super::parity::frozen_proof_input(
                    &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
                ),
                &prepared,
            )
            .err()
            .unwrap();
            assert!(
                error
                    .message()
                    .contains("unbound variable `__rust_iter_3_5_remaining`"),
                "{error:?}"
            );
            continue;
        }
        C0VerificationSession::new_program_prepared(
            &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
            &prepared,
        )
        .unwrap();
        C0VerificationSession::new_program_prepared(
            include_str!("../../design/charon-trial/into-slices/empty.click"),
            &prepared,
        )
        .unwrap();
        for source in [
            "pub fn bad(values: &mut [i32]) { for value in values { *value = 0; } }",
            "pub fn bad(values: [u32;4])->u32 { let mut x=0; for value in values { x ^= value; } x }",
            "pub fn bad(values: &[i32]) { for value in values { *value = 0; } }",
            "pub fn bad(values: &[i32])->i32 { for &value in values.iter().rev() { return value; } 0 }",
            "pub fn bad(values: &[i32], values_len: usize)->i32 { for &value in values { return value; } 0 }",
        ] {
            fs::write(p.root.join("iteration.rs"), source).unwrap();
            let old_artifact = fs::read(p.root.join("iteration.ullbc")).unwrap();
            let old_lock =
                fs::read(p.config().with_file_name("borrow.click.import.json.lock")).unwrap();
            assert!(refresh_import(&p.config()).is_err());
            assert_eq!(
                fs::read(p.root.join("iteration.ullbc")).unwrap(),
                old_artifact
            );
            assert_eq!(
                fs::read(p.config().with_file_name("borrow.click.import.json.lock")).unwrap(),
                old_lock
            );
        }
    }
}
