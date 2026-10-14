use super::*;

fn project(name: &str) -> Project {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/split-slices");
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
#[ignore = "nightly: 2.1s in the parallel gate"]
fn charon_split_at_empty_endpoints_and_full_width_lengths() {
    let p = project("split");
    let prepared = load_import(&p.config()).unwrap();
    for claim in [
        include_str!("../../design/charon-trial/split-slices/empty.click"),
        include_str!("../../design/charon-trial/split-slices/endpoints.click"),
    ] {
        C0VerificationSession::new_program_prepared(claim, &prepared).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(
                &claim.replace("result == 0u64", "result == 1u64"),
                &prepared
            )
            .is_err()
        );
    }
    for (length, mid) in [
        (0u64, 0u64),
        (4, 0),
        (4, 4),
        (2147483647, 2147483647),
        (4294967296, 1),
        (u64::MAX, 0),
    ] {
        let claim = format!(
            "verifying \"split.rs\"; fn right_length(bytes: &[u8], mid: usize) -> usize {{ requires bytes.len() == {length}u64; requires mid == {mid}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length - mid
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for claim in [
        "verifying \"split.rs\"; fn left_length(bytes: &[u8], mid: usize) -> usize { requires bytes.len() == 0u64; requires mid == 1u64; ensures result == 1u64; } by { execute(); simp(); }",
        "verifying \"split.rs\"; fn left_first(bytes: &[u8], mid: usize) -> u8 { requires bytes.len() == 0u64; requires mid == 0u64; ensures result == 0; } by { execute(); simp(); }",
    ] {
        assert!(C0VerificationSession::new_program_prepared(claim, &prepared).is_err());
    }
}

#[test]
fn charon_split_at_original_tools_agree() {
    let p = project("split");
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_split_at_copy_tools_and_expansion_agree() {
    let p = project("copies");
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_right.contract",
        "reassign_left.contract",
        "collision.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

fn expand_original(claim: &str) {
    let p = project("split");
    assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    assert_cli(&p, &["verify"]);
}
#[test]
#[ignore = "nightly: 3s in the parallel gate; charon_split_at_original_tools_agree reaches the same code"]
fn charon_split_at_expand_left_length() {
    expand_original("left_length.contract");
}
#[test]
#[ignore = "nightly: 4s in the parallel gate; charon_split_at_original_tools_agree reaches the same code"]
fn charon_split_at_expand_right_length() {
    expand_original("right_length.contract");
}
#[test]
#[ignore = "nightly: 3s in the parallel gate; charon_split_at_original_tools_agree reaches the same code"]
fn charon_split_at_expand_left_first() {
    expand_original("left_first.contract");
}
#[test]
#[ignore = "nightly: 4s in the parallel gate; charon_split_at_original_tools_agree reaches the same code"]
fn charon_split_at_expand_right_first() {
    expand_original("right_first.contract");
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_split_at_live_refresh_and_rejected_mutable_or_nonbyte_pairs() {
    for name in ["split", "copies"] {
        let p = project(name);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
        config["exporter"] = serde_json::json!(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
        );
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        C0VerificationSession::new_program_prepared(
            &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
            &prepared,
        )
        .unwrap();
        for source in [
            "pub fn bad(bytes: &mut [u8], mid:usize)->usize { let pair=bytes.split_at_mut(mid); pair.0.len() }",
            "pub fn bad(values: &[u32], mid:usize)->usize { let pair=values.split_at(mid); pair.0.len() }",
            "pub fn bad(bytes: &[u8], mid:usize)->(&[u8], &[u8]) { bytes.split_at(mid) }",
        ] {
            fs::write(p.root.join(format!("{name}.rs")), source).unwrap();
            let artifact = fs::read(p.root.join(format!("{name}.ullbc"))).unwrap();
            let lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
            assert!(refresh_import(&p.config()).is_err());
            assert_eq!(
                fs::read(p.root.join(format!("{name}.ullbc"))).unwrap(),
                artifact
            );
            assert_eq!(
                fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
                lock
            );
        }
    }
}
