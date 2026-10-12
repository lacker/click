use super::*;
const ARRAYS_SOURCE: &str = include_str!("../../design/charon-trial/array-lengths/arrays.rs");
const ARRAYS_SIDECAR: &str = include_str!("../../design/charon-trial/array-lengths/arrays.click");
const BOUNDS_SOURCE: &str = include_str!("../../design/charon-trial/array-lengths/bounds.rs");
const BOUNDS_SIDECAR: &str = include_str!("../../design/charon-trial/array-lengths/bounds.click");
fn project(bounds: bool) -> Project {
    let p = Project::new("");
    let files: &[(&str, &[u8])] = if bounds {
        &[
            ("bounds.rs", BOUNDS_SOURCE.as_bytes()),
            ("borrow.click", BOUNDS_SIDECAR.as_bytes()),
            (
                "borrow.click.import.json",
                include_bytes!("../../design/charon-trial/array-lengths/bounds.click.import.json"),
            ),
            (
                "bounds.ullbc",
                include_bytes!("../../design/charon-trial/array-lengths/bounds.ullbc"),
            ),
            (
                "borrow.click.import.json.lock",
                include_bytes!(
                    "../../design/charon-trial/array-lengths/bounds.click.import.json.lock"
                ),
            ),
        ]
    } else {
        &[
            ("arrays.rs", ARRAYS_SOURCE.as_bytes()),
            ("borrow.click", ARRAYS_SIDECAR.as_bytes()),
            (
                "borrow.click.import.json",
                include_bytes!("../../design/charon-trial/array-lengths/arrays.click.import.json"),
            ),
            (
                "arrays.ullbc",
                include_bytes!("../../design/charon-trial/array-lengths/arrays.ullbc"),
            ),
            (
                "borrow.click.import.json.lock",
                include_bytes!(
                    "../../design/charon-trial/array-lengths/arrays.click.import.json.lock"
                ),
            ),
        ]
    };
    for (name, bytes) in files {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 2s in the parallel gate; other gate tests reach the same code"]
fn charon_array_lengths_preserve_unchanged_sources_and_reject_false_claims() {
    assert_eq!(
        ARRAYS_SOURCE,
        include_str!("../../examples/rust-arrays/arrays.rs")
    );
    assert_eq!(
        ARRAYS_SIDECAR,
        include_str!("../../examples/rust-arrays/arrays.click")
    );
    for bounds in [false, true] {
        let p = project(bounds);
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = if bounds {
            BOUNDS_SIDECAR
        } else {
            ARRAYS_SIDECAR
        };
        C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
        let invalid = sidecar.replace("ensures result == 0u64;", "ensures result == 1u64;");
        assert_ne!(invalid, sidecar);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_array_lengths_proof_tools_recheck_metadata_and_array_certificates() {
    for bounds in [false, true] {
        let p = project(bounds);
        for command in ["verify", "profile", "audit"] {
            assert_cli(&p, &[command]);
        }
        for claim in if bounds {
            &[
                "signed_len.contract",
                "million_len.contract",
                "empty_len.contract",
            ][..]
        } else {
            &["length.contract", "empty.contract", "update.contract"][..]
        } {
            assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
            assert_cli(&p, &["verify"]);
        }
    }
}
#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_array_lengths_live_refresh_and_compiler_rejections() {
    for bounds in [false, true] {
        let p = project(bounds);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
        config["exporter"] = serde_json::json!(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
        );
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&p.config()).unwrap();
        C0VerificationSession::new_program_prepared(
            if bounds {
                BOUNDS_SIDECAR
            } else {
                ARRAYS_SIDECAR
            },
            load_import(&p.config()).unwrap(),
        )
        .unwrap();
    }
    let p = project(true);
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    for (source, diagnostic) in [
        (
            "pub fn bad(x:&mut [u32;3])->usize { let y=&mut *x; let n=x.len(); y[0]=7; n }",
            "E0502",
        ),
        ("pub fn bad(x:&[u16;3])->usize { x.len() }", "scalar"),
    ] {
        fs::remove_file(p.root.join("bounds.ullbc")).unwrap();
        fs::write(p.root.join("bounds.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("bounds.ullbc").exists());
        fs::write(p.root.join("bounds.rs"), BOUNDS_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}
