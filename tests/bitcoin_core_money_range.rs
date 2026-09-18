//! Hermetic re-export of the pinned Bitcoin Core v31.1 MoneyRange fixture.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use click::cli::read_click_project;
use click::instrumentation::{self, VerificationEvent};
use click::languages::cpp::{load_import, refresh_import};
use click::surface::{
    C0VerificationSession, cpp_prepared_project_smart_tactic_source_sites,
    cpp_prepared_project_tactic_source_position, expand_cpp_prepared_project_claim_source_by_label,
    expand_cpp_prepared_project_tactic_source_at, verify_cpp_prepared_project,
};
use sha2::{Digest, Sha256};

const ARCHIVE: &[u8] =
    include_bytes!("../integrations/bitcoin-core-money-range/input-closure.tar.gz");
const PROVENANCE: &str =
    include_str!("../integrations/bitcoin-core-money-range/fixture-provenance.json");
const COMMAND: &str =
    include_str!("../integrations/bitcoin-core-money-range/feerate-command.json.in");
const SIDECAR: &str = include_str!("../integrations/bitcoin-core-money-range/MoneyRange.click");

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn output(program: &Path, args: &[&str]) -> String {
    let result = Command::new(program).args(args).output().unwrap();
    assert!(
        result.status.success(),
        "{} {:?} failed: {}",
        program.display(),
        args,
        String::from_utf8_lossy(&result.stderr)
    );
    String::from_utf8(result.stdout).unwrap().trim().to_owned()
}

fn pinned_clang() -> PathBuf {
    let llvm_config = std::env::var_os("LLVM_CONFIG")
        .map(PathBuf::from)
        .or_else(|| {
            [
                "/usr/bin/llvm-config-19",
                "/usr/lib/llvm-19/bin/llvm-config",
                "/opt/homebrew/opt/llvm@19/bin/llvm-config",
            ]
            .into_iter()
            .map(PathBuf::from)
            .find(|path| path.is_file())
        })
        .expect("scripts/check.sh requires LLVM 19.1.7");
    assert_eq!(output(&llvm_config, &["--version"]), "19.1.7");
    let clang = std::env::var_os("CLANGXX")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(output(&llvm_config, &["--bindir"])).join("clang++"));
    assert!(
        output(&clang, &["--version"])
            .lines()
            .next()
            .unwrap_or_default()
            .contains("19.1.7")
    );
    clang
}

#[test]
fn pinned_upstream_money_range_reexports_and_verifies_in_normal_gate() {
    let manifest: serde_json::Value = serde_json::from_str(PROVENANCE).unwrap();
    assert_eq!(
        manifest["bitcoin_commit"],
        "9be056a8a72b624dae9623b2f7bded92c2a21c91"
    );
    assert_eq!(
        manifest["source_lock_identity"],
        "6552230b6f93c1d81c0344523d624088e3962899c7fddfd0397b0cc09461aa38"
    );
    assert_eq!(
        manifest["input_closure_sha256"],
        "fceeaef86784f820339f6dc3fc24992eb9c6bcf52edccbf6b7869d79296a3c7d"
    );
    assert_eq!(manifest["input_closure_sha256"], sha256(ARCHIVE));
    let root =
        std::env::temp_dir().join(format!("click-bitcoin-money-range-{}", std::process::id()));
    fs::create_dir(&root).expect("fixture directory must not already exist");
    let archive_path = root.join("input-closure.tar.gz");
    fs::write(&archive_path, ARCHIVE).unwrap();
    let tar = Command::new("tar")
        .args([
            "-xzf",
            archive_path.to_str().unwrap(),
            "-C",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        tar.status.success(),
        "{}",
        String::from_utf8_lossy(&tar.stderr)
    );
    let amount = root.join("bitcoin-src/src/consensus/amount.h");
    let feerate = root.join("bitcoin-src/src/policy/feerate.cpp");
    assert_eq!(
        manifest["amount_sha256"],
        sha256(&fs::read(&amount).unwrap())
    );
    assert_eq!(
        manifest["feerate_sha256"],
        sha256(&fs::read(&feerate).unwrap())
    );
    fs::create_dir_all(root.join("bitcoin-build/src")).unwrap();

    let clang = pinned_clang();
    let resource_dir = output(&clang, &["-print-resource-dir"]);
    let database = COMMAND
        .replace("@ROOT@", root.to_str().unwrap())
        .replace("@CLANGXX@", clang.to_str().unwrap())
        .replace("@RESOURCE_DIR@", &resource_dir);
    assert!(!database.contains("@ROOT@"));
    assert!(!database.contains("@CLANGXX@"));
    assert!(!database.contains("@RESOURCE_DIR@"));
    fs::write(root.join("compile_commands.json"), database).unwrap();
    let exporter = std::env::var("CLICK_CPP_EXPORTER")
        .expect("scripts/check.sh supplies the pinned C++ exporter");
    let config_path = root.join("MoneyRange.click.import.json");
    let config = serde_json::json!({
        "schema": 6,
        "language": "c++",
        "standard": "c++20",
        "target": "x86_64-unknown-linux-gnu",
        "exceptions": true,
        "rtti": true,
        "exporter": exporter,
        "compilation_database": "compile_commands.json",
        "working_directory": ".",
        "source": "bitcoin-src/src/policy/feerate.cpp",
        "logical_source": "bitcoin-src/src/consensus/amount.h",
        "dependencies": [
            "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
            "sysroot/usr/include/x86_64-linux-gnu/bits/types.h"
        ],
        "function": "MoneyRange",
        "artifact": "MoneyRange.click-cpp.json"
    });
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    let sidecar = root.join("MoneyRange.click");
    fs::write(&sidecar, SIDECAR).unwrap();

    refresh_import(&config_path)
        .expect("re-export unchanged Bitcoin source under the pinned CMake command");
    let imported = load_import(&config_path).expect("load the locked upstream import");
    assert_eq!(imported.export().preprocessor_files.len(), 320);
    assert!(
        imported
            .export()
            .profile
            .frontend_version
            .contains("19.1.7")
    );
    assert_eq!(imported.export().profile.standard, "c++20");
    assert_eq!(imported.export().profile.target, "x86_64-unknown-linux-gnu");
    let max_money = imported
        .export()
        .constants
        .iter()
        .find(|constant| constant.name == "MAX_MONEY")
        .expect("the upstream bound is imported from its C++ declaration");
    assert_eq!(max_money.evaluated_value, "2100000000000000");
    let project = read_click_project(&sidecar, SIDECAR).unwrap();
    // The one integration fixture owes termination evidence like every other
    // corpus fixture; it has no loop and no callee, so it owes no measure.
    let (verification, profile) =
        instrumentation::collect(|| verify_cpp_prepared_project(&project, &imported));
    verification.expect("verify the exact inclusive range contract and four boundary calls");
    let finished_claims = profile
        .iter()
        .filter_map(|event| match event {
            VerificationEvent::ClaimFinished { key, .. } => Some(key.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !finished_claims.is_empty(),
        "profile must observe checked claims"
    );
    assert!(
        profile
            .iter()
            .any(|event| matches!(event, VerificationEvent::TacticFinished { .. }))
    );

    let sites = cpp_prepared_project_smart_tactic_source_sites(&project, &imported).unwrap();
    assert_eq!(
        sites.len(),
        14,
        "audit must cover every upstream smart tactic"
    );
    for event in &profile {
        if let VerificationEvent::TacticFinished { tactic, .. } = event {
            cpp_prepared_project_tactic_source_position(
                &project,
                &imported,
                &tactic.claim,
                tactic.source_index,
            )
            .expect("each profiled tactic must resolve to its upstream sidecar position");
        }
    }
    for claim in [
        "MoneyRange.contract",
        "below_range_is_false.ensures_0",
        "zero_is_in_range.ensures_0",
        "max_money_is_in_range.ensures_0",
        "above_range_is_false.ensures_0",
    ] {
        assert!(
            sites.iter().any(|site| site.claim_label == claim),
            "{claim} has no source-selectable smart tactic"
        );
        let profiled_claim = if claim.ends_with(".ensures_0") {
            claim.replace(".ensures_0", ".contract")
        } else {
            claim.to_owned()
        };
        assert!(
            profile.iter().any(|event| matches!(event,
                VerificationEvent::TacticFinished { tactic, .. } if tactic.claim == profiled_claim
            )),
            "profile missed {claim}"
        );
    }
    let (session, _) = C0VerificationSession::new_cpp_prepared_project(&project, &imported)
        .expect("start a retained audit session on the same import");
    let expanded_contract = expand_cpp_prepared_project_claim_source_by_label(
        &project,
        &imported,
        "MoneyRange.contract",
    )
    .expect("the documented claim expansion must use the locked upstream import");
    verify_cpp_prepared_project(&project.with_entry_source(expanded_contract), &imported)
        .expect("the documented expanded range claim must reverify");
    for site in sites {
        let claim = site.claim_label.as_str();
        let position = cpp_prepared_project_tactic_source_position(
            &project,
            &imported,
            claim,
            site.source_index,
        )
        .expect("each upstream claim has a selectable tactic");
        let profiled_claim = if claim.ends_with(".ensures_0") {
            claim.replace(".ensures_0", ".contract")
        } else {
            claim.to_owned()
        };
        let profiled_position = cpp_prepared_project_tactic_source_position(
            &project,
            &imported,
            &profiled_claim,
            site.source_index,
        )
        .expect("the profiler must resolve the same upstream tactic location");
        assert_eq!(profiled_position, position);
        let expanded = expand_cpp_prepared_project_tactic_source_at(
            &project,
            &imported,
            position.line,
            position.column,
        )
        .expect("expand a tactic against the same locked import");
        assert_ne!(expanded, SIDECAR);
        let rewritten = project.with_entry_source(expanded.clone());
        let remaining = cpp_prepared_project_smart_tactic_source_sites(&rewritten, &imported)
            .expect("expanded proof remains source-inventoriable")
            .into_iter()
            .filter(|candidate| candidate.claim_label == claim)
            .count();
        let original = cpp_prepared_project_smart_tactic_source_sites(&project, &imported)
            .unwrap()
            .into_iter()
            .filter(|candidate| candidate.claim_label == claim)
            .count();
        assert!(
            remaining < original,
            "expansion must remove the audited smart site"
        );
        verify_cpp_prepared_project(&rewritten, &imported)
            .expect("expanded certificate must reverify against the upstream import");
        let next = cpp_prepared_project_tactic_source_position(&rewritten, &imported, claim, 0)
            .expect("the audited claim remains source-selectable");
        session
            .verify_at_project(&expanded, next.line, next.column)
            .expect("audit session must accept the expanded certificate");
    }

    let source_contract = SIDECAR
        .split_once("contract bool BelowRange")
        .expect("the modular boundary contracts follow MoneyRange")
        .0;
    let false_source = source_contract.replace(
        "if old(nValue[0]) <= 2100000000000000i64",
        "if old(nValue[0]) < 2100000000000000i64",
    );
    assert_ne!(false_source, source_contract);
    fs::write(&sidecar, &false_source).unwrap();
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let false_error = verify_cpp_prepared_project(&false_project, &imported)
        .expect_err("an exclusive upper bound must not prove the upstream function");
    assert!(
        false_error.message().contains("MoneyRange.contract")
            && false_error.message().contains("unclosed goal"),
        "{}",
        false_error.message()
    );
    fs::write(&sidecar, SIDECAR).unwrap();

    let amount_bytes = fs::read(&amount).unwrap();
    let mut changed_amount = amount_bytes.clone();
    changed_amount.push(b'\n');
    fs::write(&amount, changed_amount).unwrap();
    let changed_header = load_import(&config_path).unwrap_err();
    assert!(
        changed_header.contains("C++ logical source differs"),
        "{changed_header}"
    );
    fs::write(&amount, amount_bytes).unwrap();
    load_import(&config_path).expect("restoring upstream bytes restores the locked import");

    let transitive = root.join("sysroot/usr/include/c++/12/limits");
    let transitive_bytes = fs::read(&transitive).unwrap();
    let mut changed_transitive = transitive_bytes.clone();
    changed_transitive.push(b'\n');
    fs::write(&transitive, changed_transitive).unwrap();
    let changed_dependency = load_import(&config_path).unwrap_err();
    assert!(
        changed_dependency.contains("C++ preprocessor input inventory differs"),
        "{changed_dependency}"
    );
    fs::write(&transitive, transitive_bytes).unwrap();
    load_import(&config_path).expect("restoring a transitive header restores the locked import");

    let database_path = root.join("compile_commands.json");
    let database_bytes = fs::read_to_string(&database_path).unwrap();
    let changed_database = database_bytes.replace("-std=c++20", "-std=c++17");
    assert_ne!(changed_database, database_bytes);
    fs::write(&database_path, changed_database).unwrap();
    let changed_command = load_import(&config_path).unwrap_err();
    assert!(
        changed_command.contains("C++ compilation database differs"),
        "{changed_command}"
    );
    fs::write(&database_path, database_bytes).unwrap();
    load_import(&config_path).expect("restoring the CMake command restores the locked import");

    let config_bytes = fs::read(&config_path).unwrap();
    let mut wrong_profile: serde_json::Value = serde_json::from_slice(&config_bytes).unwrap();
    wrong_profile["rtti"] = serde_json::json!(false);
    fs::write(
        &config_path,
        serde_json::to_vec_pretty(&wrong_profile).unwrap(),
    )
    .unwrap();
    let changed_profile = load_import(&config_path).unwrap_err();
    assert!(
        changed_profile.contains("C++ import lock does not match the import config"),
        "{changed_profile}"
    );
    fs::write(&config_path, &config_bytes).unwrap();

    let mut wrong_location: serde_json::Value = serde_json::from_slice(&config_bytes).unwrap();
    wrong_location["logical_source"] = serde_json::json!("bitcoin-src/src/policy/feerate.h");
    fs::write(
        &config_path,
        serde_json::to_vec_pretty(&wrong_location).unwrap(),
    )
    .unwrap();
    let wrong_location_error = refresh_import(&config_path)
        .expect_err("MoneyRange must not resolve to a different upstream header");
    assert!(
        wrong_location_error.contains("selected function `MoneyRange` was not found"),
        "{wrong_location_error}"
    );
    let stale_selector = load_import(&config_path)
        .expect_err("a rejected selector must not load the old semantic artifact");
    assert!(
        stale_selector.contains("C++ import lock does not match the import config"),
        "{stale_selector}"
    );
    fs::write(&config_path, config_bytes).unwrap();
    load_import(&config_path).expect("the original selector and lock remain valid");
    fs::remove_dir_all(root).unwrap();
}
