//! Hermetic re-export of the pinned Bitcoin Core v31.1 MoneyRange fixture.

use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use click::cli::read_click_project;
use click::instrumentation::{self, VerificationEvent};
use click::languages::cpp::PreparedCppImport;
#[path = "support/cpp_description.rs"]
mod cpp_description;
use click::surface::{
    C0VerificationSession, display_source_names, expand_project_claim_source_by_label,
    expand_project_tactic_source_at, project_smart_tactic_source_sites,
    project_tactic_source_position, verify_program_prepared_project,
};
use cpp_description::{load_import, lock_section_mut, lock_source_mut, refresh_import};
#[path = "support/pinned_clang.rs"]
mod pinned_clang;
use pinned_clang::{output, pinned_clang, sha256};

const ARCHIVE: &[u8] =
    include_bytes!("../integrations/bitcoin-core-money-range/input-closure.tar.gz");
const PROVENANCE: &str =
    include_str!("../integrations/bitcoin-core-money-range/fixture-provenance.json");
const COMMAND: &str =
    include_str!("../integrations/bitcoin-core-money-range/feerate-command.json.in");
const SIDECAR: &str = include_str!("../integrations/bitcoin-core-money-range/MoneyRange.click");
const PROJECT: &str = include_str!("../integrations/bitcoin-core-money-range/click.project.json");

/// The project's `bitcoin` unit is the selected CMake command itself: every
/// argument in order, relocated to the unit root, except those Click
/// supplies (the driver, target, standard, resource directory, `-c` and `-o`).
#[test]
fn bitcoin_unit_arguments_are_the_cmake_command() {
    let command: serde_json::Value = serde_json::from_str(COMMAND).unwrap();
    let mut words = command[0]["command"].as_str().unwrap().split_whitespace();
    assert_eq!(words.next(), Some("@CLANGXX@"));
    let mut expected = Vec::new();
    while let Some(word) = words.next() {
        if word == "-o" || word == "-c" {
            words.next();
        } else if !(word.starts_with("--target=")
            || word == "-std=c++20"
            || word.starts_with("-resource-dir="))
        {
            expected.push(word.replace("@ROOT@/", ""));
        }
    }
    let project: serde_json::Value = serde_json::from_str(PROJECT).unwrap();
    let unit = &project["units"]["bitcoin"];
    assert_eq!(unit["language"], "c++");
    assert_eq!(
        (&unit["exceptions"], &unit["rtti"]),
        (&true.into(), &true.into())
    );
    let actual = unit["args"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| argument.as_str().unwrap().to_string())
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
    assert!(actual.iter().any(|argument| argument == "-O2"));
}

fn check_upstream_fee_frac(selected: &str, name: &str, source: &str) {
    check_upstream_cpp(
        selected,
        name,
        source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
    );
}

fn check_upstream_cpp(
    selected: &str,
    name: &str,
    source: &str,
    logical_source: &str,
    integer_header: &str,
) {
    check_upstream_cpp_rounding_phase(selected, name, source, logical_source, integer_header, None);
}

/// A sidecar fixture's leading `import` lines and its text after its
/// `verifying` clause. A composed sidecar keeps one `verifying` clause, and
/// every fixture's library imports go at its head, before that clause.
fn fixture_imports_and_body(fixture: &str) -> (&str, &str) {
    let clause = fixture.find("verifying \"").unwrap();
    let imports = &fixture[..clause];
    assert!(
        imports
            .lines()
            .all(|line| line.is_empty() || line.starts_with("import click::")),
        "a fixture's verifying clause follows only its library imports: {imports}"
    );
    let body = fixture[clause..].split_once(';').unwrap().1;
    (imports.trim(), body)
}

#[derive(Clone, Copy, PartialEq)]
enum RoundingPhase {
    Tools,
    FullExpansion,
    Rejections,
    TransportRejections,
    NumeratorRejections,
    RoundingRejections,
    FitRejections,
    AuthorityRejections,
    AdjustedNumeratorRejections,
}

fn check_upstream_cpp_rounding_phase(
    selected: &str,
    name: &str,
    source: &str,
    logical_source: &str,
    integer_header: &str,
    phase: Option<RoundingPhase>,
) {
    assert_eq!(
        sha256(ARCHIVE),
        "fceeaef86784f820339f6dc3fc24992eb9c6bcf52edccbf6b7869d79296a3c7d"
    );
    let root = std::env::temp_dir().join(format!(
        "click-bitcoin-fee-frac-{name}-{}",
        std::process::id()
    ));
    fs::create_dir(&root).unwrap();
    let archive_path = root.join("input-closure.tar.gz");
    fs::write(&archive_path, ARCHIVE).unwrap();
    let result = Command::new("tar")
        .args([
            "-xzf",
            archive_path.to_str().unwrap(),
            "-C",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(result.status.success());
    assert_eq!(
        sha256(&fs::read(root.join("bitcoin-src/src/util/feefrac.h")).unwrap()),
        "213a97d13eb82b34831466febcff24f4c20879603f36fc6edd894b89000f7ab9"
    );
    assert_eq!(
        sha256(&fs::read(root.join("bitcoin-src/src/serialize.h")).unwrap()),
        "87a273aa8cb9aeea82cd8038bb85284a5782c8abc35f8c826eb60f1a01e06775"
    );
    fs::create_dir_all(root.join("bitcoin-build/src")).unwrap();
    let clang = pinned_clang();
    let database = COMMAND
        .replace("@ROOT@", root.to_str().unwrap())
        .replace("@CLANGXX@", clang.to_str().unwrap())
        .replace("@RESOURCE_DIR@", &output(&clang, &["-print-resource-dir"]));
    fs::write(root.join("compile_commands.json"), database).unwrap();
    let mut config = serde_json::json!({
        "schema": 6, "language": "c++", "standard": "c++20", "target": "x86_64-unknown-linux-gnu",
        "exceptions": true, "rtti": true,
        "exporter": std::env::var("CLICK_CPP_EXPORTER").unwrap(),
        "compilation_database": "compile_commands.json", "working_directory": ".",
        "source": "bitcoin-src/src/policy/feerate.cpp", "logical_source": logical_source,
        "dependencies": [integer_header, "sysroot/usr/include/x86_64-linux-gnu/bits/types.h"],
        "function": selected, "artifact": format!("{name}.click-cpp.json")
    });
    let evaluation_caller = name.starts_with("FeeFracEvaluate");
    let fee_rate_import = name == "CFeeRateGetFeeImported";
    let fee_rate_per_k = selected == "CFeeRate::GetFeePerK";
    let fee_rate_caller = name.starts_with("CFeeRateGetFee");
    let result_fit_div = name.starts_with("FeeFracDivResultFit");
    let bounded_div = name == "FeeFracDivBounded" || result_fit_div;
    if evaluation_caller
        || fee_rate_caller
        || bounded_div
        || matches!(
            name,
            "FeeFracDivConstevalRefused" | "FeeFracDivImported" | "FeeFracDivBounded"
        )
    {
        const CHECK_HASH: &str = "82705f6150e57b4de9123d22b3820f60f6f75f58c1c8b9fbff78863afca816a7";
        let header = "bitcoin-src/src/util/check.h";
        assert_eq!(sha256(&fs::read(root.join(header)).unwrap()), CHECK_HASH);
        config["dependencies"] = serde_json::json!([
            header,
            integer_header,
            "sysroot/usr/include/x86_64-linux-gnu/bits/types.h"
        ]);
        config["library_assertions"] = serde_json::json!([{
            "kind": "checked_boolean_statement_with_consteval_metadata",
            "function": "inline_assertion_check", "header": header, "sha256": CHECK_HASH
        }]);
    }
    if evaluation_caller || fee_rate_caller || bounded_div || name == "FeeFracDivImported" {
        const STRING_VIEW_HASH: &str =
            "9b1a575ffad1e8575cd6fc1c9a24b0cdde3793275be431726cc9c1b178a8733c";
        let header = "sysroot/usr/include/c++/12/string_view";
        assert_eq!(
            sha256(&fs::read(root.join(header)).unwrap()),
            STRING_VIEW_HASH
        );
        config["dependencies"]
            .as_array_mut()
            .unwrap()
            .push(header.into());
        config["dependencies"]
            .as_array_mut()
            .unwrap()
            .sort_by(|a, b| a.as_str().cmp(&b.as_str()));
        config["library_assertions"][0]["kind"] =
            "checked_boolean_statement_with_literal_metadata".into();
        config["library_assertions"][0]["literal_constructor"] = serde_json::json!({
            "function": "std::basic_string_view::basic_string_view", "header": header, "sha256": STRING_VIEW_HASH
        });
    }
    if fee_rate_caller {
        for header in [
            "bitcoin-src/src/consensus/amount.h",
            "bitcoin-src/src/policy/feerate.h",
            "bitcoin-src/src/util/feefrac.h",
        ] {
            if header == logical_source {
                continue;
            }
            config["dependencies"]
                .as_array_mut()
                .unwrap()
                .push(header.into());
        }
        config["dependencies"]
            .as_array_mut()
            .unwrap()
            .sort_by(|a, b| a.as_str().cmp(&b.as_str()));
        if !fee_rate_import {
            let exporter = root.join("click-cpp-exporter");
            fs::copy(config["exporter"].as_str().unwrap(), &exporter).unwrap();
            config["exporter"] = exporter.to_str().unwrap().into();
        }
    }
    let config_path = root.join(format!("{name}.import-description.json"));
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    let sidecar = root.join(format!("{name}.click"));
    fs::write(&sidecar, source).unwrap();
    let refreshed = refresh_import(&config_path);
    if fee_rate_import {
        refreshed.expect("GetFee must import its unchanged converted-call graph");
        let import = load_import(&config_path).unwrap();
        assert_eq!(import.export().functions[0].name, "CFeeRate_GetFee");
        assert!(
            import
                .export()
                .reachable_functions
                .iter()
                .any(|callee| callee.span.file == "bitcoin-src/src/util/feefrac.h")
        );
        click::languages::cpp::lower_import(&import).unwrap();
        let artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(cpp_description::artifact(&config_path)).unwrap())
                .unwrap();
        let initializer = &artifact["functions"][0]["body"]
            .as_array()
            .unwrap()
            .iter()
            .find(|statement| statement["kind"] == "declare")
            .unwrap()["initializer"];
        assert_eq!(initializer["kind"], "call");
        assert_eq!(initializer["conversions"][0]["cast_kind"], "no_op");
        assert_eq!(initializer["conversions"][0]["value_type"]["bits"], 64);
        assert!(cpp_description::artifact(&config_path).exists());
        assert!(root.join(click::project::LOCK_NAME).exists());
        fs::remove_dir_all(root).unwrap();
        return;
    }
    if selected == "FeeFrac::Div" && !bounded_div && name != "FeeFracDivImported" {
        let error = refreshed.expect_err("the library Assume boundary must remain explicit");
        assert!(error.contains("export C++ source"), "{error}");
        if name == "FeeFracDivConstevalRefused" {
            assert!(
                error.contains("metadata argument 2 requires a forced consteval"),
                "the real template, Boolean temporary, and source_location must reach the string_view boundary: {error}"
            );
        }
        assert!(!cpp_description::artifact(&config_path).exists());
        assert!(!root.join(click::project::LOCK_NAME).exists());
        fs::remove_dir_all(root).unwrap();
        return;
    }
    refreshed.unwrap_or_else(|error| panic!("{selected}: {error}"));
    if fee_rate_caller {
        fs::remove_file(config["exporter"].as_str().unwrap()).unwrap();
    }
    let import = load_import(&config_path).unwrap();
    assert_eq!(import.export().preprocessor_files.len(), 320);
    if evaluation_caller {
        let instance = if selected.ends_with("Down") {
            "FeeFrac_EvaluateFee__bool_true"
        } else {
            "FeeFrac_EvaluateFee__bool_false"
        };
        assert_eq!(
            import
                .export()
                .reachable_functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            vec![instance, "FeeFrac_Mul", "FeeFrac_Div"]
        );
    } else if !fee_rate_caller {
        assert!(import.export().reachable_functions.is_empty());
    }
    if selected == "FeeFrac::Div" && !bounded_div {
        use click::languages::cpp::{CppLibraryMetadata, CppLiteralMetadataBinding, CppStatement};
        let CppStatement::LibraryAssert { metadata, .. } = &import.export().functions[0].body[0]
        else {
            panic!("retained upstream annotation")
        };
        assert!(matches!(metadata[0], CppLibraryMetadata::Consteval(_)));
        let CppLibraryMetadata::Literal(literal) = &metadata[1] else {
            panic!("retained runtime literal")
        };
        assert_eq!(literal.literal, "d > 0");
        assert_eq!(literal.record, "std::basic_string_view");
        assert!(literal.record_type.contains("std::basic_string_view<char>"));
        assert_eq!(literal.binding, CppLiteralMetadataBinding::Value);
        click::languages::cpp::lower_import(&import).unwrap();
        for (premises, diagnostic) in [
            ("", "assumed library contract"),
            // A positive divisor already rules out division by zero.
            ("requires d > 0;", "signed overflow"),
            // The quotient fits int64, but rounding it upward does not:
            // (2^64 - 1) / 2 rounds up from int64::MAX to 2^63.
            (
                "requires d == 2; requires n == 18446744073709551615i128; requires round_down == 0;",
                "signed overflow",
            ),
        ] {
            let proof = format!(
                "verifying \"bitcoin-src/src/util/feefrac.h\"; static int64 FeeFrac::Div(int128 n, int32 d, bool round_down) {{ {premises} ensures 0 == 0; }} by {{ execute(); simp(); }}"
            );
            let parsed = read_click_project(&sidecar, &proof).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().contains(diagnostic), "{}", error.message());
            assert!(error.message().len() < 8000);
            if premises.is_empty() {
                assert!(error.message().contains("literal constructor"));
            }
        }
        // Zero divided by a positive divisor is zero with either rounding mode.
        // The type and divisor facts suffice; it needs no extra wide guards.
        let zero_proof = r#"verifying "bitcoin-src/src/util/feefrac.h";
static int64 FeeFrac::Div(int128 n, int32 d, bool round_down) {
    requires d > 0;
    requires to_integer(n) == 0;
    ensures result == 0i64;
} by { execute(); simp(); }
"#;
        let parsed = read_click_project(&sidecar, zero_proof).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect("zero numerator is safe for every positive divisor and rounding mode");
        // Derive the wide observer guards from the real narrow divisor
        // precondition. Execution must advance to the still-unproved narrow
        // correction; no wide guard is assumed in the contract.
        let guard_proof = r#"import click::integer;
verifying "bitcoin-src/src/util/feefrac.h";
static int64 FeeFrac::Div(int128 n, int32 d, bool round_down) {
    requires d > 0;
    ensures 0 == 0;
} by {
    have 1 <= d by { arithmetic() using { d > 0; } }
    apply(int32_less_equal_to_integer(1, d));
    have to_integer(d) != 0 by { arithmetic_certificate rules {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != 0;
        conclusion 0;
    } }
    have to_integer(d) != -1 by { arithmetic_certificate rules {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != -1;
        conclusion 0;
    } }
    execute(); simp();
}"#;
        let parsed = read_click_project(&sidecar, guard_proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("signed overflow"),
            "{}",
            error.message()
        );
        assert!(
            !error.message().contains("division by zero"),
            "{}",
            error.message()
        );
        assert!(error.message().len() < 8000);
        fs::remove_dir_all(root).unwrap();
        return;
    }
    let project = read_click_project(&sidecar, source).unwrap();
    if fee_rate_caller {
        // Expansion reuses the certificate from the original session check.
        // Other phases keep their independent full original verification.
        let retained = if matches!(
            phase,
            Some(RoundingPhase::FullExpansion | RoundingPhase::Tools)
        ) {
            Some(
                C0VerificationSession::new_program_prepared_project(&project, &import)
                    .unwrap_or_else(|error| panic!("{selected}: {}", error.message())),
            )
        } else {
            verify_program_prepared_project(&project, &import)
                .unwrap_or_else(|error| panic!("{selected}: {}", error.message()));
            None
        };
        let root_name = if fee_rate_per_k {
            "CFeeRate::GetFeePerK"
        } else {
            "CFeeRate::GetFee"
        };
        if matches!(
            phase,
            Some(RoundingPhase::FullExpansion | RoundingPhase::Tools)
        ) {
            let (session, verified) = retained.unwrap();
            let expanded = click::surface::expand_verified_function_claim_source_by_label(
                source,
                &verified,
                &format!(
                    "{}.ensures_0",
                    click::languages::cpp::names::path_name(&import.export().functions[0].path)
                ),
            )
            .unwrap()
            .expect("the fee-rate claim retains its certificate");
            let rewritten = project.with_entry_source(expanded.clone());
            if phase == Some(RoundingPhase::FullExpansion) {
                drop(session);
                verify_program_prepared_project(&rewritten, &import).unwrap();
            } else {
                let position = project_tactic_source_position(
                    &rewritten,
                    &ProgramInputs::program(&import),
                    &format!("{root_name}.contract"),
                    0,
                )
                .unwrap();
                session
                    .verify_at_project(&expanded, position.line, position.column)
                    .unwrap();
            }
        } else if phase == Some(RoundingPhase::Rejections) {
            let (from, to) = match name {
                "CFeeRateGetFeeMissingFeeAuthority" => ("views this->m_feerate.base.fee;", ""),
                "CFeeRateGetFeeMissingSizeAuthority" => ("views this->m_feerate.base.size;", ""),
                "CFeeRateGetFeeMissingAmountGuard" => ("requires 0 <= virtual_bytes;", ""),
                "CFeeRateGetFeeMissingSizeGuard" => {
                    ("requires this->m_feerate.base.size >= 0;", "")
                }
                "CFeeRateGetFeeMissingLowerFit" => (
                    "requires this->m_feerate.base.size != 0 implies -9223372036854775809 * to_integer(this->m_feerate.base.size) < to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes);",
                    "",
                ),
                "CFeeRateGetFeeMissingUpperFit" => (
                    "requires this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes) <= 9223372036854775807 * to_integer(this->m_feerate.base.size);",
                    "",
                ),
                "CFeeRateGetFeeInclusiveLowerFit" => (
                    "-9223372036854775809 * to_integer(this->m_feerate.base.size) <",
                    "-9223372036854775809 * to_integer(this->m_feerate.base.size) <=",
                ),
                "CFeeRateGetFeeFalseEmpty" => (
                    "this->m_feerate.base.size == 0 implies result == 0i64",
                    "this->m_feerate.base.size == 0 implies result == 1i64",
                ),
                "CFeeRateGetFeeFalseCorrection" => (
                    "or (result == -1i64 and virtual_bytes",
                    "or (result == 0i64 and virtual_bytes",
                ),
                "CFeeRateGetFeeNativeFeeBounds" => (
                    "requires this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) <= 9223372036854775807;",
                    "",
                ),
                "CFeeRateGetFeePerKMissingSizeGuard" => {
                    ("requires this->m_feerate.base.size > 0;", "")
                }
                "CFeeRateGetFeePerKMissingFeeAuthority" => ("views this->m_feerate.base.fee;", ""),
                "CFeeRateGetFeePerKMissingLowerFit" => (
                    "requires -9223372036854775808 * to_integer(this->m_feerate.base.size) <= to_integer(this->m_feerate.base.fee) * 1000;",
                    "",
                ),
                "CFeeRateGetFeePerKInclusiveUpperFit" => (
                    "* 1000 < 9223372036854775808",
                    "* 1000 <= 9223372036854775808",
                ),
                "CFeeRateGetFeePerKFalseRounding" => {
                    ("(to_integer(result) + 1)", "(to_integer(result) + -1)")
                }
                _ => panic!("unknown fee-rate rejection {name}"),
            };
            // The root's head is its C++ declaration, `int64 CFeeRate::GetFee(`.
            let root_signature = format!("int64 {selected}(");
            let (helpers, root_source) = source.split_once(&root_signature).unwrap();
            assert!(root_source.contains(from), "missing mutation {name}");
            let hostile = format!(
                "{helpers}{root_signature}{}",
                root_source.replacen(from, to, 1)
            );
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            if name == "CFeeRateGetFeeNativeFeeBounds" {
                verify_program_prepared_project(&parsed, &import)
                    .unwrap_or_else(|error| panic!("native int64 fee bounds: {}", error.message()));
            } else {
                let error = verify_program_prepared_project(&parsed, &import)
                    .err()
                    .unwrap_or_else(|| panic!("{name} accepted its mutated claim"));
                assert!(error.message().len() < 8000, "{}", error.message());
            }
        } else if phase == Some(RoundingPhase::TransportRejections) {
            fs::write(
                root.join("bitcoin-src/src/util/feefrac.h"),
                "// stale header\n",
            )
            .unwrap();
            let error = load_import(&config_path).unwrap_err();
            assert!(error.len() < 8000, "{error}");
        }
        fs::remove_dir_all(root).unwrap();
        return;
    }
    if matches!(phase, None | Some(RoundingPhase::Tools))
        && !matches!(selected, "GetSizeOfCompactSize" | "FeeFrac::Mul")
    {
        verify_program_prepared_project(&project, &import)
            .unwrap_or_else(|error| panic!("{selected}: {}", error.message()));
    }
    if matches!(phase, None | Some(RoundingPhase::Tools))
        && matches!(
            selected,
            "GetSizeOfCompactSize" | "FeeFrac::Mul" | "FeeFrac::Div"
        )
    {
        let sites =
            project_smart_tactic_source_sites(&project, &ProgramInputs::program(&import)).unwrap();
        let first = sites.first().unwrap();
        let position = project_tactic_source_position(
            &project,
            &ProgramInputs::program(&import),
            &first.claim_label,
            first.source_index,
        )
        .unwrap();
        let expanded = expand_project_tactic_source_at(
            &project,
            &ProgramInputs::program(&import),
            position.line,
            position.column,
        )
        .unwrap();
        let rewritten = project.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import)
            .expect("expanded upstream proof reverifies");
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let sites = project_smart_tactic_source_sites(&rewritten, &ProgramInputs::program(&import))
            .unwrap();
        let first = sites.first().unwrap();
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            &first.claim_label,
            first.source_index,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .expect("upstream retained audit agrees");
        let false_source = source
            .replace("ensures 0 == 0;", "ensures 0 == 1;")
            .replace(
                "ensures -9223372036854775808 <= to_integer(result);",
                "ensures 9223372036854775807 <= to_integer(result);",
            )
            .replace("ensures result ==", "ensures result !=")
            .replace(
                "ensures to_integer(result) ==",
                "ensures to_integer(result) !=",
            );
        let false_project = read_click_project(&sidecar, &false_source).unwrap();
        let Err(error) = verify_program_prepared_project(&false_project, &import) else {
            panic!("false upstream claim must be refused");
        };
        assert!(
            error.message().contains("unclosed goal"),
            "{}",
            error.message()
        );
    }

    if evaluation_caller && phase == Some(RoundingPhase::Tools) {
        let label = format!("{selected}.ensures_0");
        let expanded = expand_project_claim_source_by_label(
            &project,
            &ProgramInputs::program(&import),
            &label,
        )
        .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
    }
    if evaluation_caller
        && (name.ends_with("Negative")
            || name.ends_with("PositiveWide")
            || name.ends_with("SymbolicFast")
            || name.ends_with("Unified"))
        && phase == Some(RoundingPhase::FullExpansion)
    {
        let instance = if selected.ends_with("Down") {
            "true"
        } else {
            "false"
        };
        let expanded = expand_project_claim_source_by_label(
            &project,
            &ProgramInputs::program(&import),
            &format!("FeeFrac::EvaluateFee<{instance}>.ensures_0"),
        )
        .unwrap();
        let rewritten = project.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import).unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            &format!("FeeFrac::EvaluateFee<{instance}>.contract"),
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
    if evaluation_caller
        && matches!(
            phase,
            Some(
                RoundingPhase::Rejections
                    | RoundingPhase::TransportRejections
                    | RoundingPhase::NumeratorRejections
                    | RoundingPhase::RoundingRejections
                    | RoundingPhase::FitRejections
                    | RoundingPhase::AuthorityRejections
                    | RoundingPhase::AdjustedNumeratorRejections
            )
        )
    {
        // Native int64 fields already satisfy their representable range.
        // Removing these redundant requirements must keep verifying; the
        // mutations below still remove actual branch transport or forge values.
        if phase == Some(RoundingPhase::TransportRejections)
            && name.contains("ResultFit")
            && (name.ends_with("Unified")
                || name.ends_with("Negative")
                || name.ends_with("PositiveWide"))
        {
            let native_bounds = source
                .replace(
                    "requires -9223372036854775808 <= to_integer(this->fee);",
                    "",
                )
                .replace("requires to_integer(this->fee) <= 9223372036854775807;", "");
            assert_ne!(native_bounds, source);
            let parsed = read_click_project(&sidecar, &native_bounds).unwrap();
            verify_program_prepared_project(&parsed, &import).unwrap_or_else(|error| {
                panic!("{name} must use native fee bounds: {}", error.message())
            });
        }
        let hostile = if name.contains("ResultFit") && name.ends_with("SymbolicFast") {
            let down = selected.ends_with("Down");
            let fit = if down {
                "requires to_integer(this->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(this->size);"
            } else {
                "requires to_integer(this->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(this->size);"
            };
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    // `at_size <= 2147483647` holds of any `int32`; removing it weakens nothing.
                    source.replace(fit, ""),
                    source.replace(
                        fit,
                        &fit.replace(
                            if down {
                                " < 9223372036854775808"
                            } else {
                                " <= 9223372036854775807"
                            },
                            " <= 18446744073709551615",
                        ),
                    ),
                ]
            } else if phase == Some(RoundingPhase::NumeratorRejections) {
                let mut cases = vec![
                    source.replace("apply(uint64_multiply_to_integer((uint64)this->fee, (uint64)at_size));", ""),
                    source.replace(if down { "apply(uint64_divide_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)(uint32)this->size));" } else { "apply(uint64_divide_to_integer(((((uint64)this->fee * (uint64)at_size) + (uint64)this->size) - 1u64), (uint64)(uint32)this->size));" }, ""),
                ];
                if !down {
                    cases.extend([
                        source.replace("apply(uint64_add_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)this->size));", ""),
                        source.replace("apply(uint64_subtract_to_integer((((uint64)this->fee * (uint64)at_size) + (uint64)this->size), 1u64));", ""),
                        source.replace("== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 1", "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 2"),
                    ]);
                }
                cases
            } else if phase == Some(RoundingPhase::TransportRejections) {
                // The fee bound is stated twice, as an `int64` comparison and
                // as an integer one; either follows from the other, so the
                // hostile edit removes both.
                vec![
                    source
                        .replace("requires this->fee < 8589934592i64;", "")
                        .replace("requires to_integer(this->fee) <= 8589934591;", ""),
                    source.replace("requires 0 <= to_integer(this->fee);", ""),
                ]
            } else {
                assert!(phase == Some(RoundingPhase::RoundingRejections));
                vec![
                    source.replace(
                        "ensures to_integer(result) == truncating_quotient(",
                        "ensures to_integer(result) != truncating_quotient(",
                    ),
                    source.replace(
                        if down {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                ]
            }
        } else if name.contains("ResultFit") && name.ends_with("Unified") {
            let down = selected.ends_with("Down");
            let lower = if down {
                "requires -9223372036854775808 * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size);"
            } else {
                "requires -9223372036854775809 * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size);"
            };
            let upper = if down {
                "requires to_integer(this->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(this->size);"
            } else {
                "requires to_integer(this->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(this->size);"
            };
            match phase.unwrap() {
                RoundingPhase::AuthorityRejections => vec![
                    source.replace("views this->fee;", ""),
                    source.replace("views this->size;", ""),
                ],
                RoundingPhase::Rejections => vec![
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    // `at_size <= 2147483647` holds of any `int32`; removing it weakens nothing.
                ],
                RoundingPhase::FitRejections => {
                    let strict = if down { upper } else { lower };
                    vec![source.replace(lower, ""), source.replace(upper, ""), source.replace(strict, &strict.replace(" < ", " <= "))]
                }
                RoundingPhase::TransportRejections => vec![
                    source.replace("apply(int64_greater_equal_to_integer(this->fee, 0i64));", ""),
                    source.replace("apply(int64_less_than_to_integer(this->fee, 8589934592i64));", ""),
                ],
                RoundingPhase::RoundingRejections => vec![
                    source.replace(if down { "(to_integer(result) + 1) * to_integer(this->size)" } else { "(to_integer(result) + -1) * to_integer(this->size)" }, "to_integer(result) * to_integer(this->size)"),
                    source.replace(if down { "to_integer(result) * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) <= to_integer(result) * to_integer(this->size)" }, if down { "to_integer(result) * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) < to_integer(result) * to_integer(this->size)" }),
                ],
                RoundingPhase::NumeratorRejections => vec![
                    source.replace("apply(uint64_multiply_to_integer((uint64)this->fee, (uint64)at_size));", ""),
                    source.replace("to_integer(product) == to_integer(this->fee) * to_integer(at_size)", "to_integer(product) == to_integer(this->fee) * to_integer(at_size) + 1"),
                    source.replace("to_integer(negative_product) == to_integer(this->fee) * to_integer(at_size)", "to_integer(negative_product) == to_integer(this->fee) * to_integer(at_size) + 1"),
                    source.replace(if down { "apply(uint64_divide_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)(uint32)this->size));" } else { "apply(uint64_divide_to_integer(((((uint64)this->fee * (uint64)at_size) + (uint64)this->size) - 1u64), (uint64)(uint32)this->size));" }, ""),
                ],
                RoundingPhase::AdjustedNumeratorRejections => {
                    assert!(!down);
                    vec![
                        source.replace("apply(uint64_add_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)this->size));", ""),
                        source.replace("apply(uint64_subtract_to_integer((((uint64)this->fee * (uint64)at_size) + (uint64)this->size), 1u64));", ""),
                        source.replace("== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 1", "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 2"),
                    ]
                }
                _ => unreachable!(),
            }
        } else if name.contains("ResultFit") {
            let down = selected.ends_with("Down");
            let lower = if down {
                "requires -9223372036854775808 * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size);"
            } else {
                "requires -9223372036854775809 * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size);"
            };
            let upper = if down {
                "requires to_integer(this->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(this->size);"
            } else {
                "requires to_integer(this->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(this->size);"
            };
            if phase == Some(RoundingPhase::Rejections) {
                let strict = if down { upper } else { lower };
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    // `at_size <= 2147483647` holds of any `int32`; removing it weakens nothing.
                    source.replace(lower, ""),
                    source.replace(upper, ""),
                    source.replace(strict, &strict.replace(" < ", " <= ")),
                ]
            } else {
                vec![
                    source.replace(if name.ends_with("Negative") { "requires not (this->fee >= 0i64);" } else { "requires this->fee >= 0i64 and not (this->fee < 8589934592i64);" }, ""),
                    source.replace("to_integer(product) == to_integer(this->fee) * to_integer(at_size)", "to_integer(product) == to_integer(this->fee) * to_integer(at_size) + 1"),
                    source.replace(if down { "(to_integer(result) + 1) * to_integer(this->size)" } else { "(to_integer(result) + -1) * to_integer(this->size)" }, "to_integer(result) * to_integer(this->size)"),
                    source.replace(if down { "to_integer(result) * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) <= to_integer(result) * to_integer(this->size)" }, if down { "to_integer(result) * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) < to_integer(result) * to_integer(this->size)" }),
                ]
            }
        } else if name.ends_with("Unified") {
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= this->size;", ""),
                ]
            } else {
                vec![
                    source.replace("requires to_integer(this->fee) <= 9223372036854775807;", ""),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                    source.replace(
                        "apply(int64_less_than_to_integer(this->fee, 8589934592i64));",
                        "",
                    ),
                ]
            }
        } else if name.ends_with("SymbolicFast") {
            if phase == Some(RoundingPhase::NumeratorRejections) {
                assert!(selected.ends_with("Up"));
                vec![
                    source.replace(
                        "apply(uint64_add_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)this->size));",
                        "",
                    ),
                    source.replace(
                        "apply(uint64_subtract_to_integer((((uint64)this->fee * (uint64)at_size) + (uint64)this->size), 1u64));",
                        "",
                    ),
                    source.replace(
                        "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 1",
                        "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 2",
                    ),
                ]
            } else if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= this->size;", ""),
                ]
            } else {
                // As above, the two statements of the fee bound are removed
                // together.
                vec![
                    source
                        .replace("requires this->fee < 8589934592i64;", "")
                        .replace("requires to_integer(this->fee) <= 8589934591;", ""),
                    source.replace("requires 0 <= to_integer(this->fee);", ""),
                    source.replace(
                        "ensures to_integer(result) == truncating_quotient(",
                        "ensures to_integer(result) != truncating_quotient(",
                    ),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                ]
            }
        } else if name.ends_with("Negative") || name.ends_with("PositiveWide") {
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= this->size;", ""),
                ]
            } else {
                vec![
                    source.replace(
                        if name.ends_with("Negative") {
                            "requires not (this->fee >= 0i64);"
                        } else {
                            "requires this->fee >= 0i64 and not (this->fee < 8589934592i64);"
                        },
                        "",
                    ),
                    source.replace("requires to_integer(this->fee) <= 9223372036854775807;", ""),
                    source
                        .replace("* to_integer(this->size) <=", "* to_integer(this->size) <")
                        .replace(
                            "<= to_integer(result) * to_integer(this->size)",
                            "< to_integer(result) * to_integer(this->size)",
                        ),
                    source.replace(
                        "to_integer(product) == to_integer(this->fee) * to_integer(at_size)",
                        "to_integer(product) == to_integer(this->fee) * to_integer(at_size) + 1",
                    ),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                ]
            }
        } else {
            vec![
                source.replace("views this->size;", ""),
                source.replace("requires this->size == 3;", ""),
                source.replace("requires at_size == 2;", ""),
                source.replace("ensures result ==", "ensures result !="),
            ]
        };
        for (index, hostile) in hostile.into_iter().enumerate() {
            assert_ne!(
                hostile, source,
                "a rejection must change the claim or premises"
            );
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("{name} accepted hostile case {index}");
            };
            assert!(error.message().len() < 8000);
        }
    }
    if bounded_div && phase == Some(RoundingPhase::FullExpansion) {
        let expanded = expand_project_claim_source_by_label(
            &project,
            &ProgramInputs::program(&import),
            "FeeFrac::Div.ensures_0",
        )
        .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
    }
    if result_fit_div && phase == Some(RoundingPhase::Rejections) {
        let down = name.ends_with("Down");
        let mode_guard = if down {
            "requires round_down != 0;"
        } else {
            "requires round_down == 0;"
        };
        let lower = if down {
            "requires -9223372036854775808 * to_integer(d) <= to_integer(n);"
        } else {
            "requires -9223372036854775809 * to_integer(d) < to_integer(n);"
        };
        let upper = if down {
            "requires to_integer(n) < 9223372036854775808 * to_integer(d);"
        } else {
            "requires to_integer(n) <= 9223372036854775807 * to_integer(d);"
        };
        let strict = if down { upper } else { lower };
        for hostile in [
            source.replace(mode_guard, ""),
            source.replace(lower, ""),
            source.replace(upper, ""),
            source.replace("requires d > 0;", ""),
            // `d <= 2147483647` holds of any `int32`; removing it weakens nothing.
            source.replace("requires d > 0;", "requires d == 0;"),
            source.replace(strict, &strict.replace(" < ", " <= ")),
        ] {
            assert_ne!(hostile, source);
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("{name} accepted missing or weakened result-fit guard");
            };
            assert!(error.message().len() < 8000);
        }
    }
    if result_fit_div && phase == Some(RoundingPhase::TransportRejections) {
        let down = name.ends_with("Down");
        let strict_bound = if down {
            "to_integer(n) < (to_integer(result) + 1) * to_integer(d)"
        } else {
            "(to_integer(result) + -1) * to_integer(d) < to_integer(n)"
        };
        let bad_bound = if down {
            "to_integer(n) < to_integer(result) * to_integer(d)"
        } else {
            "to_integer(result) * to_integer(d) < to_integer(n)"
        };
        let inclusive = if down {
            "to_integer(result) * to_integer(d) <= to_integer(n)"
        } else {
            "to_integer(n) <= to_integer(result) * to_integer(d)"
        };
        let correction = if down {
            "apply(integer_lower_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), -9223372036854775808));"
        } else {
            "apply(integer_upper_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), 9223372036854775807));"
        };
        for hostile in [
            source.replace(strict_bound, bad_bound),
            source.replace(inclusive, &inclusive.replace(" <= ", " < ")),
            source.replace(correction, ""),
            source.replace(
                "integer_cast_identity bounds [0, 1]",
                "integer_cast_identity bounds [1, 0]",
            ),
            source.replace(
                "ensures -9223372036854775808 <= to_integer(result);",
                "ensures to_integer(result) == 9223372036854775808;",
            ),
        ] {
            assert_ne!(hostile, source);
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("{name} accepted false rounding or missing narrowing/correction evidence");
            };
            assert!(error.message().len() < 8000);
        }
    }
    if name == "FeeFracDivBounded" && phase == Some(RoundingPhase::Rejections) {
        for hostile in [
            source.replace(
                "round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n)",
                "round_down != 0 implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),
            source.replace(
                "round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d)",
                "round_down != 0 implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            source.replace(
                "round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d)",
                "round_down == 0 implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            source.replace(
                "round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n)",
                "round_down == 0 implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),
            source.replace(
                "requires -9223372036854775808 * to_integer(d) <= to_integer(n);",
                "",
            ),
            source.replace(
                "requires to_integer(n) <= 9223372036854775807 * to_integer(d);",
                "",
            ),
            source.replace("requires d > 0;", ""),
            // `d <= 2147483647` holds of any `int32`; removing it weakens nothing.
            source.replace("requires d > 0;", "requires d == 0;"),
            source.replace(
                "ensures -9223372036854775808 <= to_integer(result);",
                "ensures to_integer(result) == 9223372036854775808;",
            ),
            source.replace(
                "integer_cast_identity bounds [0, 1]",
                "integer_cast_identity bounds [1, 0]",
            ),
        ] {
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().len() < 8000);
        }
    }
    if selected == "FeeFrac::Mul" {
        assert!(import.export().records.is_empty());
        assert_eq!(import.export().functions[0].parameters.len(), 2);
        // These four endpoints follow from the parameter types. Their
        // 64-by-32-bit product fits in int128 for every input.
        let mut full_domain = source.to_string();
        let mut intrinsic_proofs = String::new();
        for redundant in [
            "requires -9223372036854775808 <= to_integer(a);",
            "requires to_integer(a) <= 9223372036854775807;",
            "requires -2147483648 <= to_integer(b);",
            "requires to_integer(b) <= 2147483647;",
        ] {
            assert!(full_domain.contains(redundant));
            full_domain = full_domain.replace(redundant, "");
            let bound = redundant
                .strip_prefix("requires ")
                .unwrap()
                .strip_suffix(';')
                .unwrap();
            intrinsic_proofs.push_str(&format!(
                "have {bound} by {{ arithmetic_certificate {{ type_range => {bound}; conclusion 0; }} }}\n"
            ));
        }
        full_domain = full_domain.replacen("} by {", &format!("}} by {{\n{intrinsic_proofs}"), 1);
        let parsed = read_click_project(&sidecar, &full_domain).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect("type_range supplies every intrinsic endpoint without caller requirements");

        // Keep missing-premise controls with bounds that the types do not
        // imply. The original full-domain positive contract stays above.
        let bounded = source
            .replace("-9223372036854775808", "-100")
            .replace("9223372036854775807", "100")
            .replace("-2147483648", "-10")
            .replace("2147483647", "10");
        let parsed = read_click_project(&sidecar, &bounded).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect("the explicitly bounded certificate is valid");
        for omitted in [
            "requires -100 <= to_integer(a);",
            "requires to_integer(a) <= 100;",
            "requires -10 <= to_integer(b);",
            "requires to_integer(b) <= 10;",
        ] {
            assert!(bounded.contains(omitted));
            let hostile = bounded.replace(omitted, "");
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            assert!(
                verify_program_prepared_project(&parsed, &import).is_err(),
                "a certificate cannot cite the missing bound {omitted}"
            );
        }
        for false_result in ["0", "to_integer(a) * to_integer(b) + 1"] {
            // a = b = 1 refutes the zero result; adding one is always false.
            let hostile = source.replace(
                "ensures to_integer(result) == to_integer(a) * to_integer(b);",
                &format!("ensures to_integer(result) == {false_result};"),
            );
            assert_ne!(hostile, source);
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            assert!(
                verify_program_prepared_project(&parsed, &import).is_err(),
                "the original multiplication must reject {false_result}"
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_fee_frac_mul_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::Mul",
        "FeeFracMul",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click"),
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_fee_frac_div_imports_and_retains_native_proof_obligations() {
    check_upstream_fee_frac("FeeFrac::Div", "FeeFracDivImported", "");
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn pinned_upstream_fee_frac_div_consteval_contract_reaches_runtime_string_view_boundary() {
    check_upstream_fee_frac("FeeFrac::Div", "FeeFracDivConstevalRefused", "");
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn pinned_upstream_fee_frac_div_refuses_unmodelled_library_assume() {
    check_upstream_fee_frac("FeeFrac::Div", "FeeFracDivRefused", "");
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_isempty_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::IsEmpty",
        "FeeFracIsEmpty",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click"),
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_fee_frac_add_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator+=",
        "FeeFracAdd",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracAdd.click"),
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_addself_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator+=",
        "FeeFracAddSelf",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracAddSelf.click"),
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_subtract_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator-=",
        "FeeFracSubtract",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracSubtract.click"),
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_subtractself_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator-=",
        "FeeFracSubtractSelf",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracSubtractSelf.click"),
    );
}

fn pinned_span_fixture_with_exact_dependencies(
    name: &str,
    harness: &str,
    declaration_dependencies: &[&str],
) -> (PathBuf, PreparedCppImport) {
    assert_eq!(
        sha256(ARCHIVE),
        "fceeaef86784f820339f6dc3fc24992eb9c6bcf52edccbf6b7869d79296a3c7d"
    );
    let root =
        std::env::temp_dir().join(format!("click-bitcoin-span-{name}-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let archive = root.join("input-closure.tar.gz");
    fs::write(&archive, ARCHIVE).unwrap();
    assert!(
        Command::new("tar")
            .args([
                "-xzf",
                archive.to_str().unwrap(),
                "-C",
                root.to_str().unwrap()
            ])
            .status()
            .unwrap()
            .success()
    );
    for (header, digest) in [
        (
            "bitcoin-src/src/span.h",
            "485dc37ba8ed9b0e8d8212061122a5c1cd4e71e6ecc5380ac1a2277de395b0e3",
        ),
        (
            "sysroot/usr/include/c++/12/span",
            "f1e67ea2c1e2e0faef697f37d995abb59eeb7fb0c0cf13a586fe2799ed9196bd",
        ),
    ] {
        assert_eq!(sha256(&fs::read(root.join(header)).unwrap()), digest);
    }
    fs::create_dir_all(root.join("bitcoin-build/src")).unwrap();
    // Only the harness TU changes; the archived sources and compile flags do not.
    fs::write(root.join("span-probe.cpp"), harness).unwrap();
    let clang = pinned_clang();
    let database = COMMAND
        .replace("@ROOT@", root.to_str().unwrap())
        .replace("@CLANGXX@", clang.to_str().unwrap())
        .replace("@RESOURCE_DIR@", &output(&clang, &["-print-resource-dir"]))
        .replace("bitcoin-src/src/policy/feerate.cpp", "span-probe.cpp");
    fs::write(root.join("compile_commands.json"), database).unwrap();
    let exporter = root.join("click-cpp-exporter");
    fs::copy(std::env::var("CLICK_CPP_EXPORTER").unwrap(), &exporter).unwrap();
    let mut config = serde_json::json!({
        "schema": 6, "language": "c++", "standard": "c++20", "target": "x86_64-unknown-linux-gnu",
        "exceptions": true, "rtti": true, "exporter": exporter,
        "compilation_database": "compile_commands.json", "working_directory": ".",
        "source": "span-probe.cpp", "logical_source": "span-probe.cpp",
        "dependencies": [],
        "function": "probe", "artifact": "span.click-cpp.json"
    });
    let dependencies = config["dependencies"].as_array_mut().unwrap();
    dependencies.extend(declaration_dependencies.iter().map(|path| (*path).into()));
    dependencies.sort_by(|a, b| a.as_str().cmp(&b.as_str()));
    let config_path = root.join("span.import-description.json");
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    refresh_import(&config_path).unwrap();
    fs::remove_file(exporter).unwrap();
    let import = load_import(&config_path).unwrap();
    (root, import)
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
// The actual archived declaration is an empty scoped enum. Forwarding all of
// its native values must work without inventing enumerators or backing access.
fn pinned_std_byte_values_verify_with_native_integer_contracts_offline() {
    use click::languages::cpp::CppType;
    let header = "sysroot/usr/include/c++/12/cstddef";
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-values",
        "#include <span.h>\nstd::byte probe(std::byte value) noexcept { return value; }\n",
        &[header],
    );
    assert_eq!(
        sha256(&fs::read(root.join(header)).unwrap()),
        "51409c852efecb6e4de3ef7c31e51e63ddd4ec376ee00e3c68e85e6579fa8648"
    );
    let CppType::Enumeration {
        declaration_id,
        name,
        is_scoped,
        is_fixed,
        span,
        ..
    } = &import.export().functions[0].return_type
    else {
        panic!("std::byte lost its nominal enum declaration");
    };
    assert_eq!(declaration_id, "c:@N@std@E@byte");
    assert_eq!(name, "std::byte");
    assert!(*is_scoped && *is_fixed);
    assert_eq!(span.file, header);
    let source = "verifying \"span-probe.cpp\"; uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }";
    let path = root.join("byte.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
    let position = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "probe.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    fs::remove_dir_all(root).unwrap();
}

// A nominal template argument must survive even if its record fields never
// mention the enum. This closes the offline declaration-authentication gap.
#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn pinned_std_byte_template_record_keeps_nominal_argument() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-template-record",
        "#include <span.h>\ntemplate<class T> struct Holder { int value; };\nusing Byte = std::byte;\nint probe(const Holder<Byte>& h) noexcept { return h.value; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let record = import
        .export()
        .records
        .iter()
        .find(|record| record.name == "Holder__std_byte")
        .unwrap();
    assert_eq!(record.byte_template_arguments.len(), 1);
    assert_eq!(record.byte_template_arguments[0].index, 0);
    let source = "verifying \"span-probe.cpp\"; int32 probe(const struct Holder__std_byte& h) { views h.value; ensures result == h.value; } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
}

// The selected assumed interface preserves the descriptor's address and
// length. Reading its fields requires views, but grants no backing authority.
#[test]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn pinned_writable_byte_span_reference_preserves_view_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "writable-byte-span-reference",
        "#include <span.h>\nstd::span<std::byte> probe(const std::span<int>& span) noexcept { return std::as_writable_bytes(span); }\n",
        &[
            "sysroot/usr/include/c++/12/cstddef",
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let source = "verifying \"span-probe.cpp\"; std::span<std::byte> probe(const std::span<int>& span) { views std_span_data(span); views std_span_size(span); ensures std_span_data(result) == (uint8*)std_span_data(span); ensures std_span_size(result) == std_span_size(span) * 4u64; ensures std_span_data(span) == old(std_span_data(span)); ensures std_span_size(span) == old(std_span_size(span)); } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
}

// Keep the fixed by-value source and true claim for the documented snapshot
// proof gap. Restore the positive E/R check when that gap is repaired.
#[test]
#[ignore = "nightly: pinned C++ by-value span certificate round trip"]
fn pinned_writable_byte_span_by_value_preserves_pointer_snapshot() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "writable-byte-span",
        "#include <span.h>\nstd::span<std::byte> probe(std::span<int> span) noexcept { return std::as_writable_bytes(span); }\n",
        &[
            "sysroot/usr/include/c++/12/cstddef",
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let source = "verifying \"span-probe.cpp\"; std::span<std::byte> probe(std::span<int> span) { ensures std_span_data(result) == old((uint8*)std_span_data(span)); ensures std_span_size(result) == old(std_span_size(span)) * 4u64; } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: repeated offline artifact and contract refusals"]
fn pinned_byte_template_metadata_and_span_authority_are_checked() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-template-rejections",
        "#include <span.h>\ntemplate<class T> struct Holder { int value; };\nint probe(const Holder<std::byte>& h) noexcept { return h.value; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let artifact_path = cpp_description::artifact(&root.join("span.import-description.json"));
    let lock_path = root.join(click::project::LOCK_NAME);
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(&artifact_path).unwrap()).unwrap();
    let lock: serde_json::Value = serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    for change in 0..7 {
        let mut forged = artifact.clone();
        let record = forged["records"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|record| record["name"] == "Holder__std_byte")
            .unwrap();
        match change {
            0 => record["byte_template_arguments"] = serde_json::json!([]),
            1 => record["byte_template_arguments"][0]["index"] = 1.into(),
            2 => {
                record["byte_template_arguments"][0]["value_type"]["declaration_id"] =
                    "c:@E@Other".into()
            }
            3 => {
                record["byte_template_arguments"][0]["value_type"]["span"]["file"] =
                    "span-probe.cpp".into()
            }
            4 => {
                record["byte_template_arguments"][0]["value_type"]["underlying_type"]["bits"] =
                    32.into()
            }
            5 => {
                let duplicate = record["byte_template_arguments"][0].clone();
                record["byte_template_arguments"]
                    .as_array_mut()
                    .unwrap()
                    .push(duplicate);
            }
            6 => forged["preprocessor_files"]
                .as_array_mut()
                .unwrap()
                .retain(|file| {
                    !file["canonical_path"]
                        .as_str()
                        .unwrap()
                        .ends_with("/cstddef")
                }),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] = sha256(&bytes).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(&artifact_path, bytes).unwrap();
        fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
        assert!(
            load_import(&root.join("span.import-description.json")).is_err(),
            "mutation {change}"
        );
    }
    drop(import);

    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "writable-byte-span-authority",
        "#include <span.h>\nstd::span<std::byte> probe(std::span<int> span) noexcept { return std::as_writable_bytes(span); }\n",
        &[
            "sysroot/usr/include/c++/12/cstddef",
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let base = "verifying \"span-probe.cpp\"; std::span<std::byte> probe(std::span<int> span) { ensures std_span_size(result) == std_span_size(span) * 4u64; } by { execute(); simp(); }";
    for bad in [
        base.replace(" * 4u64", " * 3u64"),
        base.replace("ensures std_span_size(result)", "ensures std_span_data(result) == (uint8*)std_span_data(span) + 1; ensures std_span_size(result)"),
        base.replace("ensures std_span_size(result)", "ensures 1u64 <= std_span_size(result); ensures std_span_size(result)"),
        base.replace(
            "ensures std_span_size(result)",
            "ensures std_span_data(result)[0] == 0u8; ensures std_span_size(result)",
        ),
    ] {
        fs::write(root.join("bad.click"), &bad).unwrap();
        let project = read_click_project(&root.join("bad.click"), &bad).unwrap();
        assert!(verify_program_prepared_project(&project, &import).is_err());
    }
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "writable-byte-span-reference",
        "#include <span.h>\nstd::span<std::byte> probe(const std::span<int>& span) noexcept { return std::as_writable_bytes(span); }\n",
        &[
            "sysroot/usr/include/c++/12/cstddef",
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let source = "verifying \"span-probe.cpp\"; std::span<std::byte> probe(const std::span<int>& span) { views std_span_data(span); views std_span_size(span); ensures std_span_data(result) == (uint8*)std_span_data(span); ensures std_span_size(result) == std_span_size(span) * 4u64; ensures std_span_data(span) == old(std_span_data(span)); ensures std_span_size(span) == old(std_span_size(span)); } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
    for field in ["std_span_data", "std_span_size"] {
        let bad = source.replace(&format!("views {field}(span);"), "");
        fs::write(root.join("bad.click"), &bad).unwrap();
        let project = read_click_project(&root.join("bad.click"), &bad).unwrap();
        assert!(verify_program_prepared_project(&project, &import).is_err());
    }
}

#[test]
#[ignore = "nightly: 16s in the parallel gate"]
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
    let config_path = root.join("MoneyRange.import-description.json");
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
        instrumentation::collect(|| verify_program_prepared_project(&project, &imported));
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

    let sites =
        project_smart_tactic_source_sites(&project, &ProgramInputs::program(&imported)).unwrap();
    assert_eq!(
        sites.len(),
        14,
        "audit must cover every upstream smart tactic"
    );
    for event in &profile {
        if let VerificationEvent::TacticFinished { tactic, .. } = event {
            project_tactic_source_position(
                &project,
                &ProgramInputs::program(&imported),
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
    let mut session_checks = Vec::new();
    let expanded_contract = expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::program(&imported),
        "MoneyRange.contract",
    )
    .expect("the documented claim expansion must use the locked upstream import");
    verify_program_prepared_project(&project.with_entry_source(expanded_contract), &imported)
        .expect("the documented expanded range claim must reverify");
    for site in sites {
        let claim = site.claim_label.as_str();
        let position = project_tactic_source_position(
            &project,
            &ProgramInputs::program(&imported),
            claim,
            site.source_index,
        )
        .expect("each upstream claim has a selectable tactic");
        let profiled_claim = if claim.ends_with(".ensures_0") {
            claim.replace(".ensures_0", ".contract")
        } else {
            claim.to_owned()
        };
        let profiled_position = project_tactic_source_position(
            &project,
            &ProgramInputs::program(&imported),
            &profiled_claim,
            site.source_index,
        )
        .expect("the profiler must resolve the same upstream tactic location");
        assert_eq!(profiled_position, position);
        let expanded = expand_project_tactic_source_at(
            &project,
            &ProgramInputs::program(&imported),
            position.line,
            position.column,
        )
        .expect("expand a tactic against the same locked import");
        assert_ne!(expanded, SIDECAR);
        let rewritten = project.with_entry_source(expanded.clone());
        let remaining =
            project_smart_tactic_source_sites(&rewritten, &ProgramInputs::program(&imported))
                .expect("expanded proof remains source-inventoriable")
                .into_iter()
                .filter(|candidate| candidate.claim_label == claim)
                .count();
        let original =
            project_smart_tactic_source_sites(&project, &ProgramInputs::program(&imported))
                .unwrap()
                .into_iter()
                .filter(|candidate| candidate.claim_label == claim)
                .count();
        assert!(
            remaining < original,
            "expansion must remove the audited smart site"
        );
        verify_program_prepared_project(&rewritten, &imported)
            .expect("expanded certificate must reverify against the upstream import");
        let next = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&imported),
            claim,
            0,
        )
        .expect("the audited claim remains source-selectable");
        session_checks.push((expanded, next));
    }
    // A retained session's environment names its own kernel tables, which
    // every verification above replaces, so the session starts after them.
    let (session, _) = C0VerificationSession::new_program_prepared_project(&project, &imported)
        .expect("start a retained audit session on the same import");
    for (expanded, next) in &session_checks {
        session
            .verify_at_project(expanded, next.line, next.column)
            .expect("audit session must accept the expanded certificate");
    }

    let source_contract = SIDECAR
        .split_once("contract bool BelowRange")
        .expect("the modular boundary contracts follow MoneyRange")
        .0;
    let false_source = source_contract.replace(
        "if old(nValue) <= 2100000000000000i64",
        "if old(nValue) < 2100000000000000i64",
    );
    assert_ne!(false_source, source_contract);
    fs::write(&sidecar, &false_source).unwrap();
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let false_error = verify_program_prepared_project(&false_project, &imported)
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
    // A project unit re-reads each rooted input and names the one whose
    // bytes changed.
    let changed_dependency = load_import(&config_path).unwrap_err();
    assert!(
        changed_dependency.contains("c++/12/limits` differs from its import lock"),
        "{changed_dependency}"
    );
    fs::write(&transitive, transitive_bytes).unwrap();
    load_import(&config_path).expect("restoring a transitive header restores the locked import");

    let database_path = root.join("compile_commands.json");
    let database_bytes = fs::read_to_string(&database_path).unwrap();
    // The unit states the command's arguments, so changing one changes the
    // unit's description, which the lock no longer matches.
    let changed_database = database_bytes.replace(" -g ", " -g -DCLICK_COMMAND_VARIANT=1 ");
    assert_ne!(changed_database, database_bytes);
    fs::write(&database_path, changed_database).unwrap();
    let changed_command = load_import(&config_path).unwrap_err();
    assert!(
        changed_command.contains("does not match its description"),
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
        changed_profile.contains("does not match its description"),
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
        stale_selector.contains("has no source `bitcoin-src/src/policy/feerate.h`"),
        "{stale_selector}"
    );
    fs::write(&config_path, config_bytes).unwrap();
    load_import(&config_path).expect("the original selector and lock remain valid");
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn pinned_upstream_compact_size_1_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize1",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize1.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_compact_size_3_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize3",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize3.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_compact_size_5_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize5",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize5.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_compact_size_9_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize9",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize9.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fee_frac_div_bounded_native_correction_is_safe() {
    check_bounded_upstream_rounding(RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fee_frac_div_bounded_full_expansion_reverifies() {
    check_bounded_upstream_rounding(RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fee_frac_div_bounded_rejects_false_rounding_and_missing_guards() {
    check_bounded_upstream_rounding(RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_result_fit_div_down_verifies_native_narrowing_and_correction() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_down_expands_and_reverifies() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_down_rejects_missing_or_inclusive_fit_guards() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_result_fit_div_down_rejects_false_rounding_and_missing_transport() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_result_fit_div_up_verifies_native_narrowing_and_correction() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_up_expands_and_reverifies() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_up_rejects_missing_or_inclusive_fit_guards() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_result_fit_div_up_rejects_false_rounding_and_missing_transport() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::TransportRejections);
}

fn check_result_fit_upstream_rounding(mode: &str, phase: RoundingPhase) {
    let source = match mode {
        "Down" => {
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitDown.click")
        }
        "Up" => {
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitUp.click")
        }
        _ => unreachable!(),
    };
    check_upstream_cpp_rounding_phase(
        "FeeFrac::Div",
        &format!("FeeFracDivResultFit{mode}"),
        source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

fn check_bounded_upstream_rounding(phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        "FeeFrac::Div",
        "FeeFracDivBounded",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click"),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

fn check_upstream_fee_evaluation_fast(mode: &str, expected: i64, phase: RoundingPhase) {
    let instance = if mode == "Down" { "true" } else { "false" };
    let contract = format!(
        "views this->fee; views this->size; requires this->fee == 7i64; requires this->size == 3; requires at_size == 2; ensures result == {expected}i64; ensures this->fee == old(this->fee); ensures this->size == old(this->size);"
    );
    let (imports, div) = fixture_imports_and_body(include_str!(
        "../integrations/bitcoin-core-money-range/FeeFracDivBounded.click"
    ));
    let source = format!(
        r#"{imports}
{}
{div}
int64 FeeFrac::EvaluateFee<{instance}>(int32 at_size) const {{ {contract} }} by {{ execute(); simp(); }}
int64 FeeFrac::EvaluateFee{mode}(int32 at_size) const {{ {contract} }} by {{ execute(); simp(); }}
"#,
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    );
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}Fast"),
        &source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fee_evaluation_down_exports_full_graph_and_verifies_fast_case() {
    check_upstream_fee_evaluation_fast("Down", 4, RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fee_evaluation_up_exports_full_graph_and_verifies_fast_case() {
    check_upstream_fee_evaluation_fast("Up", 5, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fee_evaluation_down_rejects_missing_authority_bounds_and_false_results() {
    check_upstream_fee_evaluation_fast("Down", 4, RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fee_evaluation_up_rejects_missing_authority_bounds_and_false_results() {
    check_upstream_fee_evaluation_fast("Up", 5, RoundingPhase::Rejections);
}

fn check_upstream_result_fit_fast_fee_evaluation(mode: &str, phase: RoundingPhase) {
    let (div, caller) = match mode {
        "Down" => (
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitDown.click"),
            include_str!(
                "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitDown.click.in"
            ),
        ),
        "Up" => (
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitUp.click"),
            include_str!(
                "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitUp.click.in"
            ),
        ),
        _ => unreachable!(),
    };
    let (imports, div) = fixture_imports_and_body(div);
    let source = format!(
        "{imports}\n{}\n{div}\n{caller}",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    );
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}ResultFitSymbolicFast"),
        &source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_down_verifies_beyond_size() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fast_result_fit_down_expands_and_reverifies() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_missing_fee_and_branch_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_false_rounding() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::NumeratorRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fast_result_fit_up_verifies_beyond_size() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fast_result_fit_up_expands_and_reverifies() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_missing_fee_and_branch_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_false_rounding() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

fn check_upstream_symbolic_fast_fee_evaluation(mode: &str, phase: RoundingPhase) {
    let (imports, div) = fixture_imports_and_body(include_str!(
        "../integrations/bitcoin-core-money-range/FeeFracDivBounded.click"
    ));
    let caller = if mode == "Down" {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateFastDown.click.in")
    } else {
        assert_eq!(mode, "Up");
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateFastUp.click.in")
    };
    let source = format!(
        "{imports}\n{}\n{div}\n{caller}",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    );
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}SymbolicFast"),
        &source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_has_exact_floor_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_expands_and_reverifies() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_rejects_missing_authority_and_amount_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_rejects_missing_fee_bounds_and_false_rounding() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_has_exact_ceiling_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_expands_and_reverifies() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_authority_and_amount_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_fee_bounds_and_false_rounding() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::TransportRejections);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

fn wide_fee_evaluation_source(mode: &str, positive: bool) -> String {
    wide_fee_evaluation_source_with_profile(mode, positive, false)
}

fn wide_fee_evaluation_source_with_profile(mode: &str, positive: bool, result_fit: bool) -> String {
    let down = mode == "Down";
    let bounds = |result: &str, size: &str, product: &str| {
        if down {
            [
                format!("{result} * {size} <= {product}"),
                format!("{product} < ({result} + 1) * {size}"),
            ]
        } else {
            [
                format!("{product} <= {result} * {size}"),
                format!("({result} + -1) * {size} < {product}"),
            ]
        }
    };
    let caller = bounds(
        "to_integer(result)",
        "to_integer(this->size)",
        "to_integer(this->fee) * to_integer(at_size)",
    );
    let helper = bounds(
        "to_integer(rounded)",
        "to_integer(denominator)",
        "to_integer(product)",
    );
    let fit_bounds = |product: &str| {
        if down {
            [
                format!("-9223372036854775808 * to_integer(this->size) <= {product}"),
                format!("{product} < 9223372036854775808 * to_integer(this->size)"),
            ]
        } else {
            [
                format!("-9223372036854775809 * to_integer(this->size) < {product}"),
                format!("{product} <= 9223372036854775807 * to_integer(this->size)"),
            ]
        }
    };
    let input = fit_bounds("to_integer(this->fee) * to_integer(at_size)");
    let product = fit_bounds("to_integer(product)");
    let template = if result_fit {
        include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateWideResultFit.click.in"
        )
    } else {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateWide.click.in")
    };
    let fragment = template
        .replace(
            "@WIDE_GUARD@",
            if positive {
                "this->fee >= 0i64 and not (this->fee < 8589934592i64)"
            } else {
                "not (this->fee >= 0i64)"
            },
        )
        .replace("@MODE@", mode)
        .replace("@INSTANCE@", if down { "true" } else { "false" })
        .replace("@ROUND@", if down { "1" } else { "0" })
        .replace("@CALLER_BOUND_1@", &caller[0])
        .replace("@CALLER_BOUND_2@", &caller[1])
        .replace("@DIV_BOUND_1@", &helper[0])
        .replace("@DIV_BOUND_2@", &helper[1])
        .replace("@INPUT_BOUND_1@", &input[0])
        .replace("@INPUT_BOUND_2@", &input[1])
        .replace("@PRODUCT_BOUND_1@", &product[0])
        .replace("@PRODUCT_BOUND_2@", &product[1])
        .replace(
            "@FEE_WITNESS@",
            if positive {
                "8589934592"
            } else {
                "-8589934592"
            },
        );
    assert!(!fragment.contains('@'));
    let (imports, div) = fixture_imports_and_body(if !result_fit {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click")
    } else if down {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitDown.click")
    } else {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitUp.click")
    });
    format!(
        "{imports}\n{}\n{div}\n{fragment}",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    )
}

fn check_upstream_result_fit_wide_fee_evaluation(mode: &str, positive: bool, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!(
            "FeeFracEvaluate{mode}ResultFit{}",
            if positive { "PositiveWide" } else { "Negative" }
        ),
        &wide_fee_evaluation_source_with_profile(mode, positive, true),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation(
        "Down",
        false,
        RoundingPhase::TransportRejections,
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::TransportRejections);
}

fn unified_fee_evaluation_source(mode: &str) -> String {
    unified_fee_evaluation_source_with_profile(mode, false)
}

fn unified_fee_evaluation_source_with_profile(mode: &str, result_fit: bool) -> String {
    let wide = wide_fee_evaluation_source_with_profile(mode, true, result_fit);
    let (helpers, callers) = wide.split_once("int64 FeeFrac::EvaluateFee<").unwrap();
    let wide_body = callers
        .split_once("} by {")
        .unwrap()
        .1
        .split_once("\n}\nint64")
        .unwrap()
        .0;
    assert!(
        wide_body.contains("let { result: product } ="),
        "{wide_body}"
    );
    let negative = wide_body
        .replace("denominator", "negative_denominator")
        .replace(
            "let { result: product } =",
            "let { result: negative_product } =",
        )
        .replace("to_integer(product)", "to_integer(negative_product)")
        .replace("FeeFrac::Div(product,", "FeeFrac::Div(negative_product,")
        .replace("rounded", "negative_rounded");
    let fast = match (mode, result_fit) {
        ("Down", false) => include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastDown.click.in"
        ),
        ("Up", false) => {
            include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateFastUp.click.in")
        }
        ("Down", true) => include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitDown.click.in"
        ),
        ("Up", true) => include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitUp.click.in"
        ),
        _ => panic!("unknown rounding mode"),
    };
    let fast_body = fast
        .split_once("} by {")
        .unwrap()
        .1
        .split_once("\n}\n\nint64")
        .unwrap()
        .0;
    let fast_body = fast_body.strip_suffix("    simp();").unwrap();
    let contract = callers.split_once("} by {").unwrap().0;
    let bounds = contract
        .lines()
        .filter_map(|l| l.trim().strip_prefix("ensures "))
        .filter(|l| l.contains(" * "))
        .map(|l| l.trim_end_matches(';'))
        .collect::<Vec<_>>();
    assert_eq!(bounds.len(), 2);
    let input_bounds = contract
        .lines()
        .filter_map(|l| l.trim().strip_prefix("requires "))
        .filter(|l| l.contains(" * "))
        .map(|l| l.trim_end_matches(';'))
        .collect::<Vec<_>>();
    let template = if result_fit {
        assert_eq!(input_bounds.len(), 2);
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateResultFit.click.in")
    } else {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateBounded.click.in")
    };
    let template = if result_fit {
        template
            .replace("@INPUT_BOUND_1@", input_bounds[0])
            .replace("@INPUT_BOUND_2@", input_bounds[1])
    } else {
        template.to_owned()
    };
    let fragment = template
        .replace("@INSTANCE@", if mode == "Down" { "true" } else { "false" })
        .replace("@MODE@", mode)
        .replace("@CALLER_BOUND_1@", bounds[0])
        .replace("@CALLER_BOUND_2@", bounds[1])
        .replace("@FAST_PROOF@", fast_body)
        .replace("@WIDE_POSITIVE_PROOF@", wide_body)
        .replace("@WIDE_NEGATIVE_PROOF@", &negative);
    assert!(!fragment.contains('@'));
    format!("{helpers}{fragment}")
}

fn check_upstream_result_fit_unified_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}ResultFitUnified"),
        &unified_fee_evaluation_source_with_profile(mode, true),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_down_verifies_all_fee_branches_beyond_size() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_down_expands_and_reverifies() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_field_authority() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::AuthorityRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_domain_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::FitRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_down_checks_native_fee_bounds_and_branch_transport() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_false_rounding() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::NumeratorRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_up_verifies_all_fee_branches_beyond_size() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_up_expands_and_reverifies() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_field_authority() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::AuthorityRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_domain_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::FitRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_up_checks_native_fee_bounds_and_branch_transport() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_false_rounding() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_or_forged_adjusted_numerator() {
    check_upstream_result_fit_unified_fee_evaluation(
        "Up",
        RoundingPhase::AdjustedNumeratorRejections,
    );
}

fn check_upstream_unified_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}Unified"),
        &unified_fee_evaluation_source(mode),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_verifies_all_fee_branches() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_verifies_all_fee_branches() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_expands_and_reverifies() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_expands_and_reverifies() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_rejects_missing_domain_bounds() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_rejects_missing_domain_bounds() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_rejects_false_rounding_and_missing_transport() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::TransportRejections);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_rejects_false_rounding_and_missing_transport() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

fn check_upstream_negative_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}Negative"),
        &wide_fee_evaluation_source(mode, false),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_has_symbolic_floor_bounds() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_has_symbolic_ceiling_bounds() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_instance_expands_and_reverifies() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_instance_expands_and_reverifies() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_rejects_false_bounds_and_missing_guards() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_rejects_false_bounds_and_missing_guards() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_rejects_forged_product_and_rounding_transport() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::TransportRejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_rejects_forged_product_and_rounding_transport() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

fn check_upstream_positive_wide_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}PositiveWide"),
        &wide_fee_evaluation_source(mode, true),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_has_symbolic_bounds() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_instance_expands_and_reverifies() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_rejects_false_bounds_and_missing_guards() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_rejects_forged_product_and_rounding_transport() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_has_symbolic_bounds() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_instance_expands_and_reverifies() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_rejects_false_bounds_and_missing_guards() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_rejects_forged_product_and_rounding_transport() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_rate_getfee_imports_converted_call_graph() {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeImported",
        "",
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

fn getfee_source() -> String {
    let unified = unified_fee_evaluation_source_with_profile("Up", true);
    let helpers = unified
        .split_once("\ncontract int64 FastOversizeFee")
        .unwrap()
        .0
        .replace(
            "verifying \"bitcoin-src/src/util/feefrac.h\";",
            "verifying \"bitcoin-src/src/policy/feerate.cpp\";",
        );
    let (imports, empty) = fixture_imports_and_body(include_str!(
        "../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click"
    ));
    assert!(imports.is_empty());
    format!(
        "{helpers}\n{empty}\n{}",
        include_str!("../integrations/bitcoin-core-money-range/CFeeRateGetFee.click.in")
    )
}

fn check_getfee(name: &str, phase: Option<RoundingPhase>) {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        name,
        &getfee_source(),
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        phase,
    );
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_expands_and_reverifies_offline() {
    check_getfee(
        "CFeeRateGetFeeExpansion",
        Some(RoundingPhase::FullExpansion),
    );
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn upstream_getfee_retains_certificates_offline() {
    check_getfee("CFeeRateGetFeeRetained", Some(RoundingPhase::Tools));
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_modular_callers_cover_empty_negative_and_oversize_inputs() {
    let source = getfee_source();
    // The method's head leaves `this` implicit; a named contract for its
    // function type writes the receiver as a parameter.
    let root_contract = format!(
        "const struct CFeeRate* this, {}",
        source
            .split_once("int64 CFeeRate::GetFee(")
            .unwrap()
            .1
            .split_once("} by {")
            .unwrap()
            .0
            .replacen(") const {", ") {", 1)
    );
    let mut callers = String::new();
    for (name, requirements, conclusion) in [
        (
            "NegativeMinimumFee",
            "requires this->m_feerate.base.fee == -1i64; requires this->m_feerate.base.size == 2; requires virtual_bytes == 1; requires virtual_bytes != 0; requires this->m_feerate.base.fee < 0i64;",
            "ensures result != 0i64;",
        ),
        (
            "PositiveOversizeFee",
            "requires this->m_feerate.base.fee == 7i64; requires this->m_feerate.base.size == 1; requires virtual_bytes == 2;",
            "",
        ),
        (
            "ZeroAmountFee",
            "requires this->m_feerate.base.fee == 7i64; requires this->m_feerate.base.size == 2; requires virtual_bytes == 0;",
            "",
        ),
    ] {
        let proof = if conclusion.is_empty() {
            "execute(); simp();"
        } else {
            "have this->m_feerate.base.size != 0 by { simp(); } execute(); extract(result != 0i64); simp();"
        };
        let contract = root_contract.replacen(
            "views this->m_feerate.base.fee;",
            &format!("{requirements}\n    views this->m_feerate.base.fee;"),
            1,
        );
        callers.push_str(&format!("\ncontract int64 {name}({contract} {conclusion} }}\ntheorem {name}_application() executes CFeeRate::GetFee(const struct CFeeRate* this, int32 virtual_bytes) {{ ensures {name}(&CFeeRate::GetFee) by {{ {proof} }} }}\n"));
    }
    callers.push_str(r#"
contract int64 EmptyRate(const struct CFeeRate* this, int32 virtual_bytes) {
    views this->m_feerate.base.fee; views this->m_feerate.base.size;
    requires this->m_feerate.base.size == 0;
    requires 0 <= virtual_bytes; requires virtual_bytes <= 2147483647;
    ensures result == 0i64;
    ensures this->m_feerate.base.fee == old(this->m_feerate.base.fee);
    ensures this->m_feerate.base.size == old(this->m_feerate.base.size);
}
theorem empty_rate_application() executes CFeeRate::GetFee(const struct CFeeRate* this, int32 virtual_bytes) {
    ensures EmptyRate(&CFeeRate::GetFee) by {
        have this->m_feerate.base.size >= 0 by { arithmetic() using { this->m_feerate.base.size == 0; } }
        have this->m_feerate.base.size <= 2147483647 by { arithmetic() using { this->m_feerate.base.size == 0; } }
        have this->m_feerate.base.size != 0 implies -9223372036854775808 <= to_integer(this->m_feerate.base.fee) by { simp(); }
        have this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) <= 9223372036854775807 by { simp(); }
        have this->m_feerate.base.size != 0 implies -9223372036854775809 * to_integer(this->m_feerate.base.size) < to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes) by { simp(); }
        have this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes) <= 9223372036854775807 * to_integer(this->m_feerate.base.size) by { simp(); }
        execute(); simp();
    }
}
"#);
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeCallers",
        &format!("{source}{callers}"),
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_fee_authority() {
    check_getfee(
        "CFeeRateGetFeeMissingFeeAuthority",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_size_authority() {
    check_getfee(
        "CFeeRateGetFeeMissingSizeAuthority",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_amount_guard() {
    check_getfee(
        "CFeeRateGetFeeMissingAmountGuard",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_size_guard() {
    check_getfee(
        "CFeeRateGetFeeMissingSizeGuard",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_rejects_missing_lower_fit() {
    check_getfee(
        "CFeeRateGetFeeMissingLowerFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_rejects_missing_upper_fit() {
    check_getfee(
        "CFeeRateGetFeeMissingUpperFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_inclusive_lower_fit() {
    check_getfee(
        "CFeeRateGetFeeInclusiveLowerFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_rejects_false_empty_result() {
    check_getfee("CFeeRateGetFeeFalseEmpty", Some(RoundingPhase::Rejections));
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_getfee_rejects_false_minimum_correction() {
    check_getfee(
        "CFeeRateGetFeeFalseCorrection",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_accepts_native_fee_observer_bounds() {
    check_getfee(
        "CFeeRateGetFeeNativeFeeBounds",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_rejects_stale_reachable_header_offline() {
    check_getfee(
        "CFeeRateGetFeeStaleHeader",
        Some(RoundingPhase::TransportRejections),
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_composes_empty_and_nonempty_result_fit_profiles() {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeProof",
        &getfee_source(),
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

fn getfee_per_k_source() -> String {
    let unified = unified_fee_evaluation_source_with_profile("Down", true);
    let helpers = unified
        .split_once("\ncontract int64 FastOversizeFee")
        .unwrap()
        .0;
    format!(
        "{}\n{}",
        helpers.replace(
            "verifying \"bitcoin-src/src/util/feefrac.h\";",
            "verifying \"bitcoin-src/src/policy/feerate.h\";"
        ),
        include_str!("../integrations/bitcoin-core-money-range/CFeeRateGetFeePerK.click.in")
    )
}
fn check_getfee_per_k(name: &str, phase: Option<RoundingPhase>) {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFeePerK",
        name,
        &getfee_per_k_source(),
        "bitcoin-src/src/policy/feerate.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        phase,
    );
}
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_getfee_per_k_verifies_unchanged_down_rounding() {
    check_getfee_per_k("CFeeRateGetFeePerK", None);
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_expands_and_reverifies_offline() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKExpansion",
        Some(RoundingPhase::FullExpansion),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_per_k_retains_certificates_offline() {
    check_getfee_per_k("CFeeRateGetFeePerKRetained", Some(RoundingPhase::Tools));
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_zero_size() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKMissingSizeGuard",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_missing_authority() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKMissingFeeAuthority",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_missing_lower_fit() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKMissingLowerFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_inclusive_upper_fit() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKInclusiveUpperFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_false_rounding() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKFalseRounding",
        Some(RoundingPhase::Rejections),
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_modular_callers_cover_signed_and_oversize_rates() {
    let source = getfee_per_k_source();
    // The method's head leaves `this` implicit; a named contract for its
    // function type writes the receiver as a parameter.
    let root_contract = format!(
        "const struct CFeeRate* this{}",
        source
            .split_once("int64 CFeeRate::GetFeePerK(")
            .unwrap()
            .1
            .split_once("} by {")
            .unwrap()
            .0
            .replacen(") const {", ") {", 1)
    );
    let mut callers = String::new();
    for (name, fee, size) in [
        ("PositivePerK", 7_i64, 2),
        ("NegativePerK", -1, 2),
        ("ZeroPerK", 0, 2),
        ("WidePerK", 8589934592, 1000),
    ] {
        let contract = root_contract.replacen("views this->m_feerate.base.fee;", &format!("requires this->m_feerate.base.fee == {fee}i64; requires this->m_feerate.base.size == {size}; views this->m_feerate.base.fee;"), 1);
        callers.push_str(&format!("\ncontract int64 {name}({contract} }}\ntheorem {name}_application() executes CFeeRate::GetFeePerK(const struct CFeeRate* this) {{ ensures {name}(&CFeeRate::GetFeePerK) by {{ execute(); simp(); }} }}\n"));
    }
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFeePerK",
        "CFeeRateGetFeePerKCallers",
        &format!("{source}{callers}"),
        "bitcoin-src/src/policy/feerate.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

fn axiomatic_span_fixture(
    name: &str,
    harness: &str,
    dependencies: &[&str],
) -> (PathBuf, PreparedCppImport) {
    pinned_span_fixture_with_exact_dependencies(name, harness, dependencies)
}

#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn axiomatic_span_refused_precondition_names_model_accessors_after_execution() {
    let (root, import) = axiomatic_span_fixture(
        "model-precondition-spelling",
        "#include <span>\nstd::span<int> probe(std::span<int>& s) noexcept { unsigned long n = s.size(); return s.first(n - 1); }\n",
        SPAN_DEPENDENCIES,
    );
    let source = r#"verifying "span-probe.cpp";
std::span<int> probe(std::span<int>& s) {
    views std_span_data(s);
    views std_span_size(s);
    ensures std_span_data(result) == std_span_data(s);
} by { execute(); simp(); }
"#;
    let sidecar = root.join("span.click");
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("a possibly empty span does not justify first(n - 1)");
    let message = error.concise_report();
    assert!(message.contains("std_span_size(s)"), "{message}");
    assert!(message.contains("std_span_data(s)"), "{message}");
    assert!(!message.contains("&s["), "{message}");
    assert!(!message.contains("_M_"), "{message}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 5.9s in the parallel gate"]
fn axiomatic_span_dynamic_extent_requirement_is_proved_before_view_recovery() {
    let (root, import) = axiomatic_span_fixture(
        "dynamic-extent-prerequisite",
        "#include <span>\nstd::span<std::byte> probe(std::span<std::byte>& s) noexcept { return s.subspan(1, std::dynamic_extent); }\n",
        BYTE_SPAN_DEPENDENCIES,
    );
    let source = r#"verifying "span-probe.cpp";
std::span<std::byte> probe(std::span<std::byte>& s) {
    views std_span_data(s);
    views std_span_size(s);
    requires 1u64 <= std_span_size(s);
    ensures std_span_data(result) == std_span_data(s) + 1u64;
    ensures std_span_size(result) == std_span_size(s) - 1u64;
} by { execute(); simp(); }
"#;
    let sidecar = root.join("span.click");
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
    let hostile = source.replace("1u64 <= std_span_size(s)", "std_span_size(s) == 0u64");
    let parsed = read_click_project(&sidecar, &hostile).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("offset one is outside an empty span");
    let message = error.concise_report();
    assert!(message.contains("precondition"), "{message}");
    assert!(
        !message.contains("undischarged return obligation"),
        "{message}"
    );
    assert!(message.contains("precondition clause 3"), "{message}");
    fs::remove_dir_all(root).unwrap();
}

// Bitcoin's unchanged `SpanPopBack` verifies against Click's `std::span`
// contracts: libstdc++'s `size`, `back` and `first` are axioms with no
// exported body, and every contract states the span through model accessors.
#[test]
#[ignore = "nightly: 6.4s in the parallel gate"]
fn axiomatic_span_pop_back_verifies_against_catalog_contracts() {
    let (root, import) = axiomatic_span_fixture(
        "axiomatic-pop-back",
        "#include <span.h>\nint& probe(std::span<int>& span) { return SpanPopBack(span); }\n",
        &[
            "bitcoin-src/src/span.h",
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let axioms = import
        .export()
        .reachable_functions
        .iter()
        .filter_map(|function| function.axiom.as_ref())
        .map(|axiom| axiom.qualified_name.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        axioms,
        std::collections::BTreeSet::from([
            "std::span<int>::back",
            "std::span<int>::first",
            "std::span<int>::size"
        ])
    );
    let pop_back = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| function.name.starts_with("SpanPopBack"))
        .unwrap()
        .path
        .join("::");
    let source = format!(
        r#"import click::integer;
verifying "span-probe.cpp";
theorem uint64_predecessor_below(n: uint64) {{
    requires 1u64 <= n;
    ensures n - 1u64 <= n by {{
        apply(uint64_less_equal_to_integer(1u64, n));
        apply(uint64_subtract_to_integer(n, 1u64));
        have to_integer(n - 1u64) <= to_integer(n) by {{
            arithmetic() using {{ to_integer(n - 1u64) == to_integer(n) - 1; }}
        }}
        apply(uint64_to_integer_less_equal_implies_less_equal(n - 1u64, n));
    }}
}}
int32& {pop_back}(std::span<int>& span) {{
    owns std_span_data(span);
    owns std_span_size(span);
    requires 1u64 <= std_span_size(span);
    ensures std_span_data(span) == old(std_span_data(span));
    ensures std_span_size(span) == old(std_span_size(span)) - 1u64;
    ensures &result == old(std_span_data(span)) + (old(std_span_size(span)) - 1u64);
}} by {{
    apply(uint64_predecessor_below(std_span_size(span)));
    execute_until(statement(2));
    have size - 1u64 <= std_span_size(span) by {{
        simp() using {{ size == std_span_size(span); std_span_size(span) - 1u64 <= std_span_size(span); }}
    }}
    execute();
    simp();
}}
int32& probe(std::span<int>& span) {{
    owns std_span_data(span);
    owns std_span_size(span);
    requires 1u64 <= std_span_size(span);
    ensures std_span_size(span) == old(std_span_size(span)) - 1u64;
    ensures &result == old(std_span_data(span)) + (old(std_span_size(span)) - 1u64);
}} by {{
    execute();
    simp();
}}
"#
    );
    let sidecar = root.join("span.click");
    fs::write(&sidecar, &source).unwrap();
    let parsed = read_click_project(&sidecar, &source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));

    // Expansion runs against the same contracts, and writes back only the
    // sidecar: the catalog stays Click's.
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        &format!("{pop_back}.contract"),
    )
    .unwrap_or_else(|error| panic!("{}", error.message()));
    assert_ne!(expanded, source);
    assert!(!expanded.contains("extern"), "{expanded}");
    assert!(!expanded.contains("_M_"), "{expanded}");
    verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));

    let refuse = |edited: String, expected: &str| {
        let parsed = read_click_project(&sidecar, &edited).unwrap();
        let error = verify_program_prepared_project(&parsed, &import)
            .expect_err("an unsupported claim must not verify");
        assert!(
            display_source_names(error.message()).contains(expected),
            "{}\n{edited}",
            error.message()
        );
    };
    // Without a nonempty view the proof has no predecessor bound, and the
    // refusal spells the size through its accessor, as the sidecar does.
    refuse(
        source.replacen("    requires 1u64 <= std_span_size(span);\n", "", 1),
        "apply(uint64_predecessor_below(std_span_size(span)))",
    );
    // `first` keeps the data pointer; a moved one is false.
    refuse(
        source.replacen(
            "ensures std_span_data(span) == old(std_span_data(span));",
            "ensures std_span_data(span) == old(std_span_data(span)) + 1u64;",
            1,
        ),
        "ensures",
    );
}

// A standard function without a Click contract is refused by name; nothing
// about it is assumed.
#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn axiomatic_span_refuses_an_uncatalogued_standard_function() {
    let (root, import) = axiomatic_span_fixture(
        "axiomatic-empty",
        "#include <span>\nbool probe(std::span<int>& span) { return span.empty(); }\n",
        &[
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let axiom = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| function.axiom.is_some())
        .unwrap();
    assert_eq!(
        axiom.axiom.as_ref().unwrap().qualified_name,
        "std::span<int>::empty"
    );
    let source = r#"verifying "span-probe.cpp";
bool probe(std::span<int>& span) {
    views std_span_size(span);
    ensures result == result;
} by {
    execute();
    simp();
}
"#;
    let sidecar = root.join("span.click");
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    let spelling = axiom.path.join("::");
    assert!(
        display_source_names(error.message()).contains(&spelling),
        "{}",
        error.message()
    );
}

const SPAN_DEPENDENCIES: &[&str] = &[
    "sysroot/usr/include/c++/12/span",
    "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
];
const BYTE_SPAN_DEPENDENCIES: &[&str] = &[
    "sysroot/usr/include/c++/12/cstddef",
    "sysroot/usr/include/c++/12/span",
    "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
];
const UCHAR_SPAN: &str = "std::span<unsigned char>";

/// One caller of a generic `std::span` catalog entry: the C++ harness, the
/// sidecar that proves it, and edits of that sidecar that must be refused,
/// each with a fragment of the refusal.
struct GenericSpanCase {
    name: &'static str,
    dependencies: &'static [&'static str],
    harness: &'static str,
    sidecar: String,
    refusals: Vec<(String, &'static str)>,
}

/// Verifies each case against the catalog, then expands its proof and
/// checks that the expansion names the span only through model accessors and
/// verifies too, and that each edit is refused.
fn check_generic_span_cases(cases: Vec<GenericSpanCase>) {
    for case in cases {
        let (root, import) = axiomatic_span_fixture(
            case.name,
            &if case.harness.starts_with("#include") {
                format!("{}\n", case.harness)
            } else {
                format!("#include <span>\n{}\n", case.harness)
            },
            case.dependencies,
        );
        let source = format!("verifying \"span-probe.cpp\";\n{}\n", case.sidecar);
        let sidecar = root.join("span.click");
        fs::write(&sidecar, &source).unwrap();
        let parsed = read_click_project(&sidecar, &source).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .unwrap_or_else(|error| panic!("{}: {}\n{source}", case.name, error.message()));
        let expanded = expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "probe.contract",
        )
        .unwrap_or_else(|error| panic!("{}: {}", case.name, error.message()));
        assert!(!expanded.contains("extern"), "{expanded}");
        assert!(!expanded.contains("_M_"), "{expanded}");
        verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
            .unwrap_or_else(|error| panic!("{}: {}\n{expanded}", case.name, error.message()));
        for (edited, expected) in case.refusals {
            assert_ne!(
                edited, case.sidecar,
                "{}: the edit must change the sidecar",
                case.name
            );
            let edited = format!("verifying \"span-probe.cpp\";\n{edited}\n");
            let parsed = read_click_project(&sidecar, &edited).unwrap();
            let error = verify_program_prepared_project(&parsed, &import)
                .expect_err("an unsupported claim must not verify");
            assert!(
                display_source_names(error.message()).contains(expected),
                "{}: {}\n{edited}",
                case.name,
                error.message()
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
}

// `subspan`, `last` and `size_bytes` are catalog entries generic over the
// span's element, so `std::span<unsigned char>` and `std::span<unsigned int>`
// callers verify against the same contracts as `std::span<int>`.
#[test]
#[ignore = "nightly: 4.8s in the parallel gate"]
fn axiomatic_span_subviews_and_byte_size_verify_for_other_elements() {
    let window = format!(
        r#"import click::integer;
theorem uint64_window_bounds(n: uint64) {{
    requires 3u64 <= n;
    ensures 2u64 <= n - 1u64 by {{
        apply(uint64_less_equal_to_integer(3u64, n));
        have to_integer(1u64) <= to_integer(n) by {{
            arithmetic() using {{ to_integer(3u64) <= to_integer(n); }}
        }}
        apply(uint64_subtract_to_integer(n, 1u64));
        have to_integer(2u64) <= to_integer(n - 1u64) by {{
            arithmetic() using {{ to_integer(n - 1u64) == to_integer(n) - 1; to_integer(3u64) <= to_integer(n); }}
        }}
        apply(uint64_to_integer_less_equal_implies_less_equal(2u64, n - 1u64));
    }}
}}
{UCHAR_SPAN} probe({UCHAR_SPAN}& s) {{
    views std_span_data(s);
    views std_span_size(s);
    requires 3u64 <= std_span_size(s);
    ensures std_span_data(result) == std_span_data(s) + 1u64;
    ensures std_span_size(result) == 2u64;
}} by {{
    apply(uint64_window_bounds(std_span_size(s)));
    execute();
    simp();
}}"#
    );
    let last = format!(
        r#"{UCHAR_SPAN} probe({UCHAR_SPAN}& s) {{
    views std_span_data(s);
    views std_span_size(s);
    requires 1u64 <= std_span_size(s);
    ensures std_span_data(result) == std_span_data(s) + (std_span_size(s) - 1u64);
    ensures std_span_size(result) == 1u64;
}} by {{
    execute();
    simp();
}}"#
    );
    let size_bytes = r#"uint64 probe(std::span<unsigned int>& s) {
    views std_span_size(s);
    ensures result == std_span_size(s) * 4u64;
} by {
    execute();
    simp();
}"#
    .to_string();
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "generic-subspan",
            dependencies: SPAN_DEPENDENCIES,
            harness: "std::span<unsigned char> probe(std::span<unsigned char>& s) noexcept { return s.subspan(1, 2); }",
            refusals: vec![
                // Without room for the window, the call's precondition fails,
                // and the refusal names it.
                (
                    window
                        .replace("    requires 3u64 <= std_span_size(s);\n", "")
                        .replace("    apply(uint64_window_bounds(std_span_size(s)));\n", ""),
                    "precondition clause 3 of `std::span<unsigned char>::subspan`",
                ),
                // The window starts at the offset, not at the view's start.
                (
                    window.replace(
                        "ensures std_span_data(result) == std_span_data(s) + 1u64;",
                        "ensures std_span_data(result) == std_span_data(s);",
                    ),
                    "ensures",
                ),
            ],
            sidecar: window,
        },
        GenericSpanCase {
            name: "generic-last",
            dependencies: SPAN_DEPENDENCIES,
            harness: "std::span<unsigned char> probe(std::span<unsigned char>& s) noexcept { return s.last(1); }",
            refusals: vec![(
                last.replace("    requires 1u64 <= std_span_size(s);\n", ""),
                "precondition clause 3 of `std::span<unsigned char>::last`",
            )],
            sidecar: last,
        },
        GenericSpanCase {
            name: "generic-size-bytes",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned long probe(std::span<unsigned int>& s) noexcept { return s.size_bytes(); }",
            // An `unsigned int` is four bytes, not one.
            refusals: vec![(size_bytes.replace("* 4u64", "* 1u64"), "ensures")],
            sidecar: size_bytes,
        },
    ]);
}

// The remaining generic entries for byte-sized elements: `data` and `first`
// on `std::span<unsigned char>`, and a `std::span<std::byte>` subview.
#[test]
#[ignore = "nightly: three more pinned C++ exports"]
fn axiomatic_span_byte_element_entries_verify() {
    let byte_span = "std::span<std::byte>";
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "generic-data",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned char* probe(std::span<unsigned char>& s) noexcept { return s.data(); }",
            sidecar: format!(
                "uint8* probe({UCHAR_SPAN}& s) {{ views std_span_data(s); ensures result == std_span_data(s); }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "generic-first",
            dependencies: SPAN_DEPENDENCIES,
            harness: "std::span<unsigned char> probe(std::span<unsigned char>& s) noexcept { return s.first(1); }",
            sidecar: format!(
                "{UCHAR_SPAN} probe({UCHAR_SPAN}& s) {{ views std_span_data(s); views std_span_size(s); requires 1u64 <= std_span_size(s); ensures std_span_data(result) == std_span_data(s); ensures std_span_size(result) == 1u64; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "generic-byte-window",
            dependencies: BYTE_SPAN_DEPENDENCIES,
            harness: "std::span<std::byte> probe(std::span<std::byte>& s) noexcept { return s.subspan(1, std::dynamic_extent); }",
            sidecar: format!(
                r#"{byte_span} probe({byte_span}& s) {{
    views std_span_data(s);
    views std_span_size(s);
    requires 1u64 <= std_span_size(s);
    ensures std_span_data(result) == std_span_data(s) + 1u64;
    ensures std_span_size(result) == std_span_size(s) - 1u64;
}} by {{ execute(); simp(); }}"#
            ),
            refusals: vec![],
        },
    ]);
}

const UINT_SPAN: &str = "std::span<unsigned int>";

// A returned element reference is read and written directly, as in
// `return s[0];` and `s[0] = v;`, for element types other than `int`. The
// read needs a view of the element and the write needs to own it; the span
// contracts grant neither.
#[test]
#[ignore = "nightly: 8.5s in the parallel gate"]
fn axiomatic_span_element_references_read_and_write() {
    let read = format!(
        r#"uint8 probe({UCHAR_SPAN}& s) {{
    views std_span_data(s);
    views std_span_size(s);
    views std_span_data(s)[0];
    requires 1u64 <= std_span_size(s);
    ensures result == std_span_data(s)[0];
}} by {{
    execute();
    simp();
}}"#
    );
    let write = format!(
        r#"void probe({UCHAR_SPAN}& s, uint8 v) {{
    views std_span_data(s);
    views std_span_size(s);
    owns std_span_data(s)[1];
    requires 2u64 <= std_span_size(s);
    requires separate(memory(std_span_data(s)[1]), memory(std_span_data(s)));
    requires separate(memory(std_span_data(s)[1]), memory(std_span_size(s)));
    ensures std_span_data(s)[1] == v;
    ensures result == v;
}} by {{
    execute();
    simp();
}}"#
    )
    .replace("void probe", "uint8 probe");
    let back = format!(
        r#"uint32 probe({UINT_SPAN}& s) {{
    views std_span_data(s);
    views std_span_size(s);
    views std_span_data(s)[std_span_size(s) - 1u64];
    requires 1u64 <= std_span_size(s);
    ensures result == std_span_data(s)[std_span_size(s) - 1u64];
}} by {{
    execute();
    simp();
}}"#
    );
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "element-read",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned char probe(std::span<unsigned char>& s) noexcept { return s[0]; }",
            refusals: vec![
                // The read needs permission for the element itself.
                (
                    read.replace("    views std_span_data(s)[0];\n", ""),
                    "missing resource fact `views",
                ),
                // `s[0]` reads the first element, not the second.
                (
                    read.replace(
                        "ensures result == std_span_data(s)[0];",
                        "ensures result == std_span_data(s)[1];",
                    ),
                    "ensures",
                ),
            ],
            sidecar: read,
        },
        GenericSpanCase {
            name: "element-write",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned char probe(std::span<unsigned char>& s, unsigned char v) noexcept { s[1] = v; return s[1]; }",
            // A view of the element does not permit the write.
            refusals: vec![(
                write.replace("owns std_span_data(s)[1];", "views std_span_data(s)[1];"),
                "missing resource fact `owns",
            )],
            sidecar: write,
        },
        GenericSpanCase {
            name: "element-back",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned int probe(std::span<unsigned int>& s) noexcept { return s.back(); }",
            refusals: vec![(
                back.replace("    requires 1u64 <= std_span_size(s);\n", ""),
                "precondition clause 3 of `std::span<unsigned int>::back`",
            )],
            sidecar: back,
        },
    ]);
}

// Returning an element reference, and `int` element reads and writes, which
// the profile previously admitted only through a reference local.
#[test]
#[ignore = "nightly: three more pinned C++ exports"]
fn axiomatic_span_element_reference_returns_and_int_access() {
    let int_span = "std::span<int>";
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "element-reference",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned char& probe(std::span<unsigned char>& s) noexcept { return s[1]; }",
            sidecar: format!(
                "uint8& probe({UCHAR_SPAN}& s) {{ views std_span_data(s); views std_span_size(s); requires 2u64 <= std_span_size(s); ensures &result == std_span_data(s) + 1u64; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "int-element-read",
            dependencies: SPAN_DEPENDENCIES,
            harness: "int probe(std::span<int>& s) noexcept { return s[0]; }",
            sidecar: format!(
                "int32 probe({int_span}& s) {{ views std_span_data(s); views std_span_size(s); views std_span_data(s)[0]; requires 1u64 <= std_span_size(s); ensures result == std_span_data(s)[0]; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "int-element-write",
            dependencies: SPAN_DEPENDENCIES,
            harness: "void probe(std::span<int>& s, int v) noexcept { s[0] = v; }",
            sidecar: format!(
                "void probe({int_span}& s, int32 v) {{ views std_span_data(s); views std_span_size(s); owns std_span_data(s)[0]; requires 1u64 <= std_span_size(s); requires separate(memory(std_span_data(s)[0]), memory(std_span_data(s))); requires separate(memory(std_span_data(s)[0]), memory(std_span_size(s))); ensures std_span_data(s)[0] == v; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
    ]);
}

const ARRAY_DEPENDENCIES: &[&str] = &[
    "sysroot/usr/include/c++/12/array",
    "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
];
const CONST_INT_SPAN: &str = "std::span<const int>";
const STATIC_INT_SPAN: &str = "std::span<int, 4>";
const INT_ARRAY: &str = "std::array<int, 4>";

/// Imports `harness` and checks that `sidecar` is refused with `expected`:
/// the claim is about a program the catalog contracts do not admit.
fn check_refused_span_case(
    name: &str,
    dependencies: &[&str],
    harness: &str,
    sidecar: &str,
    expected: &str,
) {
    let (root, import) = axiomatic_span_fixture(name, harness, dependencies);
    let source = format!("verifying \"span-probe.cpp\";\n{sidecar}\n");
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let parsed = read_click_project(&path, &source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("an unsupported claim must not verify");
    assert!(
        display_source_names(error.message()).contains(expected),
        "{name}: {}\n{source}",
        error.message()
    );
    fs::remove_dir_all(root).unwrap();
}

// `std::span<const T>` names its const element in the record, holds a
// `const T*`, and uses the same generic entries with const element types.
#[test]
#[ignore = "nightly: 6.2s in the parallel gate"]
fn axiomatic_const_element_spans_verify() {
    let read = r#"uint8 probe(std::span<const unsigned char>& s) {
    views std_span_data(s);
    views std_span_size(s);
    views std_span_data(s)[0];
    requires 1u64 <= std_span_size(s);
    ensures result == std_span_data(s)[0];
} by {
    execute();
    simp();
}"#
    .to_string();
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "const-element-read",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned char probe(std::span<const unsigned char>& s) noexcept { return s[0]; }",
            refusals: vec![(
                read.replace("    views std_span_data(s)[0];\n", ""),
                "missing resource fact `views",
            )],
            sidecar: read,
        },
        GenericSpanCase {
            name: "const-element-data",
            dependencies: SPAN_DEPENDENCIES,
            harness: "const int* probe(std::span<const int>& s) noexcept { return s.data(); }",
            sidecar: format!(
                "const int32* probe({CONST_INT_SPAN}& s) {{ views std_span_data(s); ensures result == std_span_data(s); }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
    ]);
}

#[test]
#[ignore = "nightly: three more pinned C++ exports"]
fn axiomatic_const_element_span_subviews_verify() {
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "const-element-size-bytes",
            dependencies: SPAN_DEPENDENCIES,
            harness: "unsigned long probe(std::span<const int>& s) noexcept { return s.size_bytes(); }",
            sidecar: format!(
                "uint64 probe({CONST_INT_SPAN}& s) {{ views std_span_size(s); ensures result == std_span_size(s) * 4u64; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "const-element-first",
            dependencies: SPAN_DEPENDENCIES,
            harness: "std::span<const int> probe(std::span<const int>& s) noexcept { return s.first(1); }",
            sidecar: format!(
                "{CONST_INT_SPAN} probe({CONST_INT_SPAN}& s) {{ views std_span_data(s); views std_span_size(s); requires 1u64 <= std_span_size(s); ensures std_span_data(result) == std_span_data(s); ensures std_span_size(result) == 1u64; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "const-element-back",
            dependencies: SPAN_DEPENDENCIES,
            harness: "const int& probe(std::span<const int>& s) noexcept { return s.back(); }",
            sidecar: format!(
                "const int32& probe({CONST_INT_SPAN}& s) {{ views std_span_data(s); views std_span_size(s); requires 1u64 <= std_span_size(s); ensures &result == std_span_data(s) + (std_span_size(s) - 1u64); }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
    ]);
}

// A static-extent span keeps its extent in the type: libstdc++'s extent
// member is stateless, so the record holds only the data pointer, and the
// contracts state the size as the literal `N`.
#[test]
#[ignore = "nightly: 2.5s in the parallel gate"]
fn axiomatic_static_extent_spans_verify() {
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "static-extent-read",
            dependencies: SPAN_DEPENDENCIES,
            harness: "int probe(std::span<int, 4>& s) noexcept { return s[3]; }",
            sidecar: format!(
                "int32 probe({STATIC_INT_SPAN}& s) {{ views std_span_data(s); views std_span_data(s)[3]; ensures result == std_span_data(s)[3]; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "static-extent-size-bytes",
            dependencies: &["sysroot/usr/include/c++/12/span"],
            harness: "unsigned long probe(std::span<const unsigned char, 32>& s) noexcept { return s.size_bytes(); }",
            sidecar: "uint64 probe(std::span<const unsigned char, 32>& s) { ensures result == 32u64; } by { execute(); simp(); }".into(),
            refusals: vec![(
                "uint64 probe(std::span<const unsigned char, 32>& s) { ensures result == 33u64; } by { execute(); simp(); }".into(),
                "ensures",
            )],
        },
    ]);
    // The fifth element of a four-element span is outside the view.
    check_refused_span_case(
        "static-extent-out-of-bounds",
        SPAN_DEPENDENCIES,
        "#include <span>\nint probe(std::span<int, 4>& s) noexcept { return s[4]; }\n",
        &format!(
            "int32 probe({STATIC_INT_SPAN}& s) {{ views std_span_data(s); views std_span_data(s)[4]; ensures result == std_span_data(s)[4]; }} by {{ execute(); simp(); }}"
        ),
        "::operator[]",
    );
}

#[test]
#[ignore = "nightly: a static-extent subview export"]
fn axiomatic_static_extent_span_subviews_verify() {
    check_generic_span_cases(vec![GenericSpanCase {
        name: "static-extent-first",
        dependencies: SPAN_DEPENDENCIES,
        harness: "std::span<int> probe(std::span<int, 4>& s) noexcept { return s.first(2); }",
        sidecar: format!(
            "{} probe({STATIC_INT_SPAN}& s) {{ views std_span_data(s); ensures std_span_data(result) == std_span_data(s); ensures std_span_size(result) == 2u64; }} by {{ execute(); simp(); }}",
            "std::span<int>"
        ),
        refusals: vec![],
    }]);
}

// A defaulted argument is the constant Clang evaluates for it: `subspan(1)`
// passes `std::dynamic_extent` as its count, and verifies as a subview to
// the end.
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn defaulted_span_arguments_import_as_compiler_constants() {
    let (root, import) = axiomatic_span_fixture(
        "default-argument",
        "#include <span>\nstd::span<int> probe(std::span<int>& s) noexcept { return s.subspan(1); }\n",
        SPAN_DEPENDENCIES,
    );
    let body = serde_json::to_value(&import.export().functions[0].body).unwrap();
    let arguments = &body[0]["arguments"];
    assert_eq!(arguments[2]["value"]["kind"], "compiler_constant", "{body}");
    assert_eq!(
        arguments[2]["value"]["value"], "18446744073709551615",
        "{body}"
    );
    // The defaulted count runs to the end of the view.
    let span = "std::span<int>";
    let source = format!(
        "verifying \"span-probe.cpp\";\n{span} probe({span}& s) {{ views std_span_data(s); views std_span_size(s); requires 1u64 <= std_span_size(s); ensures std_span_data(result) == std_span_data(s) + 1u64; ensures std_span_size(result) == std_span_size(s) - 1u64; }} by {{ execute(); simp(); }}\n"
    );
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let parsed = read_click_project(&path, &source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
    fs::remove_dir_all(root).unwrap();
}

// `std::array<T, N>` holds its elements inline, named by
// `std_array_data(a)`. Its element accessors have const and mutable
// overloads; a read needs a view of the array and a write needs to own it.
#[test]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn axiomatic_std_array_element_access_verifies() {
    let write = format!(
        r#"int32 probe({INT_ARRAY}& a, int32 v) {{
    owns a;
    ensures std_array_data(a)[3] == v;
    ensures std_array_data(a)[0] == old(std_array_data(a)[0]);
    ensures result == v;
}} by {{
    execute();
    simp();
}}"#
    );
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "array-element-read",
            dependencies: ARRAY_DEPENDENCIES,
            harness: "#include <array>\nint probe(std::array<int, 4>& a) noexcept { return a[1]; }",
            sidecar: format!(
                "int32 probe({INT_ARRAY}& a) {{ views a; ensures result == std_array_data(a)[1]; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![(
                format!(
                    "int32 probe({INT_ARRAY}& a) {{ views a; ensures result == std_array_data(a)[2]; }} by {{ execute(); simp(); }}"
                ),
                "ensures",
            )],
        },
        GenericSpanCase {
            name: "array-element-write",
            dependencies: ARRAY_DEPENDENCIES,
            harness: "#include <array>\nint probe(std::array<int, 4>& a, int v) noexcept { a[3] = v; return a.back(); }",
            refusals: vec![(
                write.replace("owns a;", "views a;"),
                "missing resource fact `owns",
            )],
            sidecar: write,
        },
    ]);
    check_refused_span_case(
        "array-out-of-bounds",
        ARRAY_DEPENDENCIES,
        "#include <array>\nint probe(std::array<int, 4>& a) noexcept { return a[4]; }\n",
        &format!(
            "int32 probe({INT_ARRAY}& a) {{ views a; ensures result == 0; }} by {{ execute(); simp(); }}"
        ),
        "::operator[]",
    );
}

#[test]
fn axiomatic_std_array_reference_element_resources_verify() {
    for (name, harness, return_type, parameters, postcondition, clauses, refusals) in [
        (
            "array-reference-element-read",
            "#include <array>\nint probe(std::array<int, 4>& a) noexcept { return a[1]; }\n",
            "int32",
            format!("{INT_ARRAY}& a"),
            "result == std_array_data(a)[1]",
            vec!["views a._M_elems[1];", "views std_array_data(a)[1];"],
            vec!["views std_array_data(a)[2];"],
        ),
        (
            "array-reference-element-write",
            "#include <array>\nint probe(std::array<int, 4>& a, int v) noexcept { a[1] = v; return a[1]; }\n",
            "int32",
            format!("{INT_ARRAY}& a, int32 v"),
            "result == v and std_array_data(a)[1] == v",
            vec!["owns std_array_data(a)[1];"],
            vec!["views std_array_data(a)[1];", "owns std_array_data(a)[0];"],
        ),
        (
            "array-reference-byte-element-write",
            "#include <array>\nunsigned char probe(std::array<unsigned char, 4>& a, unsigned char v) noexcept { a[1] = v; return a[1]; }\n",
            "uint8",
            "std::array<unsigned char, 4>& a, uint8 v".into(),
            "result == v and std_array_data(a)[1] == v",
            vec!["owns std_array_data(a)[1];"],
            vec!["views std_array_data(a)[1];", "owns std_array_data(a)[0];"],
        ),
    ] {
        let (root, import) = axiomatic_span_fixture(name, harness, ARRAY_DEPENDENCIES);
        let path = root.join("span.click");
        let source_for = |clause: &str| {
            format!(
                "verifying \"span-probe.cpp\"; {return_type} probe({parameters}) {{ {clause} ensures {postcondition}; }} by {{ execute(); simp(); }}"
            )
        };
        for clause in clauses {
            let source = source_for(clause);
            fs::write(&path, &source).unwrap();
            let parsed = read_click_project(&path, &source).unwrap();
            let verified = verify_program_prepared_project(&parsed, &import)
                .unwrap_or_else(|error| panic!("{name}: {}\n{source}", error.message()));
            let expanded = click::surface::expand_verified_function_claim_source_by_label(
                &source,
                &verified,
                "probe.contract",
            )
            .unwrap()
            .expect("the verified probe claim is declared in this source");
            verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
                .unwrap_or_else(|error| panic!("{name}: {}\n{expanded}", error.message()));
        }
        for clause in refusals {
            let source = source_for(clause);
            let parsed = read_click_project(&path, &source).unwrap();
            let error = verify_program_prepared_project(&parsed, &import)
                .expect_err("a different element or a view cannot authorize the access");
            let report = error.concise_report();
            assert!(!report.contains("type mismatch"), "{report}");
            assert!(!report.contains("*&a["), "{report}");
            if name.ends_with("write") {
                assert!(report.contains("owns"), "{report}");
            }
        }
        if name == "array-reference-element-read" {
            let source = source_for("views a._M_elems[2147483647 + 1];");
            let parsed = read_click_project(&path, &source).unwrap();
            let error = verify_program_prepared_project(&parsed, &import)
                .expect_err("overflowing element arithmetic must be refused");
            let report = error.concise_report();
            assert!(report.contains("segment std_array_data(a)["), "{report}");
            assert!(!report.contains("*&a["), "{report}");
        }
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
#[ignore = "nightly: two more pinned C++ exports"]
fn axiomatic_std_array_size_and_data_verify() {
    check_generic_span_cases(vec![
        GenericSpanCase {
            name: "array-size",
            dependencies: &["sysroot/usr/include/c++/12/array"],
            harness: "#include <array>\nunsigned long probe(std::array<unsigned char, 32>& a) noexcept { return a.size(); }",
            sidecar: "uint64 probe(std::array<unsigned char, 32>& a) { ensures result == 32u64; } by { execute(); simp(); }".into(),
            refusals: vec![],
        },
        GenericSpanCase {
            name: "array-data",
            dependencies: &["sysroot/usr/include/c++/12/array"],
            harness: "#include <array>\nint* probe(std::array<int, 4>& a) noexcept { return a.data(); }",
            sidecar: format!(
                "int32* probe({INT_ARRAY}& a) {{ ensures result == &std_array_data(a)[0]; }} by {{ execute(); simp(); }}"
            ),
            refusals: vec![],
        },
    ]);
}

// A caller writes through the reference `SpanPopBack` returns. The write
// needs ownership of that backing cell, which the span's contracts neither
// grant nor need; the descriptor itself is all `back` and `first` read.
#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn axiomatic_span_pop_back_write_needs_backing_ownership() {
    let (root, import) = axiomatic_span_fixture(
        "axiomatic-pop-back-write",
        "#include <span.h>\nint probe(std::span<int>& span, int input) { int& back = SpanPopBack(span); back = input; return back; }\n",
        &[
            "bitcoin-src/src/span.h",
            "sysroot/usr/include/c++/12/span",
            "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
        ],
    );
    let pop_back = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| function.name.starts_with("SpanPopBack"))
        .unwrap()
        .path
        .join("::");
    let source = format!(
        r#"import click::integer;
verifying "span-probe.cpp";
theorem uint64_predecessor_below(n: uint64) {{
    requires 1u64 <= n;
    ensures n - 1u64 <= n by {{
        apply(uint64_less_equal_to_integer(1u64, n));
        apply(uint64_subtract_to_integer(n, 1u64));
        have to_integer(n - 1u64) <= to_integer(n) by {{
            arithmetic() using {{ to_integer(n - 1u64) == to_integer(n) - 1; }}
        }}
        apply(uint64_to_integer_less_equal_implies_less_equal(n - 1u64, n));
    }}
}}
int32& {pop_back}(std::span<int>& span) {{
    owns std_span_data(span);
    owns std_span_size(span);
    requires 1u64 <= std_span_size(span);
    ensures std_span_data(span) == old(std_span_data(span));
    ensures std_span_size(span) == old(std_span_size(span)) - 1u64;
    ensures &result == old(std_span_data(span)) + (old(std_span_size(span)) - 1u64);
}} by {{
    apply(uint64_predecessor_below(std_span_size(span)));
    execute_until(statement(2));
    have size - 1u64 <= std_span_size(span) by {{
        simp() using {{ size == std_span_size(span); std_span_size(span) - 1u64 <= std_span_size(span); }}
    }}
    execute();
    simp();
}}
int32 probe(std::span<int>& span, int32 input) {{
    owns std_span_data(span);
    owns std_span_size(span);
    owns std_span_data(span)[std_span_size(span) - 1u64];
    requires 1u64 <= std_span_size(span);
    requires separate(memory(std_span_data(span)), memory(std_span_data(span)[std_span_size(span) - 1u64]));
    requires separate(memory(std_span_size(span)), memory(std_span_data(span)[std_span_size(span) - 1u64]));
    ensures result == input;
}} by {{
    execute();
    simp();
}}
"#
    );
    let sidecar = root.join("span.click");
    fs::write(&sidecar, &source).unwrap();
    let parsed = read_click_project(&sidecar, &source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
    let unowned = source.replacen(
        "    owns std_span_data(span)[std_span_size(span) - 1u64];\n",
        "",
        1,
    );
    let parsed = read_click_project(&sidecar, &unowned).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("a write through the returned reference needs its cell");
}

// Actual std::byte pointers retain native one-byte strides, checked nominal
// identities and ordinary ownership across offline verification and expansion.
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn pinned_std_byte_pointer_stores_verify_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-pointer",
        "#include <span.h>\nstd::byte probe(std::byte* p, std::byte value) noexcept { *(p + 1) = value; return *(p + 1); }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let source = "verifying \"span-probe.cpp\"; uint8 probe(uint8* p, uint8 value) { owns p[0..2]; ensures p[1] == value; ensures p[0] == old(p[0]); ensures result == value; } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
    let bad = source.replace("owns p[0..2]", "views p[0..2]");
    fs::write(root.join("bad.click"), &bad).unwrap();
    assert!(
        verify_program_prepared_project(
            &read_click_project(&root.join("bad.click"), &bad).unwrap(),
            &import
        )
        .is_err()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn pinned_std_byte_automatic_pointer_store_initializes_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-address",
        "#include <span.h>\nstd::byte probe(std::byte value) noexcept { std::byte obj; *(&obj) = value; return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
    );
    fs::remove_dir_all(root).unwrap();
}

fn check_pinned_byte_proof(root: &Path, import: &PreparedCppImport, source: &str) {
    fs::write(root.join("byte.click"), source).unwrap();
    let project = read_click_project(&root.join("byte.click"), source).unwrap();
    verify_program_prepared_project(&project, import).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::program(import),
        "probe.contract",
    )
    .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, import).unwrap();
    let position = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(import),
        "probe.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
}

#[test]
// Consistent rehashing cannot substitute another nominal enum or move its
// declaration to another locked source to manufacture byte alias privilege.
fn pinned_std_byte_pointer_artifacts_reject_forged_declarations_offline() {
    let (root, _) = pinned_span_fixture_with_exact_dependencies(
        "byte-pointer-forgery",
        "#include <span.h>\nstd::byte probe(std::byte* p) noexcept { return *p; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let artifact_path = cpp_description::artifact(&root.join("span.import-description.json"));
    let lock_path = root.join(click::project::LOCK_NAME);
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(&artifact_path).unwrap()).unwrap();
    let lock: serde_json::Value = serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    fn change_enums(value: &mut serde_json::Value, change: usize) {
        match value {
            serde_json::Value::Object(object) => {
                if object.get("kind").and_then(|v| v.as_str()) == Some("enumeration") {
                    match change {
                        0 => {
                            object.insert("name".into(), "Other".into());
                            object.insert("declaration_id".into(), "c:@E@Other".into());
                        }
                        1 => {
                            object.get_mut("span").unwrap()["file"] = "span-probe.cpp".into();
                        }
                        2 => {
                            object.get_mut("span").unwrap()["start_line"] = 70.into();
                        }
                        3 => {
                            object.get_mut("underlying_type").unwrap()["signed"] = true.into();
                        }
                        _ => unreachable!(),
                    }
                }
                for child in object.values_mut() {
                    change_enums(child, change);
                }
            }
            serde_json::Value::Array(values) => {
                for child in values {
                    change_enums(child, change);
                }
            }
            _ => {}
        }
    }
    for change in 0..5 {
        let mut forged = artifact.clone();
        if change == 4 {
            forged["preprocessor_files"]
                .as_array_mut()
                .unwrap()
                .retain(|file| {
                    !file["canonical_path"]
                        .as_str()
                        .unwrap()
                        .ends_with("/cstddef")
                });
        } else {
            change_enums(&mut forged, change);
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] = sha256(&bytes).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(&artifact_path, bytes).unwrap();
        fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
        assert!(
            load_import(&root.join("span.import-description.json")).is_err(),
            "mutation {change}"
        );
    }
    // A self-consistent dependency digest still cannot replace the standard
    // header pin. Keep the declaration spelling and span unchanged.
    let header = "sysroot/usr/include/c++/12/cstddef";
    let mut header_bytes = fs::read(root.join(header)).unwrap();
    header_bytes.extend_from_slice(b"\n// substituted standard header\n");
    fs::write(root.join(header), &header_bytes).unwrap();
    let mut forged_lock = lock;
    lock_section_mut(&mut forged_lock)["dependencies"][header] = sha256(&header_bytes).into();
    fs::write(
        &artifact_path,
        serde_json::to_vec_pretty(&artifact).unwrap(),
    )
    .unwrap();
    // Preserve the original artifact bytes hashed by the lock, rather than
    // relying on JSON formatting to round-trip byte-for-byte.
    let restored = fs::read(&artifact_path).unwrap();
    lock_source_mut(&mut forged_lock)["artifact"]["sha256"] = sha256(&restored).into();
    lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = restored.len().into();
    fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
    let error = load_import(&root.join("span.import-description.json")).unwrap_err();
    assert!(
        error.contains("std::byte declaration header differs"),
        "{error}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
// Allocated enum scalars can lend their exact byte owner to an ordinary helper;
// the returned contract value must refresh the caller binding.
fn pinned_std_byte_modular_pointer_call_verifies_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-pointer-call",
        "#include <span.h>\nvoid fill(std::byte* p, std::byte value) noexcept { *p = value; } std::byte probe(std::byte value) noexcept { std::byte obj = static_cast<std::byte>(0); fill(&obj, value); return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; void fill(uint8* p, uint8 value) { owns p[0..1]; ensures p[0] == value; } by { execute(); simp(); } uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
// Pointer reinterpretation supplies no initialization. Four concrete byte
// stores complete the shared uint32 representation on the selected LE target.
fn pinned_std_byte_reinterpretation_initializes_uint32_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-word",
        "#include <span.h>\nunsigned int probe() noexcept { unsigned int obj; std::byte* p = reinterpret_cast<std::byte*>(&obj); *p = static_cast<std::byte>(120); *(p + 1) = static_cast<std::byte>(86); *(p + 2) = static_cast<std::byte>(52); *(p + 3) = static_cast<std::byte>(18); return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; uint32 probe() { ensures result == 305419896u32; } by { execute(); simp(); }",
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn pinned_std_byte_reinterpreted_call_result_preserves_pointer_identity_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-call",
        "#include <span.h>\nunsigned int* echo(unsigned int* p) noexcept { return p; } std::byte* probe(unsigned int* p) noexcept { return reinterpret_cast<std::byte*>(echo(p)); }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; uint32* echo(uint32* p) { ensures result == p; } by { execute(); simp(); } uint8* probe(uint32* p) { ensures result == (uint8*)p; } by { execute(); simp(); }",
    );
    let artifact_path = cpp_description::artifact(&root.join("span.import-description.json"));
    let lock_path = root.join(click::project::LOCK_NAME);
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(&artifact_path).unwrap()).unwrap();
    let lock: serde_json::Value = serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    for change in 0..4 {
        let mut forged = artifact.clone();
        let conversion = &mut forged["functions"][0]["body"][0]["conversions"][0];
        match change {
            0 => conversion["cast_kind"] = "no_op".into(),
            1 => conversion["explicit"] = false.into(),
            2 => conversion["source_type"]["pointee"]["bits"] = 64.into(),
            3 => {
                conversion["value_type"]["pointee"]["name"] = "Other".into();
                conversion["value_type"]["pointee"]["declaration_id"] = "c:@E@Other".into();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] = sha256(&bytes).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(&artifact_path, bytes).unwrap();
        fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
        assert!(
            load_import(&root.join("span.import-description.json")).is_err(),
            "mutation {change}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn pinned_std_byte_reinterpretation_does_not_initialize_partial_storage() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-partial",
        "#include <span.h>\nunsigned int probe() noexcept { unsigned int obj; std::byte* p = reinterpret_cast<std::byte*>(&obj); *p = static_cast<std::byte>(120); return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let source = "verifying \"span-probe.cpp\"; uint32 probe() { ensures result == 120u32; } by { execute(); simp(); }";
    fs::write(root.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(
        &read_click_project(&root.join("bad.click"), source).unwrap(),
        &import,
    )
    .unwrap_err();
    assert!(
        error.message().contains("uninitialized"),
        "{}",
        error.message()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
// Changing the access type cannot mint write permission over the original word.
fn pinned_std_byte_reinterpretation_requires_original_storage_ownership() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-authority",
        "#include <span.h>\nunsigned char probe(unsigned int* p) noexcept { std::byte* bytes = reinterpret_cast<std::byte*>(p); *bytes = static_cast<std::byte>(7); return static_cast<unsigned char>(*bytes); }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let source = "verifying \"span-probe.cpp\"; uint8 probe(uint32* p) { owns p[0..1]; ensures result == 7u8; } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
    for bad in [
        source.replace("owns p[0..1];", "views p[0..1];"),
        source.replace("owns p[0..1];", ""),
    ] {
        fs::write(root.join("bad.click"), &bad).unwrap();
        assert!(
            verify_program_prepared_project(
                &read_click_project(&root.join("bad.click"), &bad).unwrap(),
                &import
            )
            .is_err()
        );
    }
    fs::remove_dir_all(root).unwrap();
}
