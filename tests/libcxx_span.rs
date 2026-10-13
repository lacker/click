//! Click's C++ standard-library catalog against a pinned libc++ closure.
//! The proofs are the ones that verify against libstdc++; only the parsed
//! library differs, and its layout binds the same model accessors.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use click::cli::read_click_project;
use click::languages::cpp::{PreparedCppImport, load_import, refresh_import};
use click::surface::{
    ProgramInputs, expand_project_claim_source_by_label, verify_program_prepared_project,
};

#[path = "support/pinned_clang.rs"]
mod pinned_clang;
use pinned_clang::{output, pinned_clang, sha256};

const ARCHIVE: &[u8] = include_bytes!("fixtures/libcxx-span/input-closure.tar.gz");
const SPAN: &str = "struct span__int__value_unsigned_long_18446744073709551615";

/// Imports `probe` from `harness`, compiled against the pinned libc++.
fn libcxx_fixture(
    name: &str,
    harness: &str,
    dependencies: &[&str],
) -> (PathBuf, PreparedCppImport) {
    assert_eq!(
        sha256(ARCHIVE),
        "eeae6f54e4e25a8a58a5ad503640a9042ff14ee0c15300e7807573e757bdd086"
    );
    let root = std::env::temp_dir().join(format!("click-libcxx-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
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
    assert_eq!(
        sha256(&fs::read(root.join("libcxx/include/c++/v1/span")).unwrap()),
        "b8b350b8a4992602c184694bee10ac1dc4a7e9412a02988c9e6466972195ba10"
    );
    fs::write(root.join("span-probe.cpp"), harness).unwrap();
    let clang = pinned_clang();
    let r = root.to_str().unwrap();
    let command = format!(
        "{} --target=x86_64-unknown-linux-gnu --sysroot={r}/sysroot -resource-dir={} -nostdinc++ \
         -isystem {r}/libcxx/include/x86_64-unknown-linux-gnu/c++/v1 -isystem {r}/libcxx/include/c++/v1 \
         -std=c++20 -c {r}/span-probe.cpp",
        clang.display(),
        output(&clang, &["-print-resource-dir"])
    );
    let database = serde_json::json!([{ "directory": r, "command": command, "file": format!("{r}/span-probe.cpp") }]);
    fs::write(
        root.join("compile_commands.json"),
        serde_json::to_vec_pretty(&database).unwrap(),
    )
    .unwrap();
    let exporter = root.join("click-cpp-exporter");
    fs::copy(std::env::var("CLICK_CPP_EXPORTER").unwrap(), &exporter).unwrap();
    let config = serde_json::json!({
        "schema": 6, "language": "c++", "standard": "c++20", "target": "x86_64-unknown-linux-gnu",
        "exceptions": true, "rtti": true, "exporter": exporter,
        "compilation_database": "compile_commands.json", "working_directory": ".",
        "source": "span-probe.cpp", "logical_source": "span-probe.cpp",
        "dependencies": dependencies,
        "function": "probe", "artifact": "span.click-cpp.json"
    });
    let config_path = root.join("span.click.import.json");
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    refresh_import(&config_path).unwrap();
    fs::remove_file(exporter).unwrap();
    let import = load_import(&config_path).unwrap();
    (root, import)
}

/// Verifies `sidecar`, then its expansion, which must name the span only
/// through model accessors, and refuses each edit with its fragment.
fn check(root: &Path, import: &PreparedCppImport, sidecar: &str, refusals: &[(String, &str)]) {
    let source = format!("verifying \"span-probe.cpp\";\n{sidecar}\n");
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let parsed = read_click_project(&path, &source).unwrap();
    verify_program_prepared_project(&parsed, import)
        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(import),
        "probe.contract",
    )
    .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(
        !expanded.contains("__data_") && !expanded.contains("__size_"),
        "{expanded}"
    );
    verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), import)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    for (edited, expected) in refusals {
        let edited = format!("verifying \"span-probe.cpp\";\n{edited}\n");
        let parsed = read_click_project(&path, &edited).unwrap();
        let error = verify_program_prepared_project(&parsed, import)
            .expect_err("an unsupported claim must not verify");
        assert!(
            error.message().contains(expected),
            "{}\n{edited}",
            error.message()
        );
    }
}

// libc++'s dynamic-extent span holds `__data_` and `__size_`. The accessors
// bind to them, so the libstdc++ proof of an element read verifies
// unchanged, and its expansion names no libc++ field.
#[test]
fn libcxx_span_binds_the_model_accessors_and_catalog() {
    let (root, import) = libcxx_fixture(
        "element-read",
        "#include <span>\nint probe(std::span<int>& s) noexcept { return s[1]; }\n",
        &["libcxx/include/c++/v1/span"],
    );
    let span = import
        .export()
        .records
        .iter()
        .find(|record| format!("struct {}", record.name) == SPAN)
        .unwrap();
    assert_eq!(
        span.fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        ["__data_", "__size_"]
    );
    let sidecar = format!(
        "int32 probe({SPAN}& s) {{
    views std_span_data(s);
    views std_span_size(s);
    views std_span_data(s)[1];
    requires 2u64 <= std_span_size(s);
    ensures result == std_span_data(s)[1];
}} by {{
    execute();
    simp();
}}"
    );
    check(
        &root,
        &import,
        &sidecar,
        &[(
            sidecar.replace("    requires 2u64 <= std_span_size(s);\n", ""),
            "operator_index",
        )],
    );
    fs::remove_dir_all(root).unwrap();
}
