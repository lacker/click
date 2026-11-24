// Scaling tests of `src/bin/click-audit/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// A site cap covering the whole claim must not re-run it for each site.
#[test]
#[ignore = "nightly: partial audit scaling stays outside the verification gate"]
fn partial_claim_audit_runs_once_after_a_fixed_prefix() {
    let directory = std::env::temp_dir().join(format!(
        "click-audit-partial-scaling-{}",
        std::process::id()
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(
        directory.join("unit.c"),
        "int32 identity(int32 x) { return x; }",
    )
    .unwrap();
    let path = directory.join("unit.click");
    let samples = [4, 8, 16, 32].map(|size| {
        let source = format!("verifying \"unit.c\";\nint32 identity(int32 x) {{ ensures result == x; }} by {{\nstep_until(function.exit);\n{}{}close();\n}}\n", "have x + 0 == x by close();\n".repeat(8), "have x == x by close();\n".repeat(size));
        fs::write(&path, source).unwrap();
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        let start = &sites[9];
        let arguments = parse_arguments([
            "--start-at".to_string(), format!("{}:{}:{}", path.display(), start.click_position.line, start.click_position.column),
            "--max-sites".to_string(), size.to_string(), path.display().to_string(),
        ]).unwrap();
        let (result, work) = click::instrumentation::measure_deterministic_work(|| run_audit(arguments));
        result.unwrap();
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] * 4 <= pair[0] * 9,
            "partial audit scaling: {samples:?}"
        );
    }
    let markdown = directory.join("unit.md");
    fs::write(&markdown, "# Partial selection in a container\n\n```c filename=unit.c\nint32 identity(int32 x) { return x; }\n```\n\n```click\nverifying \"unit.c\";\nint32 identity(int32 x) { ensures result == x; } by {\nstep_until(function.exit);\nhave x == x by close();\nhave x + 0 == x by close();\nclose();\n}\n```\n\n```expect\npass\n```\n").unwrap();
    let sites = inventory_sites(std::slice::from_ref(&markdown)).unwrap();
    let arguments = parse_arguments([
        "--start-at".to_string(),
        format_location(&site_location(&sites[1])),
        "--max-sites".to_string(),
        "2".to_string(),
        markdown.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).expect("container coordinates select the same two Click occurrences");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
#[ignore = "nightly: audit scaling stays outside the verification gate"]
fn bounded_whole_claim_audit_matches_uncapped_work_at_every_size() {
    let directory = std::env::temp_dir().join(format!(
        "click-audit-bounded-scaling-{}",
        std::process::id()
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(
        directory.join("unit.c"),
        "int32 identity(int32 x) { return x; }",
    )
    .unwrap();
    let path = directory.join("unit.click");
    for size in [4, 8, 16, 32] {
        let mut source = String::from(
            "verifying \"unit.c\";\nint32 identity(int32 x) { ensures result == x; } by {\nstep_until(function.exit);\n",
        );
        // Keep the premise set fixed as the independent written sites grow.
        for _ in 0..size {
            source.push_str("have x == x by close();\n");
        }
        source.push_str("close();\n}\n");
        fs::write(&path, source).unwrap();
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert_eq!(sites.len(), size + 2);
        let arguments = parse_arguments([
            "--max-sites".to_string(),
            sites.len().to_string(),
            path.display().to_string(),
        ])
        .unwrap();
        let (result, work) =
            click::instrumentation::measure_deterministic_work(|| run_audit(arguments));
        result.unwrap();
        let uncapped = parse_arguments([path.display().to_string()]).unwrap();
        let (result, uncapped_work) =
            click::instrumentation::measure_deterministic_work(|| run_audit(uncapped));
        result.unwrap();
        // Compare the same claim at every size: the cap must add no repeated
        // expansion or cold checking, regardless of that claim's own cost.
        // Retained session work runs on its owned worker thread; the counter
        // here includes inventory, expansion, and both cold verifications.
        assert_eq!(work, uncapped_work, "{size} sites");
        eprintln!("audit {size}: bounded {work}, uncapped {uncapped_work} main-thread work units");
    }
    fs::remove_dir_all(directory).unwrap();
}
