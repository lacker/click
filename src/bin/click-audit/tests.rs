use super::*;
use click::surface::{
    c0_smart_tactic_source_sites, c0_tactic_source_position, verify_c0_sources,
    verify_c0_sources_at,
};

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
        let source = format!("verifying \"unit.c\";\nint32 identity(int32 x) {{ ensures result == x; }} by {{\nexecute();\n{}{}simp();\n}}\n", "have x + 0 == x by simp;\n".repeat(8), "have x == x by simp;\n".repeat(size));
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
    fs::write(&markdown, "# Partial selection in a container\n\n```c filename=unit.c\nint32 identity(int32 x) { return x; }\n```\n\n```click\nverifying \"unit.c\";\nint32 identity(int32 x) { ensures result == x; } by {\nexecute();\nhave x == x by simp;\nhave x + 0 == x by simp;\nsimp();\n}\n```\n\n```expect\npass\n```\n").unwrap();
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
            "verifying \"unit.c\";\nint32 identity(int32 x) { ensures result == x; } by {\nexecute();\n",
        );
        // Keep the premise set fixed as the independent written sites grow.
        for _ in 0..size {
            source.push_str("have x == x by simp;\n");
        }
        source.push_str("simp();\n}\n");
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

#[test]
fn parses_arguments_and_duration_units() {
    let arguments = parse_arguments(
        [
            "--session-time-limit",
            "30s",
            "--expansion-time-limit",
            "250ms",
            "--verification-time-limit",
            "2m",
            "--session-work-limit",
            "7_000",
            "--expansion-work-limit",
            "8000",
            "--verification-work-limit",
            "9000",
            "--performance-slack",
            "1_000",
            "--start-at",
            "examples/example.click:12:3",
            "--claim",
            "example.ensures_0",
            "--changed-since",
            "HEAD~1",
            "--verbose",
            "--keep-going",
            "--max-sites",
            "3",
            "examples",
        ]
        .map(str::to_string),
    )
    .unwrap();
    assert_eq!(
        arguments.limits,
        AuditLimits {
            session: PhaseLimit {
                work: 7_000,
                time: Duration::from_secs(30),
            },
            expansion: PhaseLimit {
                work: 8_000,
                time: Duration::from_millis(250),
            },
            verification: PhaseLimit {
                work: 9_000,
                time: Duration::from_secs(120),
            },
            performance_slack: 1_000,
        }
    );
    assert_eq!(
        arguments.start_at,
        Some(SourceLocation {
            path: PathBuf::from("examples/example.click"),
            line: 12,
            column: 3,
        })
    );
    assert!(arguments.keep_going);
    assert!(arguments.verbose);
    assert_eq!(arguments.claims, ["example.ensures_0"]);
    assert_eq!(arguments.changed_since.as_deref(), Some("HEAD~1"));
    assert_eq!(arguments.max_sites, Some(3));
    assert_eq!(arguments.path, PathBuf::from("examples"));
}

#[test]
fn work_options_count_units_and_refuse_durations() {
    let error = parse_arguments(["--performance-slack", "500ms", "examples"].map(str::to_string))
        .unwrap_err();
    assert!(error.contains("--performance-slack"), "{error}");
    assert!(error.contains("not time"), "{error}");
    assert!(parse_work_units("").is_err());
    assert!(parse_work_units("_").is_err());
    assert_eq!(parse_work_units("2_000_000"), Ok(2_000_000));
    let defaults = parse_arguments(["examples".to_string()]).unwrap();
    assert_eq!(defaults.limits, AuditLimits::default());
    // The help text states the defaults the parser applies.
    for (option, value) in [
        ("--session-work-limit", DEFAULT_SESSION_WORK_LIMIT),
        ("--expansion-work-limit", DEFAULT_EXPANSION_WORK_LIMIT),
        ("--verification-work-limit", DEFAULT_VERIFICATION_WORK_LIMIT),
        ("--performance-slack", DEFAULT_PERFORMANCE_SLACK),
    ] {
        assert!(
            USAGE.contains(&format!("{option} {value}")),
            "usage should state `{option} {value}`"
        );
    }
}

#[test]
fn source_locations_parse_from_the_right_and_are_one_based() {
    assert_eq!(
        parse_source_location("some:directory/example.click:12:34").unwrap(),
        SourceLocation {
            path: PathBuf::from("some:directory/example.click"),
            line: 12,
            column: 34,
        }
    );
    assert!(parse_source_location("example.click:0:1").is_err());
    assert!(parse_source_location("example.click:1").is_err());
}

#[test]
fn named_claim_selection_is_exact_ordered_and_rejects_ambiguity() {
    let site = |path: &str, claim: &str, line| AuditSite {
        click_path: PathBuf::from(path),
        position: SourcePosition {
            line,
            column: 1,
            origin: None,
        },
        click_position: SourcePosition {
            line,
            column: 1,
            origin: None,
        },
        claim: claim.to_string(),
        tactic_name: "auto".to_string(),
    };
    let sites = vec![
        site("a.click", "alpha.ensures_0", 1),
        site("a.click", "alpha.ensures_0", 2),
        site("a.click", "beta.ensures_0", 3),
    ];
    let named = |label: &str| AuditClaim {
        requested: label.to_string(),
        label: label.to_string(),
        path: None,
    };
    let selected = select_claim_sites(&sites, &[named("alpha.ensures_0")]).unwrap();
    assert_eq!(selected.len(), 2);
    assert_eq!(selected[0].position.line, 1);
    assert_eq!(selected[1].position.line, 2);
    assert!(
        select_claim_sites(&sites, &[named("missing")])
            .unwrap_err()
            .contains("unknown audit claim")
    );

    let ambiguous = vec![
        site("a.click", "alpha.ensures_0", 1),
        site("b.click", "alpha.ensures_0", 1),
    ];
    assert!(
        select_claim_sites(&ambiguous, &[named("alpha.ensures_0")])
            .unwrap_err()
            .contains("ambiguous")
    );
    // A claim selected by location names its file, which settles the
    // ambiguity.
    let located = AuditClaim {
        requested: "b.click:1".to_string(),
        label: "alpha.ensures_0".to_string(),
        path: Some(PathBuf::from("b.click")),
    };
    let selected = select_claim_sites(&ambiguous, std::slice::from_ref(&located)).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].click_path, PathBuf::from("b.click"));
}

#[test]
fn changed_selection_maps_leaf_proof_and_contract_changes_to_callers() {
    let c_sources = [
        ("leaf.c", "int32 leaf(int32 x) { return x; }"),
        (
            "caller.c",
            "int32 caller(int32 x) { int32 y = leaf(x); return y; }",
        ),
        ("unrelated.c", "int32 unrelated(int32 x) { return x; }"),
    ];
    let baseline = r#"
verifying "leaf.c";
verifying "caller.c";
verifying "unrelated.c";
int32 leaf(int32 x) { ensures result == x; } by simp;
int32 caller(int32 x) { ensures result == x; } by auto;
int32 unrelated(int32 x) { ensures result == x; } by auto;
"#;
    let site = |claim: &str, line| AuditSite {
        click_path: PathBuf::from("example.click"),
        position: SourcePosition {
            line,
            column: 1,
            origin: None,
        },
        click_position: SourcePosition {
            line,
            column: 1,
            origin: None,
        },
        claim: claim.to_string(),
        tactic_name: "auto".to_string(),
    };
    let sites = vec![
        site("leaf.contract", 1),
        site("caller.contract", 2),
        site("unrelated.contract", 3),
    ];

    for changed in [
        baseline.replacen("by simp", "by auto", 1),
        baseline.replacen("result == x", "result >= x", 1),
    ] {
        let selection =
            c0_incremental_selection(&changed, &c_sources, baseline, &c_sources).unwrap();
        assert_eq!(selection.selected_functions, ["caller", "leaf"]);
        let functions = selection
            .selected_functions
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let selected = select_function_sites(&sites, &functions);
        assert_eq!(
            selected
                .iter()
                .map(|site| site.claim.as_str())
                .collect::<Vec<_>>(),
            ["leaf.contract", "caller.contract"]
        );
    }
}

#[test]
fn click_engine_changes_force_a_full_changed_audit() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"));
    assert!(changed_paths_require_full_audit(
        repo,
        &[PathBuf::from("src/surface.rs")]
    ));
    assert!(!changed_paths_require_full_audit(
        repo,
        &[PathBuf::from("examples/owned-vector/vector.c")]
    ));
}

#[test]
fn resume_command_retries_the_cursor_inclusively() {
    let arguments = Arguments {
        path: PathBuf::from("examples with spaces"),
        limits: AuditLimits {
            session: PhaseLimit {
                work: 7_000,
                time: Duration::from_secs(30),
            },
            expansion: PhaseLimit {
                work: 8_000,
                time: Duration::from_secs(2),
            },
            verification: PhaseLimit {
                work: 9_000,
                time: Duration::from_secs(3),
            },
            performance_slack: 1_000,
        },
        time_limit: Duration::from_secs(600),
        start_at: None,
        claims: vec!["example.ensures_0".to_string()],
        changed_since: Some("HEAD~1".to_string()),
        verbose: true,
        keep_going: false,
        exclude: vec![PathBuf::from("examples with spaces/skipped")],
        max_sites: Some(1),
    };
    let location = SourceLocation {
        path: PathBuf::from("/tmp/example.click"),
        line: 12,
        column: 34,
    };
    assert_eq!(
        resume_command(&arguments, &location),
        "click audit --session-work-limit 7000 --expansion-work-limit 8000 \
             --verification-work-limit 9000 --performance-slack 1000 \
             --session-time-limit 30s --expansion-time-limit 2s \
             --verification-time-limit 3s --time-limit 10m \
             --exclude 'examples with spaces/skipped' \
             --verbose --claim example.ensures_0 --changed-since 'HEAD~1' --max-sites 1 \
             --start-at /tmp/example.click:12:34 'examples with spaces'"
    );
}

#[test]
fn exclude_is_repeatable_and_requires_a_path() {
    let arguments =
        parse_arguments(["--exclude", "a", "--exclude", "b/c.md", "examples"].map(str::to_string))
            .unwrap();
    assert_eq!(
        arguments.exclude,
        [PathBuf::from("a"), PathBuf::from("b/c.md")]
    );
    let error = parse_arguments(["examples", "--exclude"].map(str::to_string)).unwrap_err();
    assert!(error.contains("missing path after `--exclude`"), "{error}");
}

#[test]
fn end_of_options_accepts_a_dash_prefixed_target() {
    let arguments = parse_arguments(["--".to_string(), "-example.click".to_string()]).unwrap();
    assert_eq!(arguments.path, PathBuf::from("-example.click"));
}

#[test]
fn performance_comparison_requires_ratio_and_absolute_slack() {
    let slack = 500;
    assert!(!verification_regressed(5_000, 9_000, slack));
    assert!(!verification_regressed(100, 250, slack));
    assert!(verification_regressed(1_000, 2_501, slack));
    assert!(!verification_regressed(usize::MAX, usize::MAX, slack));
}

/// The expanded-over-original comparison counts deterministic work: an
/// expanded proof that genuinely does more work fails, and fails with the
/// same counts every time, whatever the clock says.
#[test]
fn an_expansion_that_does_more_work_fails_the_comparison_deterministically() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/scalar.md");
    let source = load_audit_source(&path).unwrap();
    let original = source.container_source.clone();
    let explicit = "by {\n        step();\n        have result == 1 by {\n            normalize();\n        }\n        assumption();\n    }";
    let redundant = format!(
        "by {{\n        step();\n{}        assumption();\n    }}",
        "        have result == 1 by {\n            normalize();\n        }\n".repeat(300)
    );
    let lean = original.replacen("by auto;", explicit, 1);
    let heavy = original.replacen("by auto;", &redundant, 1);
    assert_ne!(lean, original);
    assert_ne!(heavy, original);
    let limits = AuditLimits::default();
    let cost = |container: &str| {
        cold_verify(
            container,
            &source,
            "scalar.arithmetic_result",
            limits.verification,
            "test verification",
        )
        .unwrap()
    };
    // A process's first verification also loads the built-in standard
    // library; `click audit` has always initialized its session first.
    cost(&original);
    let original_cost = cost(&original);
    // The expansion `click expand` emits passes.
    assert_eq!(
        performance_regression(original_cost, cost(&lean), limits.performance_slack),
        None
    );
    let heavy_cost = cost(&heavy);
    let regression = performance_regression(original_cost, heavy_cost, limits.performance_slack)
        .unwrap_or_else(|| {
            panic!(
                "an expansion doing far more work regresses: {original_cost:?} -> {heavy_cost:?}"
            )
        });
    assert!(
        regression.contains("deterministic work units"),
        "{regression}"
    );
    let (again_original, again_heavy) = (cost(&original), cost(&heavy));
    assert_eq!(again_original.work, original_cost.work);
    assert_eq!(again_heavy.work, heavy_cost.work);
}

/// Machine load changes only the reported wall clock: every audit phase
/// spends the same deterministic work on a machine whose cores are all busy.
#[test]
fn an_audit_under_cpu_load_spends_the_same_work() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/scalar.md");
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    let site = sites.first().expect("the scalar mdtest has one smart site");
    let limits = AuditLimits::default();
    let run = || {
        let mut worker = AuditSessionWorker::start(&path, limits.session).unwrap();
        let timings = audit_site(
            site,
            &mut worker,
            &limits,
            true,
            Instant::now() + Duration::from_secs(600),
        )
        .expect("the scalar site audits");
        let cold = timings.cold_verification.expect("the first site compares");
        [
            worker.initialization.work,
            timings.expansion.work,
            timings.session_verification.work,
            cold.0.work,
            cold.1.work,
            timings.reexpansion.work,
        ]
    };
    // The first run in a process also loads the built-in standard library.
    run();
    let quiet = run();
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let burners = (0..std::thread::available_parallelism().map_or(4, |count| count.get()) * 2)
        .map(|_| {
            let stop = stop.clone();
            std::thread::spawn(move || {
                let mut spin = 0_u64;
                while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                    spin = std::hint::black_box(spin.wrapping_add(1));
                }
            })
        })
        .collect::<Vec<_>>();
    let loaded = run();
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    for burner in burners {
        burner.join().unwrap();
    }
    assert_eq!(quiet, loaded);
}

#[test]
fn whole_run_deadline_caps_each_phase() {
    let deadline = Instant::now() + Duration::from_secs(1);
    let limit = remaining_phase_limit(deadline, Duration::from_secs(30)).unwrap();
    assert!(limit <= Duration::from_secs(1));
    assert!(limit > Duration::ZERO);

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .unwrap();
    assert_eq!(
        remaining_phase_limit(expired, Duration::from_secs(30)),
        Err(RUN_LIMIT_EXHAUSTED.to_string())
    );
}

#[test]
fn site_timing_output_distinguishes_measured_and_skipped_cold_work() {
    let cost = |work, milliseconds| PhaseCost {
        work,
        elapsed: Duration::from_millis(milliseconds),
    };
    let rewrite = |cold_verification| SiteRewrite {
        expanded: String::new(),
        expansion: cost(10, 1),
        cold_verification,
        reexpansion: cost(50, 5),
    };
    let skipped = render_site_rewrite(&rewrite(None));
    assert!(skipped.contains("cold comparison not run"), "{skipped}");
    assert!(!skipped.contains("cold original 0"), "{skipped}");

    let measured = render_site_rewrite(&rewrite(Some((cost(30, 3), cost(40, 4)))));
    assert!(
        measured.contains("cold original 30 units, 3ms"),
        "{measured}"
    );
    assert!(
        measured.contains("cold rewritten 40 units, 4ms"),
        "{measured}"
    );
}

#[test]
fn start_cursor_is_an_inclusive_global_lower_bound() {
    let site = |path: &str, line| AuditSite {
        click_path: PathBuf::from(path),
        position: SourcePosition {
            line,
            column: 3,
            origin: None,
        },
        click_position: SourcePosition {
            line,
            column: 3,
            origin: None,
        },
        claim: "claim".to_string(),
        tactic_name: "simp".to_string(),
    };
    let sites = vec![
        site("/tmp/a.click", 10),
        site("/tmp/a.click", 20),
        site("/tmp/b.click", 5),
    ];
    assert_eq!(
        first_site_at_or_after(
            &sites,
            Some(&SourceLocation {
                path: PathBuf::from("/tmp/a.click"),
                line: 20,
                column: 3,
            })
        ),
        1
    );
    assert_eq!(
        first_site_at_or_after(
            &sites,
            Some(&SourceLocation {
                path: PathBuf::from("/tmp/a.click"),
                line: 15,
                column: 1,
            })
        ),
        1
    );
}

#[test]
fn expanded_tiny_project_reparses_and_verifies() {
    let c_source = "int32 example() { return 0; }";
    let click_source = r#"
verifying "example.c";

int32 example() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("example.c", c_source)];
    let inventory = c0_smart_tactic_source_sites(click_source, &sources).unwrap();
    assert_eq!(
        inventory
            .iter()
            .map(|site| (
                site.claim_label.as_str(),
                site.source_index,
                site.tactic_name.as_str()
            ))
            .collect::<Vec<_>>(),
        vec![
            ("example.contract", 0, "execute"),
            ("example.contract", 1, "simp"),
        ]
    );
    verify_c0_sources(click_source, &sources).unwrap();
    let position =
        c0_tactic_source_position(click_source, &sources, "example.contract", 0).unwrap();
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column).unwrap();

    assert_ne!(expanded, click_source);
    click::surface::verifying_source_paths(&expanded).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
fn rewritten_claim_position_survives_an_expansion_that_removes_a_tactic() {
    let c_source = "int32 example() { return 0; }";
    let click_source = r#"verifying "example.c";
int32 example() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("example.c", c_source)];
    let position =
        c0_tactic_source_position(click_source, &sources, "example.contract", 1).unwrap();
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("redundant trailing simp should expand away");
    assert!(!expanded.contains("simp();"));

    let source = AuditSource {
        container_source: expanded.clone(),
        click_source: expanded,
        c_sources: vec![("example.c".to_string(), c_source.to_string())],
        inputs: CInput::Bundle(vec![("example.c".to_string(), c_source.to_string())]),
        project: None,
        line_offset: 0,
        mdtest: None,
    };
    let relocated = claim_source_position(&source, "example.contract")
        .expect("the rewritten claim should have a fresh selector");
    verify_c0_sources_at(
        &source.click_source,
        &[("example.c", c_source)],
        relocated.line,
        relocated.column,
    )
    .expect("the relocated rewritten proof should verify");
}

#[test]
fn inventory_does_not_advertise_loop_invariants_as_proof_sites() {
    let c_source = r#"
int32 count_to_one() {
    int32 i;
    i = 0;
    while (i < 1) {
        i = i + 1;
    }
    return i;
}
"#;
    let click_source = r#"
verifying "loop.c";

int32 count_to_one() {
    ensures result == 1;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= 1;
        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
"#;
    let sources = [("loop.c", c_source)];
    let inventory = c0_smart_tactic_source_sites(click_source, &sources).unwrap();

    assert!(
        inventory
            .iter()
            .all(|site| !site.claim_label.contains(".invariant_")),
        "{inventory:?}"
    );
    assert!(
        inventory.iter().any(|site| {
            site.claim_label == "count_to_one.contract" && site.tactic_name == "simp"
        })
    );
}

#[test]
fn repository_root_targets_examples_and_passing_mdtests() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let targets = audit_targets(&root).expect("repository audit targets should resolve");
    assert!(
        targets.iter().any(|path| {
            path.extension()
                .is_some_and(|extension| extension == "click")
        }),
        "example sidecars must be included"
    );
    assert!(
        targets
            .iter()
            .any(|path| path.ends_with("mdtests/scalar.md")),
        "passing mdtests must be included"
    );
    let imported_mdtest = targets
        .iter()
        .find(|path| path.ends_with("mdtests/specification_imports.md"))
        .expect("import-backed mdtests must remain audit targets");
    let direct_mdtest_targets =
        audit_targets(&root.join("mdtests")).expect("the mdtest directory should stay selectable");
    assert!(direct_mdtest_targets.contains(imported_mdtest));
    let imported_sites = inventory_sites(std::slice::from_ref(imported_mdtest))
        .expect("audit should resolve an mdtest's imported Click modules");
    assert!(
        imported_sites.iter().any(|site| {
            site.claim.contains("imported_function_is_available") && site.tactic_name == "auto"
        }),
        "{imported_sites:?}"
    );
}

#[test]
fn markdown_inventory_and_expansion_use_container_coordinates() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/scalar.md");
    let sites =
        inventory_sites(std::slice::from_ref(&path)).expect("the scalar mdtest should inventory");
    let site = sites.first().expect("the scalar mdtest has one smart site");
    assert!(site.position.line > site.click_position.line);
    let location = format_location(&site_location(site));
    let expanded = expand_location(&location).expect("the markdown smart site should expand");
    let source =
        load_audit_source_from_text(&path, expanded).expect("expanded markdown should re-extract");
    let refs = source_refs(&source.c_sources);
    verify_c0_sources(&source.click_source, &refs).expect("expanded markdown proof should verify");
    let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
    audit_site(
        site,
        &mut worker,
        &AuditLimits::default(),
        true,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("markdown audit retains extracted Click coordinates");
}

#[test]
fn cpp_mdtest_audit_inventories_imported_semantics() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/cpp_scalar_catch.md");
    let source = load_audit_source(&path).expect("prepare C++ mdtest for audit");
    assert!(matches!(source.inputs, CInput::PreparedProgram(_)));
    assert!(source.project.is_some());
    let sites = inventory_sites(&[path]).expect("inventory C++ smart proof sites");
    assert!(sites.iter().any(|site| site.claim == "caller.ensures_0"));
}

#[test]
fn branched_expansion_reaches_the_audit_fixed_point() {
    let directory =
        std::env::temp_dir().join(format!("click-audit-branched-paths-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"int32 write_selected(int32 p[2], int32 flag) {
    if (flag) { p[0] = 1; return 0; }
    else { p[1] = 1; return 1; }
}"#;
    let click_source = r#"verifying "write_selected.c";
int32 write_selected(int32 p[2], int32 flag) {
    consumes p[0..2];
    ensures result == 0 or result == 1;
} by {
    execute();
    if result == 0 {
        have result + 1 == 1 by simp;
    } else {
        have result - 1 == 0 by simp;
    }
    simp();
}
"#;
    let click_path = directory.join("branched.click");
    fs::write(directory.join("write_selected.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.tactic_name == "have")
        .expect("the branch should expose an auditable smart have");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("the audit expansion path should handle branched frames");
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c0_sources(&source.click_source, &refs)
        .expect("the audited branched expansion should verify");

    assert_eq!(
        reexpand_source(&click_path, &site.claim, &expanded).unwrap(),
        expanded
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn infeasible_branch_arm_site_audits_instead_of_reporting_a_missing_tactic() {
    // Reduced from `tree_contains` in `examples/modeled-binary-tree`, whose
    // first `branch` guards a C path the contract rules out. Checked
    // execution drops that arm, so its `simp` never runs; audit used to fail
    // the site with `has no source tactic 2` while `click verify` passed the
    // same sidecar. The site must audit: it expands by removal, the rewrite
    // verifies, and re-expansion is a fixed point.
    let directory =
        std::env::temp_dir().join(format!("click-audit-dropped-arm-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"int32 flag(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}"#;
    let click_source = r#"verifying "flag.c";
int32 flag(int32 x) {
    requires x <= 0;
    ensures result == 0;
} by {
    branch then { step(); simp(); } else {}
    step();
    simp();
}
"#;
    let click_path = directory.join("dropped_arm.click");
    fs::write(directory.join("flag.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c0_sources(click_source, &[("flag.c", c_source)])
        .expect("the infeasible-arm proof should verify");

    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.position.line == 6)
        .expect("the dropped arm's simp should be an auditable site");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("a smart tactic on a dropped C path should expand");
    assert!(!expanded.contains("step(); simp();"), "{expanded}");
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c0_sources(&source.click_source, &refs)
        .expect("the audited dropped-arm expansion should verify");

    assert_eq!(
        reexpand_source(&click_path, &site.claim, &expanded).unwrap(),
        expanded
    );
    fs::remove_dir_all(directory).unwrap();
}

// macOS `/usr/bin/gcc` is Apple Clang and cannot exercise the GNU import path.
#[cfg(not(target_os = "macos"))]
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn prepared_audit_reuses_validated_inputs_across_sites() {
    let directory =
        std::env::temp_dir().join(format!("click-audit-prepared-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("unit.click");
    let config = directory.join("unit.click.import.json");
    fs::write(
        directory.join("unit.c"),
        "int identity(int x) { return x; }\n",
    )
    .unwrap();
    fs::write(&path, "verifying \"unit.c\";\nint32 identity(int32 x) { ensures result == x; } by { execute(); simp(); }\n").unwrap();
    fs::write(&config, serde_json::to_vec(&serde_json::json!({
        "schema": 1, "target": "x86_64-linux-kernel", "compiler": "/usr/bin/gcc", "working_directory": ".",
        "environment": {"allow": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"}},
        "sources": [{"logical_source": "unit.c", "path": "unit.c", "args": [], "artifact": "unit.i"}]
    })).unwrap()).unwrap();
    click::languages::c::compiler_import::create_lock(&config).unwrap();
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert!(sites.len() >= 2);
    let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
    // An active audit has already selected an immutable input. Any attempt to
    // reread the importer per tactic would now fail. A new audit must fail.
    fs::remove_file(directory.join("unit.i")).unwrap();
    for site in &sites {
        audit_site(
            site,
            &mut worker,
            &AuditLimits::default(),
            true,
            Instant::now() + Duration::from_secs(30),
        )
        .unwrap();
    }
    assert!(AuditSessionWorker::start(&path, AuditLimits::default().session).is_err());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn smart_have_inside_an_open_scope_audits_instead_of_reporting_a_missing_tactic() {
    // Reduced from `object_retain_many` in `examples/refcount` and the two
    // `have`s of `arena_write` in `examples/arena`. The resource-scope driver
    // checked the `have` but recorded no expansion for its source occurrence,
    // so audit failed the site with `has no source tactic 1` while `click
    // verify` accepted the same sidecar. The grouped closer in the same proof
    // covers the produced resource claim whose closure the certificate spells
    // `assumption`.
    let directory =
        std::env::temp_dir().join(format!("click-audit-scope-have-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"struct object {
    int32 refs;
};

void object_retain_many(struct object* obj, int32 amount) {
    obj->refs = obj->refs + amount;
}"#;
    let click_source = r#"authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns allocation(obj, sizeof(struct object));
    owns *obj;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "object_retain_many.c";

void object_retain_many(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires defined(obj->refs + amount);
    owns control(obj);
    produces amount of reference(obj);
    ensures defined(obj->refs);
} by {
    open(control(obj)) {
        have obj->refs == count(reference(obj)) by simp;
        step();
        fold(amount of reference(obj));
    }
    execute();
    simp();
}
"#;
    let click_path = directory.join("scope_have.click");
    fs::write(directory.join("object_retain_many.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c0_sources(click_source, &[("object_retain_many.c", c_source)])
        .expect("the produced-resource proof should verify");

    let line_of = |needle: &str| {
        let offset = click_source
            .find(needle)
            .unwrap_or_else(|| panic!("proof should contain `{needle}`"));
        click_source[..offset]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1
    };
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    for needle in [
        "have obj->refs == count(reference(obj)) by simp;",
        "simp();\n}",
    ] {
        let line = line_of(needle);
        let site = sites
            .iter()
            .find(|site| site.position.line == line)
            .unwrap_or_else(|| panic!("line {line} should be an auditable site"));
        let expanded = expand_location(&format_location(&site_location(site)))
            .unwrap_or_else(|error| panic!("line {line} should expand: {error}"));
        let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
        let refs = source_refs(&source.c_sources);
        verify_c0_sources(&source.click_source, &refs)
            .unwrap_or_else(|error| panic!("line {line} rewrite: {}", error.message()));
        assert_eq!(
            reexpand_source(&click_path, &site.claim, &expanded).unwrap(),
            expanded
        );
    }
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn audit_expands_an_unnamed_witness_with_a_checked_return_pointer() {
    let directory =
        std::env::temp_dir().join(format!("click-audit-witness-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"struct node {
    int32 value;
    unsigned long word;
};

struct node* unpack(struct node* node) {
    return (struct node*)(node->word & ~1);
}"#;
    let click_source = r#"resource packed(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "unpack.c";

struct node* unpack(struct node* node) {
    requires node != 0;
    owns packed(node);
    ensures address(result) == (node->word & ~1);
} by {
    unfold(packed(node));
    execute();
    fold(packed(node));
    simp();
}
"#;
    let click_path = directory.join("witness.click");
    fs::write(directory.join("unpack.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c0_sources(click_source, &[("unpack.c", c_source)])
        .expect("the witness fold/unfold proof should verify");

    let closer_line = click_source
        .lines()
        .position(|line| line.trim() == "simp();")
        .expect("proof should contain the closer")
        + 1;
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.position.line == closer_line)
        .expect("the closer should be an auditable site");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("the checked return pointer names the witness");
    verify_c0_sources(&expanded, &[("unpack.c", c_source)])
        .expect("the expansion must verify with fresh kernel state");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn audits_an_undecided_wide_guard_after_a_recursive_call() {
    // `list_count_live` in `examples/marked-linked-list` reduced: a recursive
    // call whose result lands in a local, then a C `if` whose condition loads
    // an `unsigned long` cell of the node the call did not touch, all inside
    // the `else` arm of a surface `if`. `execute()` renders the guard it
    // cannot decide as a proof `if` anchored at the statement's entry, and the
    // recheck applies each arm's `step()` under `RequireProven`: the arm
    // assumes the surface lowering of the guard while the C guard evaluates
    // against the snapshot its own load resolved. Those agree only because
    // every integer scalar one to eight bytes wide is named where it is
    // loaded; an unnamed `load_uint64` reads the whole current snapshot, which
    // after the call differs by the `local:rest` cell the load cannot alias,
    // and audit reported `2 feasible condition paths` where `click verify`
    // passed.
    let directory =
        std::env::temp_dir().join(format!("click-audit-wide-guard-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"struct cell {
    int32 value;
    unsigned long word;
};

uint32 count_live(struct cell *node) {
    if (node == 0) {
        return 0;
    }
    uint32 rest = count_live((struct cell *)(node->word & ~1));
    if ((node->word & 1) != 0) {
        return rest;
    }
    return rest + 1;
}"#;
    let click_source = r#"resource tagged(node: struct cell*) {
    if node != 0 {
        owns *node;
        fact aligned(node, 8);
        let next: struct cell* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
        owns tagged(next);
    }
}

verifying "count_live.c";

uint32 count_live(struct cell* node) {
    decreases tagged(node);
    owns tagged(node);
} by {
    if node == 0 {
        execute();
        simp();
    } else {
        unfold(tagged(node));
        execute();
        fold(tagged(node));
        simp();
    }
}
"#;
    let click_path = directory.join("count_live.click");
    fs::write(directory.join("count_live.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c0_sources(click_source, &[("count_live.c", c_source)])
        .expect("the recursive count proof should verify");

    let arm_execute = click_source
        .rfind("execute();")
        .expect("proof should contain the `else` arm's execute");
    let line = click_source[..arm_execute]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.position.line == line)
        .expect("the arm's execute should be an auditable site");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("the arm's execute should expand");
    assert!(
        expanded.contains("if at(statement(5).entry, (node->word & 1))"),
        "the undecided C guard should expand to an anchored proof `if`: {expanded}"
    );
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c0_sources(&source.click_source, &refs)
        .unwrap_or_else(|error| panic!("the rewritten arm should reverify: {}", error.message()));
    assert_eq!(
        reexpand_source(&click_path, &site.claim, &expanded).unwrap(),
        expanded
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn audits_an_omitted_preservation_with_two_body_breaks() {
    // `stop_at` from `mdtests/loop_body_break_exit.md` with both phases
    // omitted: a `while (true)` whose only ways out are two `break`s in
    // nested C `if`s. `click verify` passed while the expansion the audit
    // checks did not: the preservation driver runs sibling arms on one
    // interleaved provenance chain, and a leaf's lineage walk followed the
    // sibling arm's nested split marker and adopted that arm's steps, so the
    // emitted script reached the second `if` at the wrong frontier and `step`
    // reported "2 feasible condition paths".
    let directory =
        std::env::temp_dir().join(format!("click-audit-break-exit-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"int32 stop_at(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 3) {
            break;
        }
        if (i == 0) {
            break;
        }
        i = 0;
    }
    return i;
}"#;
    let click_source = r#"verifying "stop_at.c";

int32 stop_at(int32 n) {
    requires n >= 0;
    ensures result == 3 or result == 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;
    }
    step();
    simp();
}
"#;
    let click_path = directory.join("stop_at.click");
    fs::write(directory.join("stop_at.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c0_sources(click_source, &[("stop_at.c", c_source)])
        .expect("the omitted-phase break-exit loop should verify");

    let loop_offset = click_source
        .find("loop {")
        .expect("the proof should contain the loop tactic");
    let line = click_source[..loop_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.position.line == line)
        .expect("the omitted-phase loop should be an auditable site");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("the omitted-phase loop should expand");
    assert!(
        expanded.contains("if i == 3") && expanded.contains("if i == 0"),
        "each breaking C `if` should expand to a proof case: {expanded}"
    );
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c0_sources(&source.click_source, &refs).unwrap_or_else(|error| {
        panic!(
            "the rewritten preservation should reverify: {}",
            error.message()
        )
    });
    assert_eq!(
        reexpand_source(&click_path, &site.claim, &expanded).unwrap(),
        expanded
    );
    fs::remove_dir_all(directory).unwrap();
}

/// The reduced `examples/arena` audit failures audit every smart site: a
/// loop proof after a proof-level `branch`, an entry alignment fact cited as
/// a premise, and the retained session checked between main-thread
/// expansions and cold reverifications. Before the session had a thread of
/// its own, every expansion replaced the kernel tables its environment names.
#[test]
#[ignore = "nightly: 23s in the parallel gate"]
fn reduced_arena_init_fixtures_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let deadline = Instant::now() + Duration::from_secs(120);
    for relative in [
        "mdtests/loop_after_proof_branch_expands.md",
        "mdtests/entry_alignment_premise_expands.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert!(sites.len() >= 4, "{relative}: {sites:?}");
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        for (index, site) in sites.iter().enumerate() {
            if let Err(message) = audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            ) {
                panic!(
                    "{relative}:{}:{} should audit: {message}",
                    site.position.line, site.position.column
                );
            }
        }
    }
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn a_field_selected_memory_endpoint_audits_every_site() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/resource_field_memory_endpoint.md");
    let deadline = Instant::now() + Duration::from_secs(120);
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert!(sites.len() >= 2, "{sites:?}");
    let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
    for (index, site) in sites.iter().enumerate() {
        if let Err(message) = audit_site(
            site,
            &mut worker,
            &AuditLimits::default(),
            index == 0,
            deadline,
        ) {
            panic!(
                "{}:{} should audit: {message}",
                site.position.line, site.position.column
            );
        }
    }
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn an_unfold_bound_scalar_field_audits_every_site() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/resource_unfold_binds_scalar_field.md");
    let deadline = Instant::now() + Duration::from_secs(120);
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert!(sites.len() >= 2, "{sites:?}");
    let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
    for (index, site) in sites.iter().enumerate() {
        if let Err(message) = audit_site(
            site,
            &mut worker,
            &AuditLimits::default(),
            index == 0,
            deadline,
        ) {
            panic!(
                "{}:{} should audit: {message}",
                site.position.line, site.position.column
            );
        }
    }
}

#[test]
fn sidecar_importing_a_sibling_project_loads_under_the_verify_root() {
    // `examples/rbtree-insert` imports `../rbtree-model/rbtree_model.click`.
    // `click verify` widens a lone sidecar's project root to cover its
    // imports; audit loaded the project at the sidecar's own directory and
    // refused the import as outside the project root.
    let directory =
        std::env::temp_dir().join(format!("click-audit-sibling-import-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir_all(directory.join("model")).unwrap();
    fs::create_dir_all(directory.join("entry")).unwrap();
    fs::write(
        directory.join("model/model.click"),
        "function twice(x: int) -> int {\n    x + x\n}\n",
    )
    .unwrap();
    fs::write(
        directory.join("entry/double.c"),
        "int32 double_it(int32 x) {\n    return x + x;\n}\n",
    )
    .unwrap();
    let click_path = directory.join("entry/double.click");
    fs::write(
        &click_path,
        r#"import "../model/model.click";

verifying "double.c";

int32 double_it(int32 x) {
    requires x >= 0;
    requires x < 1000;
    ensures result == x + x;
} by {
    execute();
    simp();
}
"#,
    )
    .unwrap();
    let sites = inventory_sites(std::slice::from_ref(&click_path))
        .expect("the sidecar should load under the root `click verify` selects");
    assert!(sites.iter().any(|site| site.tactic_name == "simp"));
    fs::remove_dir_all(directory).unwrap();
}

#[test]
#[ignore = "nightly: 41s in the parallel gate"]
fn loop_expansion_preserves_match_pointer_theorem_arguments_and_audits_every_site() {
    let fixture =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/rb_ascending_walk_to_root.md");
    let original = fs::read_to_string(fixture).unwrap();
    let source = original.replacen(
        "function plug(",
        "theorem ptr_self(p: struct rb_node*) { ensures p == p by { simp(); } }\n\
         theorem ptr_equal(p: struct rb_node*, q: struct rb_node*) { requires p == q; ensures p == q by { assumption(); } }\n\nfunction plug(",
        1,
    ).replace("initialize by simp;", "");
    let anchor = "                    have identity == parent by {\n                        extract(identity == parent);\n                    }";
    assert!(
        source.contains(anchor),
        "fixture must retain the Left arm's pointer equality"
    );
    let source = source.replacen(
        anchor,
        &format!(
            "{anchor}\n\
        have identity == identity by {{ apply(ptr_self(identity)); assumption(); }}\n\
        have identity == parent by {{ apply(ptr_equal(identity, parent)); assumption(); }}"
        ),
        1,
    );
    let directory =
        std::env::temp_dir().join(format!("click-audit-loop-pointer-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("loop_pointer.md");
    fs::write(&path, source).unwrap();
    let prepared = load_audit_source(&path).unwrap();
    verify_c0_sources(&prepared.click_source, &source_refs(&prepared.c_sources))
        .expect("the original loop must verify before expansion");
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    let loop_site = sites
        .iter()
        .find(|site| site.tactic_name == "loop")
        .unwrap();
    let expanded = expand_location(&format_location(&site_location(loop_site)))
        .expect("the loop's named pointer arguments must expand");
    assert!(expanded.contains("apply(ptr_self(identity))"), "{expanded}");
    assert!(
        expanded.contains("apply(ptr_equal(identity, parent))"),
        "{expanded}"
    );
    let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
    let deadline = Instant::now() + Duration::from_secs(120);
    for (index, site) in sites.iter().enumerate() {
        audit_site(
            site,
            &mut worker,
            &AuditLimits::default(),
            index == 0,
            deadline,
        )
        .unwrap_or_else(|message| {
            panic!(
                "{}:{} {}: {message}",
                site.position.line, site.position.column, site.tactic_name
            )
        });
    }
    drop(worker);
    fs::remove_dir_all(directory).unwrap();
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn short_circuit_conditions_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let deadline = Instant::now() + Duration::from_secs(120);
    for relative in [
        "mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md",
        "mdtests/a_condition_reaching_one_value_along_two_paths_splits_into_them.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert!(sites.len() >= 2, "{relative}: {sites:?}");
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| {
                panic!(
                    "{relative}:{}:{} should audit: {message}",
                    site.position.line, site.position.column
                )
            });
        }
    }
}

/// Ranked loops without invariants have an empty initialization certificate.
/// The printer retains `assumption();` there; audit must also establish that
/// every rewrite parses, re-verifies in the retained session and directly,
/// reaches an expansion fixed point, and respects the ordinary work limits.
#[test]
fn ranked_loops_without_invariants_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for relative in [
        "mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md",
        "mdtests/a_ranked_unsigned_loop_with_no_invariant_closes_a_branching_body.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert_eq!(sites.len(), 3, "{relative}: {sites:?}");
        assert!(sites.iter().any(|site| site.tactic_name == "loop"));
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        let deadline = Instant::now() + Duration::from_secs(120);
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| {
                panic!(
                    "{relative}:{}:{} {}: {message}",
                    site.position.line, site.position.column, site.tactic_name
                )
            });
        }
    }
}

/// Caller requirements that read seeded arrays must survive both unchanged
/// retained checks and audit's expanded rewrites, at every tactic site.
#[test]
#[ignore = "nightly: 31 s, over the gate's per-test budget (2026-10-06)"]
fn callers_with_seeded_array_requirements_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for relative in [
        "mdtests/static_array_parity_fixed_multidimensional.md",
        "mdtests/static_array_parity_multidimensional.md",
        "mdtests/static_array_parity_scalar.md",
        "mdtests/static_local_arrays.md",
        "mdtests/static_local_array_requirement_stated_explicitly.md",
        "mdtests/cstr_dynamic_indexed_read.md",
        "mdtests/cstr_source_identity_reordered_requirement.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert!(!sites.is_empty(), "{relative} must have tactic sites");
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        let deadline = Instant::now() + Duration::from_secs(120);
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| {
                panic!(
                    "{relative}:{}:{} {}: {message}",
                    site.position.line, site.position.column, site.tactic_name
                )
            });
        }
    }
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn resource_proof_expansions_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (relative, expected_sites) in [
        ("mdtests/resource_witness_unfold_fold.md", 2),
        ("mdtests/rb_parent_family.md", 18),
        ("mdtests/population_count_states_its_transition.md", 2),
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert_eq!(sites.len(), expected_sites, "{relative}");
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        let deadline = Instant::now() + Duration::from_secs(120);
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| {
                panic!(
                    "{relative}:{}:{}: {message}",
                    site.position.line, site.position.column
                )
            });
        }
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn nested_call_outcomes_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for relative in [
        "mdtests/outcomes_routes_a_throw_that_leaves_the_function.md",
        "mdtests/grouped_proof_closes_claims_across_two_throwing_calls.md",
        "mdtests/execute_splits_a_throwing_call_inside_a_c_if.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert!(!sites.is_empty(), "{relative} must have tactic sites");
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        let deadline = Instant::now() + Duration::from_secs(120);
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| {
                panic!(
                    "{relative}:{}:{}: {message}",
                    site.position.line, site.position.column
                )
            });
        }
    }
}

#[test]
fn exceptional_call_paths_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (relative, expected_sites) in [
        ("mdtests/exceptional_call_continuation.md", 2),
        ("mdtests/exceptional_terminal_call.md", 2),
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert_eq!(
            sites.len(),
            expected_sites,
            "{relative} must audit every helper and caller site"
        );
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        let deadline = Instant::now() + Duration::from_secs(120);
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| panic!("{relative}: {message}"));
        }
    }
}

#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn result_parameter_postconditions_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for relative in [
        "mdtests/result_parameter_old_value_certifies.md",
        "mdtests/result_parameter_entry_snapshot_certifies.md",
        "mdtests/result_parameter_current_binding_certifies.md",
        "mdtests/result_parameter_resource_binding_certifies.md",
        "mdtests/result_parameter_mutation_certifies.md",
        "mdtests/result_parameter_field_binding_certifies.md",
        "mdtests/result_parameter_cast_binding_certifies.md",
        "mdtests/result_parameter_pointer_operations_certify.md",
        "mdtests/result_parameter_array_indices_certify.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert!(!sites.is_empty(), "{relative} must have tactic sites");
        let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
        let deadline = Instant::now() + Duration::from_secs(120);
        for (index, site) in sites.iter().enumerate() {
            audit_site(
                site,
                &mut worker,
                &AuditLimits::default(),
                index == 0,
                deadline,
            )
            .unwrap_or_else(|message| panic!("{relative}: {message}"));
        }
    }
}

#[test]
fn a_claims_rewrites_combine_into_one_source() {
    let original = "step;\nsimp;\nstep;\nauto;\nstep;\n";
    let first = "step;\nrewrite(a);\nassumption();\nstep;\nauto;\nstep;\n";
    let second = "step;\nsimp;\nstep;\nstep;\n";
    assert_eq!(
        combine_rewrites(original, &[second, first]).as_deref(),
        Some("step;\nrewrite(a);\nassumption();\nstep;\nstep;\n"),
    );
    assert_eq!(combine_rewrites(original, &[first]).as_deref(), Some(first));
}

#[test]
fn rewrites_of_the_same_text_do_not_combine() {
    let original = "step;\nsimp;\nstep;\n";
    let first = "step;\nrewrite(a);\nstep;\n";
    let second = "step;\nrewrite(b);\nstep;\n";
    assert_eq!(combine_rewrites(original, &[first, second]), None);
    assert_eq!(combine_rewrites(original, &[first, first]), None);
}

/// Verifying a claim's rewrites together runs the claim once, so it costs
/// about one site's verification rather than one per site.
#[test]
#[ignore = "nightly: 73 s, over the gate's per-test budget (2026-10-06)"]
fn a_claims_rewrites_are_verified_in_one_run() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let sources = audit_targets(&path).unwrap();
    let sites = inventory_sites(&sources).unwrap();
    // The first claim in the corpus with at least three smart sites.
    let mut by_claim: BTreeMap<(PathBuf, String), Vec<&AuditSite>> = BTreeMap::new();
    for site in &sites {
        by_claim
            .entry((site.click_path.clone(), site.claim.clone()))
            .or_default()
            .push(site);
    }
    let limits = AuditLimits::default();
    let deadline = Instant::now() + Duration::from_secs(600);
    let mut checked = 0;
    for ((path, claim), claim_sites) in by_claim {
        if claim_sites.len() < 3 {
            continue;
        }
        let mut worker = AuditSessionWorker::start(&path, limits.session).unwrap();
        let mut rewrites = Vec::new();
        let mut alone = Vec::new();
        for site in &claim_sites {
            let Ok(rewrite) = audit_site_rewrite(site, &mut worker, &limits, false, deadline)
            else {
                break;
            };
            alone.push(
                verify_rewrite_in_session(
                    &mut worker,
                    &claim,
                    &rewrite.expanded,
                    &limits,
                    deadline,
                )
                .unwrap()
                .work,
            );
            rewrites.push(rewrite.expanded);
        }
        if rewrites.len() < claim_sites.len() {
            continue;
        }
        let original = worker.source.container_source.clone();
        let references = rewrites.iter().map(String::as_str).collect::<Vec<_>>();
        if combine_rewrites(&original, &references).is_none() {
            continue;
        }
        let together =
            verify_claim_rewrites(&mut worker, &claim, &references, &limits, deadline).unwrap();
        let largest = *alone.iter().max().unwrap();
        let total: usize = alone.iter().sum();
        assert!(
            together.work <= largest * 2 && together.work < total,
            "{claim}: together {} units, alone {alone:?}",
            together.work
        );
        checked += 1;
        if checked == 3 {
            break;
        }
    }
    assert_eq!(checked, 3, "the corpus has claims with several smart sites");
}

#[test]
fn inventory_keeps_distinct_sites_inside_have_bodies() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("nested.click");
    let source = r#"
theorem helper(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by { assumption(); }
}
theorem nested(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        have 0 <= x by {
            have 0 <= x by { apply(helper(x)); }
            apply(helper(x));
            assumption();
        }
        assumption();
    }
}
"#;
    fs::write(&path, source).unwrap();
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert_eq!(sites.len(), 2);
    assert!(
        sites
            .iter()
            .all(|site| site.claim == "nested.ensures_0" && site.tactic_name == "apply")
    );
    assert_ne!(sites[0].position, sites[1].position);
    for site in sites {
        assert_eq!(site.position, site.click_position);
        let expanded = expand_c0_tactic_source_at(
            source,
            &[],
            site.click_position.line,
            site.click_position.column,
        )
        .unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
    }
}

#[test]
fn inventory_obeys_the_work_and_whole_run_bounds() {
    let directory = std::env::temp_dir().join(format!(
        "click-audit-inventory-bounds-{}",
        std::process::id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("unit.click");
    fs::write(
        &path,
        "theorem identity() { ensures 0 == 0 by { simp(); } }",
    )
    .unwrap();
    let mut arguments = parse_arguments([path.display().to_string()]).unwrap();
    arguments.limits.session.work = 1;
    let error = run_audit(arguments).unwrap_err();
    assert!(error.contains("smart-site inventory"), "{error}");
    assert!(error.contains("budget"), "{error}");
    let mut arguments = parse_arguments([path.display().to_string()]).unwrap();
    arguments.time_limit = Duration::ZERO;
    let error = run_audit(arguments).unwrap_err();
    assert!(error.contains(RUN_LIMIT_EXHAUSTED), "{error}");
    fs::remove_dir_all(directory).unwrap();
}
