use super::*;
use click::surface::{
    c_smart_tactic_source_sites, c_tactic_source_position, verify_c_sources, verify_c_sources_at,
};

fn audit_all_sites(path: &Path) {
    let arguments = parse_arguments([
        "--time-limit".into(),
        "120s".into(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
}

#[test]
fn theorem_replay_with_a_partial_expression_in_an_unselected_theorem() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/retained_equality_conditionals.md");
    let arguments = parse_arguments([
        "--claim".to_string(),
        "closed_int64_equality_guards.ensures_0".to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).unwrap();
}

#[test]
#[ignore = "nightly: generic Rust claim expansion and retained/cold audit rechecks"]
fn generic_rust_clause_proofs_stay_on_the_generic_function() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (fixture, claim) in [
        (
            "option-values/options.click",
            "option_values::wrap.ensures_0",
        ),
        (
            "result-values/results.click",
            "result_values::same.ensures_0",
        ),
    ] {
        let path = root.join("design/charon-trial").join(fixture);
        let arguments = parse_arguments([
            "--claim".to_string(),
            claim.to_string(),
            path.display().to_string(),
        ])
        .unwrap();
        run_audit(arguments).unwrap_or_else(|error| panic!("{fixture}: {error}"));
    }

    let path = root.join("design/charon-trial/option-values/options.click");
    let original = fs::read_to_string(&path).unwrap();
    let invalid = original.replacen(
        "ensures result == Option<T>::Some(value);",
        "ensures result == Option<T>::Some(value) by { have 0 == 1 by close(); }",
        1,
    );
    assert_ne!(invalid, original);
    let source = load_audit_source_from_text(&path, invalid).unwrap();
    let error = match start_session(&source) {
        Ok(_) => panic!("the generic function's invalid proof must still be checked"),
        Err(error) => error,
    };
    assert!(error.contains("goal: 0 == 1"), "{error}");
    assert!(
        !error.contains("external function contracts cannot carry proof"),
        "{error}"
    );

    // An imported interface contract cannot carry a program proof.
    let path = root.join("design/charon-trial/extern-functions/ffi.click");
    let mut source = load_audit_source(&path).unwrap();
    let project = source.project.as_ref().unwrap();
    let original = fs::read_to_string(path.with_file_name("ffi.interface.click")).unwrap();
    let invalid = original.replacen(
        "ensures 0 <= result and result <= 100;",
        "ensures 0 <= result and result <= 100 by { close(); }",
        1,
    );
    assert_ne!(invalid, original);
    source.project = Some(ClickProject::new(
        project.entry(),
        project.modules().iter().map(|module| {
            if module.identity() == "ffi.interface.click" {
                click::surface::ClickModuleSource::new(module.identity(), &invalid, [])
            } else {
                module.clone()
            }
        }),
    ));
    let error = match start_session(&source) {
        Ok(_) => panic!("an interface contract cannot carry a program proof"),
        Err(error) => error,
    };
    assert!(
        error.contains("external function contracts cannot carry proof"),
        "{error}"
    );
}

/// Runtime inventory names execution-theorem proofs `T.contract`; every
/// expansion route must resolve that label to the theorem's postcondition.
#[test]
#[ignore = "nightly: execution-theorem label expansion and full claim audits"]
fn execution_theorem_contract_labels_expand_and_audit() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    for (fixture, theorem) in [
        (
            "named_contract_value_parameter_execution_theorem",
            "add3_adds_three",
        ),
        (
            "named_contract_value_parameter_execution_theorem",
            "adds_three_shifts_three",
        ),
        ("execution_theorem_imported_tactic", "zero_contract"),
    ] {
        let path = root.join(format!("{fixture}.md"));
        let source = load_audit_source(&path).unwrap();
        let claim = format!("{theorem}.contract");
        let legacy = format!("{theorem}.ensures_0");
        let expanded = expand_claim_with_source(&path, &source, &claim)
            .unwrap_or_else(|error| panic!("{claim}: {error}"));
        assert_ne!(expanded, source.container_source);
        assert_eq!(
            expanded,
            expand_claim_with_source(&path, &source, &legacy).unwrap()
        );
        let rewritten = rewritten_click_source(&source, &expanded).unwrap();
        click::surface::without_implicit_solve(|| {
            verify_rewritten_with_inputs(&source, &claim, &rewritten)
        })
        .unwrap_or_else(|error| panic!("{claim}: {error}"));
        if fixture == "named_contract_value_parameter_execution_theorem" {
            let VerificationInput::Bundle(sources) = &source.inputs else {
                panic!("the fixture has ordinary C sources");
            };
            assert_eq!(
                expand_c_claim_source_by_label(&source.click_source, &source_refs(sources), &claim)
                    .unwrap(),
                rewritten
            );
        }
        let arguments =
            parse_arguments(["--claim".to_string(), claim, path.display().to_string()]).unwrap();
        run_audit(arguments).unwrap_or_else(|error| panic!("{fixture}: {error}"));
    }
    assert!(
        expand_c_claim_source_by_label(
            "theorem ordinary() { ensures 1 == 1; }",
            &[],
            "ordinary.contract",
        )
        .is_err(),
        "ordinary theorem postconditions do not acquire a grouped contract alias"
    );
}

#[test]
#[ignore = "nightly: C++ generic method expansion and retained/cold rechecks"]
fn generic_cpp_clause_proofs_stay_on_the_generic_method() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (fixture, claim) in [
        (
            "cpp_class_template_verified_once",
            "__cpp_q_X7_43656c6c3c543e_I3_get.ensures_0",
        ),
        (
            "cpp_generic_resource_checked_once",
            "__cpp_q_X8_537461636b3c543e_I4_size.ensures_0",
        ),
    ] {
        let path = root.join("mdtests").join(format!("{fixture}.md"));
        let arguments = parse_arguments([
            "--claim".to_string(),
            claim.to_string(),
            path.display().to_string(),
        ])
        .unwrap();
        run_audit(arguments).unwrap_or_else(|error| panic!("{fixture}: {error}"));
    }

    let path = root.join("mdtests/cpp_class_template_verified_once.md");
    let original = fs::read_to_string(&path).unwrap();
    let invalid = original.replacen(
        "ensures result == this->value;",
        "ensures result == this->value by { have 0 == 1 by close(); }",
        1,
    );
    assert_ne!(invalid, original);
    let source = load_audit_source_from_text(&path, invalid).unwrap();
    let error = match start_session(&source) {
        Ok(_) => panic!("the generic method's invalid proof must still be checked"),
        Err(error) => error,
    };
    assert!(error.contains("goal: 0 == 1"), "{error}");
    assert!(
        !error.contains("external function contracts cannot carry proof"),
        "{error}"
    );

    let error = verify_c_sources(
        "extern int32 f() { ensures result == 0 by { close(); } }",
        &[],
    )
    .unwrap_err();
    assert!(
        error
            .message()
            .contains("external function contracts cannot carry proof"),
        "{error}"
    );
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
                deadline: None,
            },
            expansion: PhaseLimit {
                work: 8_000,
                time: Duration::from_millis(250),
                deadline: None,
            },
            verification: PhaseLimit {
                work: 9_000,
                time: Duration::from_secs(120),
                deadline: None,
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

/// The internal translation-unit suffix is not legal Click syntax. Calls
/// in state paths use the source spelling, with each occurrence retained.
#[test]
#[ignore = "nightly: static-call state expansion and full claim audit"]
fn static_call_state_paths_expand_and_audit() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/c_static_function.md");
    let source = load_audit_source(&path).unwrap();
    let claim = "run.contract";
    let expanded = expand_claim_with_source(&path, &source, claim)
        .expect("static calls have a source spelling in expanded states");
    let rewritten = rewritten_click_source(&source, &expanded).unwrap();
    assert!(rewritten.contains("call(add_one, 0)"), "{rewritten}");
    assert!(rewritten.contains("call(add_one, 1)"), "{rewritten}");
    assert!(!rewritten.contains("#inline:"), "{rewritten}");
    assert!(!rewritten.contains("#file-static:"), "{rewritten}");
    click::surface::without_implicit_solve(|| {
        verify_rewritten_with_inputs(&source, claim, &rewritten)
    })
    .expect("the printed call occurrences resolve to their original regions");
    let arguments = parse_arguments([
        "--claim".to_string(),
        claim.to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).expect("the original static-call proof audits completely");
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
        tactic_name: "implicit tail".to_string(),
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
int32 leaf(int32 x) { ensures result == x; } by { step_until(function.exit); close(); }
int32 caller(int32 x) { ensures result == x; }
int32 unrelated(int32 x) { ensures result == x; }
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
        tactic_name: "implicit tail".to_string(),
    };
    let sites = vec![
        site("leaf.contract", 1),
        site("caller.contract", 2),
        site("unrelated.contract", 3),
    ];

    for changed in [
        baseline.replacen("step_until(function.exit); close();", "step(); close();", 1),
        baseline.replacen("result == x", "result >= x", 1),
    ] {
        let selection =
            c_incremental_selection(&changed, &c_sources, baseline, &c_sources).unwrap();
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
fn changed_audit_selects_markdown_claims_for_relative_targets() {
    let cwd = std::env::current_dir().unwrap();
    let repo = tempfile::tempdir_in(&cwd).unwrap();
    let fixture_dir = repo.path().join("mdtests");
    fs::create_dir(&fixture_dir).unwrap();
    let fixture = fixture_dir.join("scalar.md");
    let original = include_str!("../../../mdtests/scalar.md");
    fs::write(&fixture, original).unwrap();

    let git = |args: &[&str]| {
        let output = Command::new("git")
            .current_dir(repo.path())
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    };
    git(&["init", "-q"]);
    git(&["add", "mdtests/scalar.md"]);
    git(&[
        "-c",
        "user.name=Click Test",
        "-c",
        "user.email=test@example.com",
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-qm",
        "baseline",
    ]);

    let changed = original.replacen("(1 + 2) == 3", "(1 + 3) == 4", 1);
    assert_ne!(original, changed);
    fs::write(&fixture, changed).unwrap();

    for path in [
        fixture.strip_prefix(&cwd).unwrap(),
        fixture_dir.strip_prefix(&cwd).unwrap(),
        &fixture,
    ] {
        let arguments = parse_arguments(
            ["--changed-since", "HEAD", path.to_str().unwrap()].map(str::to_string),
        )
        .unwrap();
        let inventory =
            prepare_audit(&arguments, Instant::now() + Duration::from_secs(30)).unwrap();
        assert_eq!(inventory.scoped_sites.len(), 1, "{}", path.display());
        let site = &inventory.scoped_sites[0];
        assert_eq!(site.click_path, fs::canonicalize(&fixture).unwrap());
        assert_eq!(site.claim, "scalar.arithmetic_result");
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
                deadline: None,
            },
            expansion: PhaseLimit {
                work: 8_000,
                time: Duration::from_secs(2),
                deadline: None,
            },
            verification: PhaseLimit {
                work: 9_000,
                time: Duration::from_secs(3),
                deadline: None,
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
        resume_command(&arguments, Some(&location)),
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
fn successful_replay_reports_work_increase_and_unavailable_original_cost() {
    let cost = |work| PhaseCost {
        work,
        elapsed: Duration::from_millis(20),
    };
    let report = |original, expanded| {
        claim_audit_report(String::new(), Ok(cost(original)), cost(expanded), 500)
    };
    assert!(report(5_000, 9_000).work_increase.is_none());
    assert!(report(100, 250).work_increase.is_none());
    let increase = report(1_000, 2_501).work_increase.unwrap();
    assert!(increase.contains("informational"), "{increase}");
    assert!(report(usize::MAX, usize::MAX).work_increase.is_none());

    let report = claim_audit_report(String::new(), Err("original limit".into()), cost(200), 500);
    assert!(
        report
            .detail
            .contains("cold original unavailable (original limit)")
    );
    assert!(report.detail.contains("cold rewritten 200 units"));
}

#[test]
fn cold_replay_applies_the_absolute_work_budget_and_reports_written_proof_size() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/scalar.md");
    let source = load_audit_source(&path).unwrap();
    let claim = "scalar.arithmetic_result";
    let expanded = expand_claim_with_source(&path, &source, claim).unwrap();
    let limit = AuditLimits::default().verification;
    let replay = cold_verify_expansion(&expanded, &source, claim, limit, true).unwrap();
    let rewritten_click = rewritten_click_source(&source, &expanded).unwrap();
    let speed = proof_speed(
        &source,
        &rewritten_click,
        claim,
        replay.claim_elapsed,
        limit,
    );
    assert!(speed.contains("written proof lines"), "{speed}");
    assert!(!speed.contains(", 0 written proof lines"), "{speed}");
    let error = match cold_verify_expansion(
        &expanded,
        &source,
        claim,
        PhaseLimit { work: 1, ..limit },
        true,
    ) {
        Ok(_) => panic!("one deterministic unit cannot check the proof"),
        Err(error) => error,
    };
    assert!(error.starts_with("cold replay:"), "{error}");
    assert!(error.contains("1-unit budget"), "{error}");
}

/// Machine load changes only the reported wall clock: every audit phase
/// spends the same deterministic work on a machine whose cores are all busy.
#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
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
fn whole_run_deadline_keeps_the_phase_crash_bound() {
    let configured = PhaseLimit {
        work: 100,
        time: Duration::from_secs(30),
        deadline: None,
    };
    let deadline = Instant::now() + Duration::from_secs(1);
    let limit = configured.within(deadline).unwrap();
    assert_eq!(limit.time, configured.time);
    assert_eq!(limit.deadline, Some(deadline));
    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .unwrap();
    assert_eq!(
        configured.within(expired),
        Err(RUN_LIMIT_EXHAUSTED.to_string())
    );
    assert_eq!(
        run_phase(
            "expired phase",
            PhaseLimit {
                deadline: Some(expired),
                ..configured
            },
            || -> Result<(), String> {
                panic!("an expired phase must not start");
            }
        ),
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
    assert!(skipped.contains("cold replay not run"), "{skipped}");
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
        tactic_name: "solve".to_string(),
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
    step_until(function.exit);
    close();
}
"#;
    let sources = [("example.c", c_source)];
    let inventory = c_smart_tactic_source_sites(click_source, &sources).unwrap();
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
            ("example.contract", 0, "step_until"),
            ("example.contract", 1, "close"),
        ]
    );
    verify_c_sources(click_source, &sources).unwrap();
    let position = c_tactic_source_position(click_source, &sources, "example.contract", 0).unwrap();
    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column).unwrap();

    assert_ne!(expanded, click_source);
    click::surface::verifying_source_paths(&expanded).unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
}

#[test]
fn rewritten_claim_position_survives_an_expansion_that_removes_a_tactic() {
    let c_source = "int32 example() { return 0; }";
    let click_source = r#"verifying "example.c";
int32 example() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}
"#;
    let sources = [("example.c", c_source)];
    let position = c_tactic_source_position(click_source, &sources, "example.contract", 1).unwrap();
    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("redundant trailing solve should expand away");
    assert!(!expanded.contains("solve();"));

    let source = AuditSource {
        container_source: expanded.clone(),
        click_source: expanded,
        c_sources: vec![("example.c".to_string(), c_source.to_string())],
        inputs: VerificationInput::Bundle(vec![("example.c".to_string(), c_source.to_string())]),
        project: None,
        line_offset: 0,
        mdtest: None,
    };
    let relocated = claim_source_position(&source, "example.contract")
        .expect("the rewritten claim should have a fresh selector");
    verify_c_sources_at(
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
        initialize by close();
        maintain by {
            step();
        }
    }
    step();
    close();
}
"#;
    let sources = [("loop.c", c_source)];
    let inventory = c_smart_tactic_source_sites(click_source, &sources).unwrap();

    assert!(
        inventory
            .iter()
            .all(|site| !site.claim_label.contains(".invariant_")),
        "{inventory:?}"
    );
    assert!(inventory.iter().any(|site| {
        site.claim_label == "count_to_one.contract" && site.tactic_name == "close"
    }));
}

#[test]
fn repository_root_targets_examples_and_passing_mdtests() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let targets = without_expected_failure_mdtests(
        audit_targets(&root).expect("repository audit targets should resolve"),
    )
    .expect("repository inventory should classify all container expectations");
    assert!(
        !targets.iter().any(|path| path
            .ends_with("mdtests/a_sidecar_conjunction_written_as_ampersands_names_and.md")),
        "the negative syntax fixture must not reach runtime inventory"
    );
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
            site.claim.contains("imported_function_is_available")
                && site.tactic_name == "implicit tail"
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
    verify_c_sources(&source.click_source, &refs).expect("expanded markdown proof should verify");
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
    assert!(matches!(
        source.inputs,
        VerificationInput::PreparedProgram(_)
    ));
    assert!(source.project.is_some());
    let sites = inventory_sites(&[path]).expect("inventory C++ smart proof sites");
    assert!(sites.iter().any(|site| site.claim == "caller.ensures_0"));
}

#[test]
fn partial_theorem_audit_keeps_the_region_of_a_byte_identical_expansion() {
    let source = r#"// déjà vu
theorem identity(x: int32) {
    requires x == 0;
    ensures x == 0 by {
        have x == 0 by {
            close();
        }
        close();
    }
}

theorem neighbor(x: int32) {
    ensures x == 0 implies x == 0 by close();
}
"#;
    let sites = c_smart_tactic_source_sites(source, &[]).unwrap();
    let artifact = click::surface::expand_c_tactics_source_at(
        source,
        &[],
        std::slice::from_ref(&sites[0].position),
    )
    .unwrap();
    assert_eq!(artifact.source, source);
    assert_eq!(artifact.replacement_spans.len(), 1);
    assert_eq!(
        artifact.replacement_spans[0],
        source.find("by {").unwrap()..source.find("\n}\n").unwrap()
    );

    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("partial_theorem.click");
    fs::write(&path, source).unwrap();
    let arguments = parse_arguments([
        "--claim".to_string(),
        "identity.ensures_0".to_string(),
        "--max-sites".to_string(),
        "1".to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).unwrap();
}

#[test]
fn partial_audit_checks_emitted_closers_and_leaves_other_search_available() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("partial.md");
    let mdtest = r#"```c filename=identity.c
int32 identity(int32 x) { return x; }
```

```click
verifying "identity.c";
int32 identity(int32 x) {
    requires x == 0;
    ensures result == 0;
} by {
    have 0 == x by { close(); }
    step_until(function.exit);
}
```

```expect
pass
```
"#;
    fs::write(&path, mdtest).unwrap();
    let arguments = parse_arguments([
        "--claim".to_string(),
        "identity.contract".to_string(),
        "--max-sites".to_string(),
        "1".to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).unwrap();

    let path = directory.path().join("implication.click");
    let source = "theorem identity(x: int32) { ensures x == 0 implies x == 0 by close(); }";
    fs::write(&path, source).unwrap();
    let original = load_audit_source(&path).unwrap();
    let start = source.find("close").unwrap();
    let artifact = click::surface::SelectedTacticExpansion {
        source: source.to_string(),
        replacement_spans: std::iter::once(start..start + "close();".len()).collect(),
    };
    let replay = || {
        cold_verify_expansion(
            source,
            &original,
            "identity.ensures_0",
            AuditLimits::default().verification,
            false,
        )
    };
    assert!(replay().is_ok());
    let error = artifact
        .with_checked_closers(replay)
        .unwrap()
        .err()
        .expect("a generated closer may not search for a proof");
    assert!(error.contains("cold replay:"), "{error}");
    assert!(
        replay().is_ok(),
        "the next replay restores ordinary closing"
    );
}

#[test]
fn complete_replay_allows_direct_close_and_refuses_its_search_fallback() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("implication.click");
    let original = r#"
theorem identity(x: int32) {
    ensures x == 0 implies x == 0 by { close(); }
}
"#;
    fs::write(&path, original).unwrap();
    let claim = "identity.ensures_0";
    let arguments = parse_arguments([
        "--claim".to_string(),
        claim.to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).expect("the expanded closer checks directly after intro");

    let source = load_audit_source(&path).unwrap();
    let limit = AuditLimits::default().verification;
    assert!(cold_verify_expansion(original, &source, claim, limit, false).is_ok());
    let error = cold_verify_expansion(original, &source, claim, limit, true)
        .err()
        .expect("the original closer still needs search");
    assert!(
        error.starts_with("cold replay: ") && error.contains(claim),
        "{error}"
    );
}

#[test]
fn cpp_theorem_expansion_uses_imported_record_layouts() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/cpp_class_template_override_calls_its_own_method.md");
    let arguments = parse_arguments([
        "--claim".to_string(),
        "stored_value.ensures_0".to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).unwrap();
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
    if flag != 0 {
        step_until(function.exit);
        have result + 1 == 1 by close();
    } else {
        step_until(function.exit);
        have result - 1 == 0 by close();
    }
}
"#;
    let click_path = directory.join("branched.click");
    fs::write(directory.join("write_selected.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.tactic_name == "close")
        .expect("the branch should expose a closer inside a have");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("the audit expansion path should handle branched frames");
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c_sources(&source.click_source, &refs)
        .expect("the audited branched expansion should verify");

    let limits = AuditLimits::default();
    let mut worker = AuditSessionWorker::start(&click_path, limits.session).unwrap();
    audit_site(
        site,
        &mut worker,
        &limits,
        true,
        Instant::now() + Duration::from_secs(60),
    )
    .expect("the emitted site is a checked fixed point");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn infeasible_branch_arm_site_audits_instead_of_reporting_a_missing_tactic() {
    // Reduced from `tree_contains` in `examples/modeled-binary-tree`, whose
    // first `branch` guards a C path the contract rules out. Checked
    // execution drops that arm, so its `solve` never runs; audit used to fail
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
    branch { true => { step(); close(); } false => {} }
    step();
    close();
}
"#;
    let click_path = directory.join("dropped_arm.click");
    fs::write(directory.join("flag.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c_sources(click_source, &[("flag.c", c_source)])
        .expect("the infeasible-arm proof should verify");

    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.position.line == 6)
        .expect("the dropped arm's solve should be an auditable site");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("a smart tactic on a dropped C path should expand");
    assert!(!expanded.contains("step(); close();"), "{expanded}");
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c_sources(&source.click_source, &refs)
        .expect("the audited dropped-arm expansion should verify");

    let limits = AuditLimits::default();
    let mut worker = AuditSessionWorker::start(&click_path, limits.session).unwrap();
    audit_site(
        site,
        &mut worker,
        &limits,
        true,
        Instant::now() + Duration::from_secs(60),
    )
    .expect("the emitted site is a checked fixed point");
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
    let project_file = directory.join(click::project::FILE_NAME);
    fs::write(
        directory.join("unit.c"),
        "int identity(int x) { return x; }\n",
    )
    .unwrap();
    fs::write(
        &path,
        "verifying \"unit.c\";\nint32 identity(int32 x) { ensures result == x; } by { step_until(function.exit); close(); }\n",
    )
    .unwrap();
    fs::write(
        &project_file,
        serde_json::to_vec(&serde_json::json!({"units": {"unit": {
            "language": "c", "compiler": "/usr/bin/gcc",
            "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
            "sources": {"unit.c": {}}
        }}}))
        .unwrap(),
    )
    .unwrap();
    click::project::Project::load(&project_file)
        .and_then(|project| project.lock())
        .unwrap();
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert_eq!(
        sites.len(),
        2,
        "the fixture must exercise two written smart sites"
    );
    let mut worker = AuditSessionWorker::start(&path, AuditLimits::default().session).unwrap();
    // An active audit has already selected an immutable input. Any attempt to
    // reread the importer per tactic would now fail. A new audit must fail.
    fs::remove_file(directory.join(".click/captures/unit/unit.c.i")).unwrap();
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
#[ignore = "nightly: 1.1s in the parallel gate"]
fn smart_have_inside_an_open_scope_audits_instead_of_reporting_a_missing_tactic() {
    // Reduced from `object_retain_many` in `examples/refcount` and the two
    // `have`s of `arena_write` in `examples/arena`. The resource-scope driver
    // checked the `have` but recorded no expansion for its source occurrence,
    // so audit failed the site with `has no source tactic 1` while `click
    // verify` accepted the same sidecar. The grouped closer in the same proof
    // covers the produced resource claim whose closure the certificate spells
    // `known`.
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
    with(control(obj)) {
        have obj->refs == count(reference(obj)) by close();
        step();
        fold(amount of reference(obj));
    }
    step_until(function.exit);
    close();
}
"#;
    let click_path = directory.join("scope_have.click");
    fs::write(directory.join("object_retain_many.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c_sources(click_source, &[("object_retain_many.c", c_source)])
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
        "have obj->refs == count(reference(obj)) by close();",
        "close();\n}",
    ] {
        let line = line_of(needle);
        assert!(
            sites.iter().any(|site| site.position.line == line),
            "line {line} should be an auditable site"
        );
    }
    audit_all_sites(&click_path);
    fs::remove_dir_all(directory).unwrap();
}

/// A claim whose only automation is the implicit `solve` proving a bare
/// step's obligation holds no smart site, but its expansion must still verify
/// without the implicit `solve`, so discovery makes it a site of its own. A
/// claim with smart sites is already expanded as a whole and is left to them.
#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn a_claim_proved_only_by_the_implicit_solve_is_audited() {
    let directory =
        std::env::temp_dir().join(format!("click-audit-implicit-solve-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir(&directory).unwrap();
    let c_source = r#"int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
int32 compare_smart(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}"#;
    let click_source = r#"verifying "compare.c";

int32 compare_self(uint8 bytes[]) {
    views bytes[0..2];
    ensures 1 == 1 by {
        step();
        step();
    }
}

int32 compare_smart(uint8 bytes[]) {
    views bytes[0..2];
    ensures 1 == 1 by {
        step();
        step();
        close();
    }
}
"#;
    let click_path = directory.join("compare.click");
    fs::write(directory.join("compare.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    let click_path = fs::canonicalize(&click_path).unwrap();
    let smart = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    assert!(
        smart
            .iter()
            .all(|site| site.claim == "compare_smart.ensures_0"),
        "{smart:?}"
    );
    let (implicit, failures) = implicit_solve_sites(
        std::slice::from_ref(&click_path),
        &smart,
        AuditLimits::default().session,
        false,
    )
    .unwrap();
    assert!(failures.is_empty(), "{failures:?}");
    let [site] = implicit.as_slice() else {
        panic!("one claim proved only by the implicit `solve`: {implicit:?}");
    };
    assert_eq!(site.claim, "compare_self.ensures_0");
    assert_eq!(
        site.tactic_name,
        click::instrumentation::IMPLICIT_SOLVE_TACTIC
    );
    entry_with([click_path.display().to_string()])
        .expect("both claims' expansions verify without the implicit `solve`");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
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
    step_until(function.exit);
    fold(packed(node));
    close();
    close() using {
        aligned(result, 8);
        node->word == address(result) + (node->word & 1);
    };
}
"#;
    let click_path = directory.join("witness.click");
    fs::write(directory.join("unpack.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c_sources(click_source, &[("unpack.c", c_source)])
        .expect("the witness fold/unfold proof should verify");

    let closer_line = click_source
        .lines()
        .position(|line| line.trim() == "close() using {")
        .expect("proof should contain the closer")
        + 1;
    let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
    let site = sites
        .iter()
        .find(|site| site.position.line == closer_line)
        .expect("the closer should be an auditable site");
    let expanded = expand_location(&format_location(&site_location(site)))
        .expect("the checked return pointer names the witness");
    verify_c_sources(&expanded, &[("unpack.c", c_source)])
        .expect("the expansion must verify with fresh kernel state");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn audits_an_undecided_wide_guard_after_a_recursive_call() {
    // `list_count_live` in `examples/marked-linked-list` reduced: a recursive
    // call whose result lands in a local, then a C `if` whose condition loads
    // an `unsigned long` cell of the node the call did not touch, all inside
    // the `else` arm of a surface `if`. The arm's implicit tail renders the guard it
    // cannot decide as a proof `if` anchored at the statement's entry, and the
    // recheck applies each arm's `step()`, which must prove the guard: the arm
    // assumes the surface lowering of the guard while the C guard evaluates
    // against the state its own load resolved. Those agree only because
    // every integer scalar one to eight bytes wide is named where it is
    // loaded; an unnamed `load<uint64>` reads the whole current state, which
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
    let click_source = r#"import click::separation;
resource tagged(node: struct cell*) {
    if node != 0 {
        owns *node;
        fact aligned(node, 8);
        let next: struct cell* where aligned(next, 8) and node->word == address(next) + (node->word & 1)
            and ((node->word & ~1) as (struct cell *)) == next;
        owns tagged(next);
    }
}

verifying "count_live.c";

uint32 count_live(struct cell* node) {
    decreases tagged(node);
    owns tagged(node);
} by {
    if node == 0 {
        step_until(function.exit);
        close();
    } else {
        let { next: child } = unfold(tagged(node));
        step_until(statement(1).entry);
        mark before_local;
        step();
        have separate(statement(1).region(0).footprint, memory(node->word)) by {
            close() using {};
        }
        have *((&node->word) as (int32 **)) == at(before_local, *((&node->word) as (int32 **))) by {
            preserve(memory(node->word), statement(1).region(0));
        }
        have ((node->word & ~1) as (struct cell *)) == child by { close(); }
        have separate(tagged(child), memory(node->word)) by { close(); }
        mark before_call;
        step();
        have contains(tagged(child), statement(1).region(1).footprint) by { close(); }
        apply(separation::contains_refl(memory(node->word)));
        apply(separation::separate_restrict(tagged(child), memory(node->word), statement(1).region(1).footprint, memory(node->word)));
        have *((&node->word) as (int32 **)) == at(before_call, *((&node->word) as (int32 **))) by {
            preserve(memory(node->word), statement(1).region(1));
        }
        have ((node->word & ~1) as (struct cell *)) == child by { close(); }
        mark before_assignment;
        step();
        have separate(statement(1).assignment(rest, 0).footprint, memory(node->word)) by {
            close() using {};
        }
        have *((&node->word) as (int32 **)) == at(before_assignment, *((&node->word) as (int32 **))) by {
            preserve(memory(node->word), statement(1).assignment(rest, 0));
        }
        have ((node->word & ~1) as (struct cell *)) == child by { close(); }
        fold(tagged(node));
        observe(tagged(node));
    }
}
"#;
    let click_path = directory.join("count_live.click");
    fs::write(directory.join("count_live.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c_sources(click_source, &[("count_live.c", c_source)])
        .expect("the recursive count proof should verify");

    // The arm's implicit tail is not a located site; the claim's expansion
    // renders it.
    let original = load_audit_source(&click_path).unwrap();
    let expanded = expand_claim_with_source(&click_path, &original, "count_live.contract")
        .expect("the arm's implicit tail should expand");
    assert!(
        expanded.contains("if at(region(6).entry, (node->word & 1))"),
        "the undecided C guard should expand to an anchored proof `if`: {expanded}"
    );
    let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
    let refs = source_refs(&source.c_sources);
    verify_c_sources(&source.click_source, &refs)
        .unwrap_or_else(|error| panic!("the rewritten arm should reverify: {}", error.message()));
    cold_verify_expansion(
        &expanded,
        &original,
        "count_live.contract",
        AuditLimits::default().verification,
        true,
    )
    .expect("the expanded claim should cold check without search");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn audits_an_omitted_preservation_with_two_body_breaks() {
    // `stop_at` from `mdtests/loop_body_early_exit.md` with both phases
    // omitted: a `while (true)` whose only ways out are two `break`s in
    // nested C `if`s. `click verify` passed while the expansion the audit
    // checks did not: the preservation driver runs sibling arms on one
    // interleaved lineage chain, and a leaf's lineage walk followed the
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
    close();
}
"#;
    let click_path = directory.join("stop_at.click");
    fs::write(directory.join("stop_at.c"), c_source).unwrap();
    fs::write(&click_path, click_source).unwrap();
    verify_c_sources(click_source, &[("stop_at.c", c_source)])
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
    verify_c_sources(&source.click_source, &refs).unwrap_or_else(|error| {
        panic!(
            "the rewritten preservation should reverify: {}",
            error.message()
        )
    });
    let limits = AuditLimits::default();
    let mut worker = AuditSessionWorker::start(&click_path, limits.session).unwrap();
    audit_site(
        site,
        &mut worker,
        &limits,
        true,
        Instant::now() + Duration::from_secs(60),
    )
    .expect("the emitted site is a checked fixed point");
    fs::remove_dir_all(directory).unwrap();
}

/// Audit a loop proof after a proof-level `branch`, retaining the session
/// between main-thread expansions and cold reverifications. Before the session
/// had a thread of its own, expansions replaced the kernel tables it names.
#[test]
#[ignore = "nightly: retained-session audit takes 3.6s"]
fn reduced_arena_init_fixtures_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let deadline = Instant::now() + Duration::from_secs(120);
    let relative = "mdtests/loop_after_proof_branch_expands.md";
    let path = root.join(relative);
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    // Check the first expansion and subsequent reuse of the same session.
    assert!(sites.len() >= 2, "{relative}: {sites:?}");
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
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert!(sites.len() >= 2, "{sites:?}");
    audit_all_sites(&path);
}

#[test]
fn sidecar_in_a_project_subdirectory_loads_under_the_project_root() {
    // `examples/rbtree/rbtree-insert` imports `../rbtree-model/rbtree_model.click` from
    // its project. Audit once loaded the project at the sidecar's own
    // directory and refused the import as outside the project root.
    let directory =
        std::env::temp_dir().join(format!("click-audit-project-import-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).unwrap();
    }
    fs::create_dir_all(directory.join("model")).unwrap();
    fs::create_dir_all(directory.join("entry")).unwrap();
    fs::write(directory.join("click.project.json"), "{}\n").unwrap();
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
    step_until(function.exit);
    close();
}
"#,
    )
    .unwrap();
    let sites = inventory_sites(std::slice::from_ref(&click_path))
        .expect("the sidecar should load under its project root");
    assert!(sites.iter().any(|site| site.tactic_name == "close"));
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
        "theorem ptr_self(p: struct rb_node*) { ensures p == p by { close(); } }\n\
         theorem ptr_equal(p: struct rb_node*, q: struct rb_node*) { requires p == q; ensures p == q by { close(); } }\n\nfunction plug(",
        1,
    ).replace("initialize by close();", "");
    let anchor = "                    have identity == parent by close();";
    assert!(
        source.contains(anchor),
        "fixture must retain the Left arm's pointer equality"
    );
    let source = source.replacen(
        anchor,
        &format!(
            "{anchor}\n\
        have identity == identity by {{ apply(ptr_self(identity)); close(); }}\n\
        have identity == parent by {{ apply(ptr_equal(identity, parent)); close(); }}"
        ),
        1,
    );
    let directory =
        std::env::temp_dir().join(format!("click-audit-loop-pointer-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("loop_pointer.md");
    fs::write(&path, source).unwrap();
    let prepared = load_audit_source(&path).unwrap();
    verify_c_sources(&prepared.click_source, &source_refs(&prepared.c_sources))
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
    // Audit the fixture through whole-claim replay. Exact closures can
    // keep the same source spelling while the checked replay disables search.
    audit_all_sites(&path);
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
/// The printer retains `close();` there; audit must also establish that
/// every rewrite parses, re-verifies in the retained session and directly,
/// reaches an expansion fixed point, and respects the ordinary work limits.
#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn ranked_loops_without_invariants_audit_every_site() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for relative in [
        "mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md",
        "mdtests/a_ranked_unsigned_loop_with_no_invariant_closes_a_branching_body.md",
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert_eq!(sites.len(), 1, "{relative}: {sites:?}");
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
        ("mdtests/resource_witness_unfold_fold.md", 3),
        ("mdtests/rb_parent_family.md", 38),
        ("mdtests/population_count_states_its_transition.md", 2),
    ] {
        let path = root.join(relative);
        let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
        assert_eq!(sites.len(), expected_sites, "{relative}");
        audit_all_sites(&path);
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
#[ignore = "nightly: 0.8s in the parallel gate"]
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
        "mdtests/result_parameter_entry_state_certifies.md",
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
        audit_all_sites(&path);
    }
}

#[test]
fn a_claims_rewrites_combine_into_one_source() {
    let original = "step;\nsolve;\nstep;\nauto;\nstep;\n";
    let first = "step;\nrewrite(a, b);\nclose();\nstep;\nauto;\nstep;\n";
    let second = "step;\nsolve;\nstep;\nstep;\n";
    assert_eq!(
        combine_rewrites(original, &[second, first]).as_deref(),
        Some("step;\nrewrite(a, b);\nclose();\nstep;\nstep;\n"),
    );
    assert_eq!(combine_rewrites(original, &[first]).as_deref(), Some(first));
}

#[test]
fn rewrites_of_the_same_text_do_not_combine() {
    let original = "step;\nsolve;\nstep;\n";
    let first = "step;\nrewrite(a, b);\nstep;\n";
    let second = "step;\nrewrite(b, a);\nstep;\n";
    assert_eq!(combine_rewrites(original, &[first, second]), None);
    assert_eq!(combine_rewrites(original, &[first, first]), None);
}

/// Verifying a claim's rewrites together runs the claim once, so it costs
/// about one site's verification rather than one per site.
#[test]
#[ignore = "nightly: audits combined rewrites of three multi-site claims"]
fn a_claims_rewrites_are_verified_in_one_run() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let directory = tempfile::tempdir().unwrap();
    let fixtures = [
        "statement_regions_reach_a_loop_body.md",
        "a_condition_reaching_one_value_along_two_paths_splits_into_them.md",
        "a_frame_holds_across_a_write_at_a_64_bit_index.md",
    ];
    // Exercise three disjoint replacements in each claim. The spaces inside
    // the written closers distinguish a replacement from a fixed point even
    // when emission can close the same fact directly.
    let probes = [
        "    have 1 == 1 by { close( ); }",
        "    have 2 == 2 by { close( ); }",
        "    have 3 == 3 by { close( ); }",
    ];
    let limits = AuditLimits::default();
    let deadline = Instant::now() + Duration::from_secs(600);
    for fixture in fixtures {
        let original = fs::read_to_string(root.join(fixture)).unwrap();
        let source =
            original.replacen("} by {\n", &format!("}} by {{\n{}\n", probes.join("\n")), 1);
        assert_ne!(original, source, "{fixture}");
        let path = directory.path().join(fixture);
        fs::write(&path, &source).unwrap();
        let inventory = inventory_sites(std::slice::from_ref(&path)).unwrap();
        let mut worker = AuditSessionWorker::start(&path, limits.session).unwrap();
        let mut rewrites = Vec::new();
        let mut alone = Vec::new();
        let mut claim = None;
        for probe in probes {
            let line = source.lines().position(|line| line == probe).unwrap() + 1;
            let site = inventory
                .iter()
                .find(|site| site.position.line == line)
                .unwrap_or_else(|| panic!("{fixture}:{line} must inventory its proof"));
            assert_eq!(*claim.get_or_insert(site.claim.as_str()), site.claim);
            let rewrite = audit_site_rewrite(site, &mut worker, &limits, false, deadline)
                .unwrap_or_else(|error| panic!("{fixture}:{line}: {error}"));
            alone.push(
                verify_rewrite_in_session(
                    &mut worker,
                    &site.claim,
                    &rewrite.expanded,
                    &limits,
                    deadline,
                )
                .unwrap()
                .work,
            );
            rewrites.push(rewrite.expanded);
        }
        let references = rewrites.iter().map(String::as_str).collect::<Vec<_>>();
        assert!(
            combine_rewrites(&source, &references).is_some(),
            "{fixture}"
        );
        let together =
            verify_claim_rewrites(&mut worker, claim.unwrap(), &references, &limits, deadline)
                .unwrap();
        let largest = *alone.iter().max().unwrap();
        let total: usize = alone.iter().sum();
        assert!(
            together.work <= largest * 2 && together.work < total,
            "{fixture}: together {} units, alone {alone:?}",
            together.work
        );
    }
}

#[test]
fn inventory_keeps_distinct_sites_inside_have_bodies() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("nested.click");
    let source = r#"
theorem nested(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        have 0 <= x by {
            have 0 <= x by { close(); }
            close();
        }
    }
}
"#;
    fs::write(&path, source).unwrap();
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert_eq!(sites.len(), 2);
    assert!(
        sites
            .iter()
            .all(|site| site.claim == "nested.ensures_0" && site.tactic_name == "close")
    );
    assert_ne!(sites[0].position, sites[1].position);
    for site in sites {
        assert_eq!(site.position, site.click_position);
        let expanded = expand_c_tactic_source_at(
            source,
            &[],
            site.click_position.line,
            site.click_position.column,
        )
        .unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
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
        "theorem identity() { ensures 0 == 0 by { close(); } }",
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

#[test]
#[ignore = "nightly: expanded loop audit checking work"]
fn expanded_loop_claims_stay_within_checking_work_bounds() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (fixture, claim) in [
        ("c_decreases_recursive_in_loop", "recursive_loop.contract"),
        ("later_loop_preserve", "later_loop_preserve.contract"),
        ("loop_exit_program_point", "count_from_to.contract"),
        ("nested_loop_preserve", "nested_loop_preserve.contract"),
    ] {
        let path = root.join("mdtests").join(format!("{fixture}.md"));
        let arguments = parse_arguments([
            "--claim".to_string(),
            claim.to_string(),
            path.display().to_string(),
        ])
        .unwrap();
        run_audit(arguments).unwrap_or_else(|error| panic!("{fixture}: {error}"));
    }
}

#[test]
#[ignore = "nightly: resource output expansion and retained/cold rechecks"]
fn resource_output_proofs_retain_their_implicit_return_folds() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (fixture, claim) in [
        ("cstr_at_folds_at_a_constant_length", "empty.contract"),
        (
            "fold_symbolic_quantity_without_search",
            "mint_positive.produces_0",
        ),
        ("conditional_allocated_record_output", "create.produces_0"),
        (
            "a_borrowed_composite_quantified_defined_fact_opens_and_folds",
            "mark.produces_0",
        ),
        ("calloc_zeroed_int32", "calloc_zeroed_int32.produces_0"),
        (
            "fresh_allocation_writes_are_internal_effects",
            "fresh_allocation_writes_are_internal_effects.produces_0",
        ),
        ("malloc_sizeof_scalar", "malloc_sizeof_scalar.produces_0"),
    ] {
        let path = root.join("mdtests").join(format!("{fixture}.md"));
        let arguments = parse_arguments([
            "--claim".to_string(),
            claim.to_string(),
            path.display().to_string(),
        ])
        .unwrap();
        run_audit(arguments).unwrap_or_else(|error| panic!("{fixture}: {error}"));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/bin/click-audit/tests.rs");
}

/// A selected `solve` leaves the earlier steps' implicit solving intact.
/// A whole-claim candidate that omits that automation must be refused instead.
#[test]
#[ignore = "nightly: partial and whole claim cold-verification policy"]
fn partial_claim_audit_keeps_solve_but_whole_claim_requires_its_certificate() {
    let directory = tempfile::tempdir().unwrap();
    let c_source = "int32 compare(uint8 bytes[]) { return memcmp(bytes, bytes, 2); }";
    let click_source = r#"verifying "compare.c";
function truth() -> int32 { 1 }
int32 compare(uint8 bytes[]) {
    views bytes[0..2];
    ensures 1 == 1 by {
        step();
        step();
        close();
    }
}
"#;
    let path = directory.path().join("compare.click");
    fs::write(directory.path().join("compare.c"), c_source).unwrap();
    fs::write(&path, click_source).unwrap();
    verify_c_sources(click_source, &[("compare.c", c_source)]).unwrap();
    let sites = inventory_sites(std::slice::from_ref(&path)).unwrap();
    assert_eq!(sites.len(), 1);
    let limits = AuditLimits::default();
    let deadline = Instant::now() + limits.session.time;
    let mut worker = AuditSessionWorker::start(&path, limits.session).unwrap();
    audit_selected_claim_rewrite(&sites, &mut worker, &limits, deadline, false)
        .expect("a partial rewrite must preserve the unselected steps' implicit solve");
    drop(worker);

    // Supply an incomplete expansion at the session boundary. It is valid
    // with implicit solve and has no smart sites, so only the whole-claim
    // cold check can detect the omitted evidence.
    let incomplete = click_source.replace(
        "close();",
        "have truth() == 1 by { unfold(truth()); } close();",
    );
    verify_c_sources(&incomplete, &[("compare.c", c_source)]).unwrap();
    // Even an unchanged candidate must fail if a bare step still relies on
    // implicit solving. Exercise both changed and byte-identical replies.
    for original in [click_source, incomplete.as_str()] {
        let source = load_audit_source_from_text(&path, original.to_string()).unwrap();
        let expected_error = click::surface::without_implicit_solve(|| {
            verify_rewritten_with_inputs(&source, &sites[0].claim, &incomplete)
        })
        .expect_err("the incomplete expansion needs implicit solve");
        let (requests, receiver) = mpsc::channel::<SessionRequest>();
        let (responses, response_receiver) = mpsc::channel();
        let expansion = incomplete.clone();
        let thread = thread::spawn(move || {
            for request in receiver {
                responses
                    .send(Ok(SessionResponse {
                        cost: PhaseCost {
                            work: 0,
                            elapsed: Duration::ZERO,
                        },
                        expansion: request.expansion_claim.map(|_| expansion.clone()),
                    }))
                    .unwrap();
            }
        });
        let mut worker = AuditSessionWorker {
            source,
            requests: Some(requests),
            responses: response_receiver,
            thread: Some(thread),
            initialization: PhaseCost {
                work: 0,
                elapsed: Duration::ZERO,
            },
        };
        let error = audit_claim_rewrite(&sites[0], &mut worker, &limits, deadline, false)
            .expect_err("a whole-claim rewrite must include the implicit solve's evidence");
        assert_eq!(error, format!("cold replay: {expected_error}"));
    }
}

#[test]
#[ignore = "nightly: whole-claim audits with neighboring proofs and pthread workers"]
fn whole_claim_audits_allow_unexpanded_neighbors_and_workers() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    for (fixture, claim) in [
        ("statement_program_points", "set_first_twice.prefix_exit"),
        (
            "statement_program_points",
            "set_first_twice.adjacent_boundary",
        ),
        ("statement_program_points", "set_first_twice.final_exit"),
        ("composite_resource_borrow_fact", "inspect_server.owns_0"),
        (
            "composite_resource_borrow_fact",
            "inspect_server.state_is_ready",
        ),
        ("composite_resource_observe_nested_fact", "return_fd.owns_0"),
        (
            "composite_resource_separate_fact",
            "clobber_dst_packaged.owns_0",
        ),
        (
            "composite_resource_separate_fact",
            "clobber_dst_packaged.source_unchanged",
        ),
        (
            "authority_modeled_pthread_distinct_workers_spend",
            "run.contract",
        ),
        ("modeled_pthread_counted_join", "run.contract"),
        ("modeled_pthread_counted_reverse_join", "run.contract"),
    ] {
        let path = root.join(format!("{fixture}.md"));
        let arguments = parse_arguments([
            "--claim".to_string(),
            claim.to_string(),
            path.display().to_string(),
        ])
        .unwrap();
        run_audit(arguments).unwrap_or_else(|error| panic!("{fixture}, {claim}: {error}"));
    }
}

#[test]
#[ignore = "nightly: strict selected-proof refusals and scope restoration"]
fn cold_claim_scope_keeps_selected_proofs_strict_and_refuses_unknown_labels() {
    use click::surface::{without_implicit_solve, without_implicit_solve_for_claim};
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/statement_program_points.md");
    let source = load_audit_source(&path).unwrap();
    let check = || {
        verify_rewritten_with_inputs(&source, "set_first_twice.final_exit", &source.click_source)
    };
    let error = without_implicit_solve_for_claim("set_first_twice.final_exit", check).unwrap_err();
    assert!(error.contains("set_first_twice.final_exit"), "{error}");
    assert!(error.contains("implicit tail is off"), "{error}");
    assert!(!error.contains("set_first_twice.prefix_exit"), "{error}");
    check().expect("a refused selected proof must restore the ordinary policy");
    let error = without_implicit_solve_for_claim("missing.claim", check).unwrap_err();
    assert!(
        error.contains("did not visit selected proof `missing.claim`"),
        "{error}"
    );
    let error = without_implicit_solve(|| {
        without_implicit_solve_for_claim("set_first_twice.final_exit", check)
    })
    .unwrap_err();
    assert!(
        error.contains("set_first_twice.prefix_exit"),
        "the unconditional strict scope must still reject an unexpanded neighbor: {error}"
    );
    check().expect("nested strict scopes must restore the ordinary policy");
}

/// A negative mdtest is a boundary of the entire audit, including runtime
/// discovery before smart-site inventory.
#[test]
fn audit_skips_expected_failure_before_runtime_inventory() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("mdtests/a_sidecar_conjunction_written_as_ampersands_names_and.md");
    run_audit(parse_arguments([path.display().to_string()]).unwrap()).unwrap();
}

/// Skipping a negative container must also precede C++ input preparation.
#[test]
fn audit_skips_expected_failure_before_preparing_inputs() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("negative.md");
    fs::write(&path, "```cpp filename=invalid.cpp function=invalid profile=normal_only\nthis is invalid C++\n```\n```click\ninvalid Click &&\n```\n```expect\nfail: invalid\n```\n").unwrap();
    run_audit(parse_arguments([path.display().to_string()]).unwrap()).unwrap();
}

/// A mixed selection still expands and checks its positive proof, and never
/// hides a positive container's syntax error behind the negative filter.
#[test]
fn audit_mixed_mdtests_checks_positive_sources() {
    let directory = tempfile::tempdir().unwrap();
    let negative = directory.path().join("negative.md");
    let positive = directory.path().join("positive.md");
    fs::write(
        &negative,
        "```click\ninvalid Click &&\n```\n```expect\nfail: invalid\n```\n",
    )
    .unwrap();
    fs::write(
        &positive,
        "```click\ntheorem identity() { ensures 0 == 0 by close(); }\n```\n```expect\npass\n```\n",
    )
    .unwrap();
    let sites = inventory_sites(&audit_targets(directory.path()).unwrap()).unwrap();
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].click_path, fs::canonicalize(&positive).unwrap());
    run_audit(parse_arguments([directory.path().display().to_string()]).unwrap()).unwrap();
    fs::write(
        &positive,
        "```click\ntheorem bad() { ensures true && true by close(); }\n```\n```expect\npass\n```\n",
    )
    .unwrap();
    let error =
        run_audit(parse_arguments([directory.path().display().to_string()]).unwrap()).unwrap_err();
    assert!(
        error.contains("Click writes conjunction as `and`"),
        "{error}"
    );
}

#[test]
fn keep_going_audits_other_files_after_an_inventory_failure() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("broken.md"),
        "```click\ntheorem bad() { ensures true && true by close(); }\n```\n```expect\npass\n```\n",
    )
    .unwrap();
    let healthy = directory.path().join("healthy.md");
    fs::write(
        &healthy,
        "```click\ntheorem healthy() { ensures 0 == 0 by close(); }\n```\n```expect\npass\n```\n",
    )
    .unwrap();
    let arguments = || {
        parse_arguments([
            "--keep-going".to_string(),
            directory.path().display().to_string(),
        ])
        .unwrap()
    };
    let inventory = prepare_audit(&arguments(), Instant::now() + Duration::from_secs(30))
        .expect("a broken file must not abort the inventory");
    assert_eq!(inventory.discovery_failures.len(), 1);
    assert!(inventory.discovery_failures[0].contains("broken.md"));
    assert!(inventory.discovery_failures[0].contains("Click writes conjunction as `and`"));
    assert_eq!(inventory.scoped_sites.len(), 1);
    assert_eq!(
        inventory.scoped_sites[0].click_path,
        fs::canonicalize(healthy).unwrap()
    );
    assert_eq!(
        run_audit(arguments()).unwrap_err(),
        "1 expansion audit check(s) failed"
    );
}

/// The session budget bounds one source's inventory, as it bounds one
/// session's initialization: sources that together spend more than it are
/// still each inventoried.
#[test]
#[ignore = "nightly: 0.8s debug, three audit inventories and discovery"]
fn inventory_budget_applies_to_each_source() {
    let directory = tempfile::tempdir().unwrap();
    let mut paths = Vec::new();
    for index in 0..3 {
        let path = directory.path().join(format!("unit{index}.md"));
        fs::write(
            &path,
            format!(
                "```click\ntheorem identity{index}() {{ ensures 0 == 0 by close(); }}\n```\n\
                 ```expect\npass\n```\n"
            ),
        )
        .unwrap();
        paths.push(path);
    }
    // The first inventory also loads the standard library.
    inventory_sites(std::slice::from_ref(&paths[0])).unwrap();
    let (sites, one_source) = click::instrumentation::measure_deterministic_work(|| {
        let source = load_audit_source(&paths[1]).unwrap();
        click::surface::selected_thread_runtime(&source.click_source).unwrap();
        inventory_sites(std::slice::from_ref(&paths[1])).unwrap()
    });
    assert_eq!(sites.len(), 1);
    assert!(one_source > 0);
    let mut arguments = parse_arguments([
        "--keep-going".to_string(),
        directory.path().display().to_string(),
    ])
    .unwrap();
    // Under the old whole-run inventory budget, the three sources together
    // exhausted this, and the later ones failed their inventory.
    arguments.limits.session.work = 2 * one_source;
    let inventory = prepare_audit(&arguments, Instant::now() + Duration::from_secs(60)).unwrap();
    assert!(
        !inventory
            .discovery_failures
            .iter()
            .any(|failure| failure.contains("inventory")),
        "{:?}",
        inventory.discovery_failures
    );
    assert_eq!(
        inventory
            .scoped_sites
            .iter()
            .filter(|site| site.claim.contains("identity"))
            .count(),
        paths.len()
    );
}

#[test]
#[ignore = "nightly: body-safety alias expansion and retained/cold audits"]
fn body_safety_proofs_have_one_auditable_source_site() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("mixed.md");
    fs::write(
        &path,
        "```c filename=mixed.c\nint32 read_byte(uint8 *p) { return p[0]; }\n```\n```click\nverifying \"mixed.c\";\nint32 read_byte(uint8 *p) { views p[0..1]; }\ntheorem healthy() { ensures 0 == 0 by close(); }\n```\n```expect\npass\n```\n",
    )
    .unwrap();
    let arguments =
        || parse_arguments(["--keep-going".to_string(), path.display().to_string()]).unwrap();
    let inventory = prepare_audit(&arguments(), Instant::now() + Duration::from_secs(30)).unwrap();
    assert!(
        inventory.discovery_failures.is_empty(),
        "{:?}",
        inventory.discovery_failures
    );
    assert_eq!(
        inventory.scoped_sites.len(),
        2,
        "the synthetic ensure label must not duplicate the body-safety site"
    );
    assert!(
        inventory
            .scoped_sites
            .iter()
            .any(|site| site.claim == "read_byte.contract")
    );
    assert!(
        inventory
            .scoped_sites
            .iter()
            .any(|site| site.claim == "healthy.ensures_0")
    );
    let source = load_audit_source(&path).unwrap();
    let VerificationInput::Bundle(inputs) = &source.inputs else {
        panic!("the fixture has ordinary C sources");
    };
    let position =
        claim_source_position_for_source(&source, &source.click_source, "read_byte.body_safety")
            .unwrap();
    assert_eq!(
        verify_c_sources_at(
            &source.click_source,
            &source_refs(inputs),
            position.line,
            position.column
        )
        .unwrap()
        .len(),
        1
    );
    assert!(
        verify_c_sources(&source.click_source, &source_refs(inputs))
            .unwrap()
            .is_empty(),
        "whole-source verification keeps its existing implicit body-safety result behavior"
    );
    let written = source.click_source.replace(
        "views p[0..1]; }",
        "views p[0..1]; } by { step_until(function.exit); close(); }",
    );
    let written_sites = c_smart_tactic_source_sites(&written, &source_refs(inputs)).unwrap();
    assert_eq!(
        written_sites
            .iter()
            .filter(|site| site.claim_label == "read_byte.contract")
            .count(),
        2,
        "written grouped proofs keep their existing contract label"
    );
    let expanded = expand_claim_with_source(&path, &source, "read_byte.body_safety").unwrap();
    assert_ne!(expanded, source.container_source);
    assert_eq!(
        expanded,
        expand_claim_with_source(&path, &source, "read_byte.ensures_0").unwrap()
    );
    assert_eq!(
        expanded,
        expand_claim_with_source(&path, &source, "read_byte.contract").unwrap()
    );
    run_audit(arguments()).expect("body safety and the neighboring theorem must both audit");
    run_audit(parse_arguments([path.display().to_string()]).unwrap()).unwrap();
    assert!(
        prepare_audit(&arguments(), Instant::now())
            .err()
            .expect("the deadline must still stop discovery")
            .contains(RUN_LIMIT_EXHAUSTED)
    );
}

/// A written script may already close every obligation before its implicit
/// tail is observed. A byte-identical expansion must still satisfy the full
/// audit, including cold verification with implicit solving disabled.
#[test]
fn a_fully_explicit_script_has_an_auditable_fixed_point() {
    // The written steps discharge the claim before automatic finalization.
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("explicit_identity.md");
    fs::write(
        &path,
        "```c filename=explicit_identity.c\nint32 identity(int32 x) {\n    return x;\n}\n```\n\n\
         ```click\nverifying \"explicit_identity.c\";\n\n\
         int32 identity(int32 x) {\n    ensures result == x;\n} by {\n    step();\n    \
         close();\n}\n```\n\n\
         ```expect\npass\n```\n",
    )
    .unwrap();
    let source = load_audit_source(&path).unwrap();
    let claim = "identity.contract";
    click::surface::without_implicit_solve(|| {
        verify_rewritten_with_inputs(&source, claim, &source.click_source)
    })
    .expect("the original script is already explicit");
    assert_eq!(
        expand_claim_with_source(&path, &source, claim).unwrap(),
        source.container_source
    );
    let arguments = parse_arguments([
        "--claim".to_string(),
        claim.to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).expect("an already explicit proof is a valid fixed point");
}

#[test]
#[ignore = "nightly: pthread handle copy expansion and cold replay"]
fn pthread_handle_copies_expand_and_cold_replay() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/modeled_pthread_copied_handle.md");
    let arguments = parse_arguments([
        "--claim".to_string(),
        "run.contract".to_string(),
        path.display().to_string(),
    ])
    .unwrap();
    run_audit(arguments).unwrap();
}

/// A failing site's line names its container and reproduces the site; a
/// failing container's line reproduces the container.
#[test]
fn an_expansion_failure_line_reproduces_its_site() {
    assert_eq!(
        expansion_failure_line(
            "examples/arena/cells.click:12:5",
            "\nexpansion failed\nmore"
        ),
        "failed\tsite\texamples/arena/cells.click\texamples/arena/cells.click:12:5\texpansion failed\t\t\tclick audit expansion --claim examples/arena/cells.click:12:5 examples/arena/cells.click\n"
    );
    assert!(
        expansion_failure_line("mdtests/x.md", "session failed")
            .ends_with("\tclick audit expansion mdtests/x.md\n")
    );
}
