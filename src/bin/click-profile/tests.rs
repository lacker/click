use super::*;

#[test]
fn parses_timing_events_and_keeps_the_active_stack() {
    let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 2 execute class smart statement 4 source 5
click timing: started tactic example.contract 2 step class simple statement 4 source 5
click timing: tactic example.contract 2 step class simple statement 4 source 5 1.250000s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), true)
        .expect("the current timing format should parse");
    assert_eq!(profile.slow_steps.len(), 1);
    assert_eq!(profile.slow_steps[0].key.tactic_name, "step");
    assert_eq!(profile.slow_steps[0].key.category, TacticCategory::Simple);
    assert_eq!(profile.active.len(), 1);
    assert_eq!(profile.active[0].tactic_name, "execute");
    assert_eq!(profile.active[0].category, TacticCategory::Smart);
    assert!(profile.unknown_timing.is_empty());
}

#[test]
fn structured_timeout_attributes_interrupted_phase_and_preserves_completed_work() {
    let source = PathBuf::from("examples/sample.click");
    let completed = TacticEvent {
        claim: "sample.contract".to_string(),
        tactic_index: 0,
        tactic_name: "step".to_string(),
        class: "simple".to_string(),
        statement_index: 0,
        source_index: 0,
    };
    let events = vec![
        VerificationEvent::Source(source),
        VerificationEvent::PhaseFinished {
            name: "frontend",
            elapsed: Duration::from_millis(100),
        },
        VerificationEvent::TacticStarted(completed.clone()),
        VerificationEvent::TacticFinished {
            tactic: completed,
            elapsed: Duration::from_millis(10),
        },
        VerificationEvent::DeadlineExceeded(ActiveVerificationWork::Phase("certification")),
    ];
    let mut profile = profile_from_events("sample", &events, Thresholds::default(), true).unwrap();
    finish_time_accounting(&mut profile, Duration::from_secs(5));

    assert_eq!(profile.accounting.simple, Duration::from_millis(10));
    assert_eq!(profile.accounting.interrupted, Duration::from_millis(4890));
    assert_eq!(profile.accounting.process_driver(), Duration::ZERO);
    assert_eq!(
        profile.interrupted,
        Some(InterruptedWork::Phase("certification"))
    );

    let report = render_profiles(&[profile], Thresholds::default(), Duration::from_secs(5));
    assert!(report.contains("[PHASE] certification"), "{report}");
    assert!(report.contains("TIMEOUT DIAGNOSTIC"), "{report}");
    assert!(report.contains("INCOMPLETE TIMEOUT"), "{report}");
    assert!(
        report.contains("deadline interrupted `certification` work"),
        "{report}"
    );
    assert!(!report.contains("HEALTHY VOLUME"), "{report}");
}

/// The certification timing kinds added on 2026-07-30 share the stderr
/// stream with the tactic events. The profiler must skip them silently
/// and, crucially, must not count them as drift.
#[test]
fn recognizes_and_skips_the_certification_timing_kinds() {
    let output = r#"
click timing: source examples/sample.click
click timing: function example_function 0.512s
click timing: contract execution example_function 0.400000s
click timing: contract claims example_function 0.090000s
click timing: contract entry resources do not satisfy requirements
click timing: contract entry resources do not certify requirement safety
click timing: claim paths example_function prepared 12 in 0.030000s
click timing: claim example_function Ensure(4) 0.012000s
click timing: tactic example.contract 0 execute class smart statement 1 source 2 3.000000s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");

    assert_eq!(profile.slow_steps.len(), 1);
    assert_eq!(profile.slow_steps[0].key.tactic_name, "execute");
    assert_eq!(profile.work.source_files, 1);
    assert_eq!(profile.work.functions, 1);
    assert_eq!(profile.work.claims, 1);
    assert_eq!(profile.work.certification_paths, 12);
    assert!(
        profile.unknown_timing.is_empty(),
        "certification kinds must be recognized, not counted as drift: {:?}",
        profile.unknown_timing
    );
}

/// The report must be able to answer "is this proof smart-slow or
/// simple-slow overall", which means nested containers cannot double
/// count: a control container's own share is its time minus the steps it
/// ran, and the buckets plus the unattributed remainder equal the total.
#[test]
fn accounting_splits_the_run_into_exclusive_class_time() {
    let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 0 have class control statement 1 source 0
click timing: started tactic example.contract 1 simp class smart statement 1 source 1
click timing: tactic example.contract 1 simp class smart statement 1 source 1 3.000000s
click timing: started tactic example.contract 2 close_invariants class simple statement 1 source 2
click timing: tactic example.contract 2 close_invariants class simple statement 1 source 2 4.000000s
click timing: tactic example.contract 0 have class control statement 1 source 0 8.000000s
click timing: contract execution example_function 1.000000s
click timing: contract claims example_function 0.500000s
click timing: function example_function 12.000s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");

    assert!(
        profile.unknown_timing.is_empty(),
        "{:?}",
        profile.unknown_timing
    );
    assert_eq!(profile.accounting.total, Duration::from_secs(12));
    assert_eq!(profile.accounting.smart, Duration::from_secs(3));
    assert_eq!(profile.accounting.simple, Duration::from_secs(4));
    // 8s container minus the 3s + 4s it ran.
    assert_eq!(profile.accounting.control, Duration::from_secs(1));
    assert_eq!(
        profile.accounting.certification,
        Duration::from_millis(1_500)
    );
    assert_eq!(
        profile.accounting.verifier_core(),
        Duration::from_millis(2_500)
    );
    assert_eq!(profile.accounting.unattributed(), Duration::ZERO);
    assert!(profile.active.is_empty());
    assert_eq!(profile.slow_steps.len(), 2);
    assert!(profile.slow_steps.iter().any(|step| {
        step.key.category == TacticCategory::Smart && step.elapsed == Duration::from_secs(3)
    }));
    assert!(profile.slow_steps.iter().any(|step| {
        step.key.category == TacticCategory::Simple && step.elapsed == Duration::from_secs(4)
    }));
    assert!(
        profile
            .slow_steps
            .iter()
            .all(|step| step.key.category != TacticCategory::Control)
    );

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
    assert!(report.contains("TIME ACCOUNTING"), "{report}");
    assert!(report.contains("UNATTRIBUTED"), "{report}");
    assert!(report.contains("12.000s total"), "{report}");
}

#[test]
fn function_and_claim_attribution_reconciles_exclusive_time_once() {
    let output = r#"
click timing: source examples/sample.click
click timing: started tactic alpha.ensures_0 0 have class control statement 1 source 0
click timing: started tactic alpha.ensures_0 1 simp class smart statement 1 source 1
click timing: tactic alpha.ensures_0 1 simp class smart statement 1 source 1 3.000000s
click timing: started tactic alpha.ensures_0 2 close_invariants class simple statement 1 source 2
click timing: tactic alpha.ensures_0 2 close_invariants class simple statement 1 source 2 4.000000s
click timing: tactic alpha.ensures_0 0 have class control statement 1 source 0 8.000000s
click timing: contract execution alpha 1.000000s
click timing: claim paths alpha prepared 2 in 0.250000s
click timing: claim alpha Ensure(0) 0.500000s
click timing: contract claims alpha 1.000000s
click timing: function alpha 12.000000s
click timing: tactic beta.ensures_0 0 step class simple statement 1 source 0 2.000000s
click timing: contract execution beta 0.500000s
click timing: claim beta Ensure(0) 0.250000s
click timing: contract claims beta 0.500000s
click timing: function beta 4.000000s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), false).unwrap();

    for function in profile.attribution.values() {
        assert_eq!(
            function
                .claims
                .values()
                .map(|claim| claim.buckets.total())
                .sum::<Duration>(),
            function.buckets.total(),
        );
    }
    assert_eq!(
        profile.attribution["alpha"].buckets,
        AttributedBuckets {
            simple: Duration::from_secs(4),
            smart: Duration::from_secs(3),
            control: Duration::from_secs(1),
            certification: Duration::from_secs(2),
            verifier_core: Duration::from_secs(2),
            smart_attempts: 1,
        }
    );

    let report = render_profiles_with_top(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT, 2);
    assert!(
        report.contains("TOP FUNCTIONS / CLAIMS BY EXCLUSIVE TIME"),
        "{report}"
    );
    assert!(report.find("FUNCTION alpha").unwrap() < report.find("FUNCTION beta").unwrap());
    assert!(report.contains("<shared verifier work>"), "{report}");
}

#[test]
fn profile_distinguishes_one_smart_site_from_two_dynamic_attempts() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic alpha.ensures_0 0 simp class smart statement 1 source 0 0.010000s
click timing: tactic alpha.ensures_0 0 simp class smart statement 1 source 0 0.020000s
click timing: function alpha 0.030000s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false).unwrap();
    profile.work.smart_source_sites = 1;

    let claim = &profile.attribution["alpha"].claims["alpha.ensures_0"];
    assert_eq!(claim.smart_sites.len(), 1);
    assert_eq!(claim.buckets.smart_attempts, 2);
    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
    assert!(
        report.contains("1 unique source sites,      2 dynamic attempts"),
        "{report}"
    );
    assert!(
        report.contains("paths or repeated claim execution"),
        "{report}"
    );
    assert!(report.contains("smart 2/1 attempts/sites"), "{report}");
}

/// Function-total time outside tactics is named verifier orchestration,
/// not a mysterious residual.
#[test]
fn function_residual_is_reported_as_verifier_core() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 simp class smart statement 1 source 0 1.000000s
click timing: function example_function 20.000s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    assert!(
        profile.slow_steps.is_empty(),
        "nothing here crosses a threshold; that is the point"
    );
    assert_eq!(profile.accounting.verifier_core(), Duration::from_secs(19));
    assert_eq!(profile.accounting.unattributed(), Duration::ZERO);

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(report.contains("VERIFIER CORE"), "{report}");
}

/// A proof that fails never reports a function total, and a failing proof
/// is exactly the kind worth profiling. Its split must still be readable.
#[test]
fn a_failed_run_still_reports_its_class_split() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 simp class smart statement 1 source 0 6.000000s
click timing: tactic example.contract 1 fold class simple statement 1 source 1 2.000000s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.verification_failure = Some("could not certify the claim".to_string());
    for step in &mut profile.slow_steps {
        step.key.position = Some(SourcePosition { line: 1, column: 1 });
    }

    assert_eq!(profile.accounting.total, Duration::ZERO);
    assert_eq!(profile.accounting.denominator(), Duration::from_secs(8));

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(report.contains("TIME ACCOUNTING"), "{report}");
    assert!(report.contains("8.000s total measured"), "{report}");
    assert!(report.contains("SMART      6.000s   75.0%"), "{report}");
    assert!(report.contains("SIMPLE      2.000s   25.0%"), "{report}");
}

#[test]
fn whole_run_accounting_includes_setup_phases_and_wall_residual() {
    let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.500000s
click timing: phase environment 1.000000s
click timing: tactic example.contract 0 step class simple statement 1 source 0 0.200000s
click timing: contract execution example_function 1.000000s
click timing: contract claims example_function 1.000000s
click timing: function example_function 2.200s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.accounting.wall_total = Duration::from_secs(4);

    assert_eq!(profile.accounting.frontend, Duration::from_millis(500));
    assert_eq!(profile.accounting.environment, Duration::from_secs(1));
    assert_eq!(profile.accounting.simple, Duration::from_millis(200));
    assert_eq!(profile.accounting.certification, Duration::from_secs(2));
    assert_eq!(
        profile.accounting.process_driver(),
        Duration::from_millis(300)
    );
    assert_eq!(profile.accounting.unattributed(), Duration::ZERO);
    assert_eq!(profile.work.source_files, 1);
    assert_eq!(profile.work.functions, 1);
    assert_eq!(profile.work.c_transitions.count, 1);
    assert_eq!(profile.work.c_transitions.total, Duration::from_millis(200));

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
    assert!(report.contains("4.000s total"), "{report}");
    assert!(report.contains("FRONTEND"), "{report}");
    assert!(report.contains("ENVIRONMENT"), "{report}");
    assert!(report.contains("UNATTRIBUTED"), "{report}");
    assert!(report.contains("WORK AND THROUGHPUT"), "{report}");
    assert!(report.contains("C TRANSITIONS"), "{report}");
    assert!(report.contains("SIMPLE BY KIND"), "{report}");
    assert!(!report.contains("UNEXPLAINED"), "{report}");
}

#[test]
fn small_wall_residual_is_named_process_driver_time() {
    let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.080000s
click timing: function example_function 0.080s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.accounting.wall_total = Duration::from_millis(180);

    assert_eq!(
        profile.accounting.process_driver(),
        Duration::from_millis(20)
    );
    assert_eq!(profile.accounting.unattributed(), Duration::ZERO);
    assert!(!profile.accounting.materially_unattributed());
}

#[test]
fn material_wall_residual_is_still_named_process_driver_time() {
    let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.700000s
click timing: function example_function 0.700s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.accounting.wall_total = Duration::from_millis(1_700);

    assert_eq!(
        profile.accounting.process_driver(),
        Duration::from_millis(300)
    );
    assert_eq!(profile.accounting.unattributed(), Duration::ZERO);
    assert!(!profile.accounting.materially_unattributed());
}

#[test]
fn one_second_wall_residual_is_named_process_driver_time() {
    let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 99.000000s
click timing: function example_function 99.000s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.accounting.wall_total = Duration::from_secs(199);

    assert_eq!(profile.accounting.process_driver(), Duration::from_secs(1));
    assert_eq!(profile.accounting.unattributed(), Duration::ZERO);
    assert!(!profile.accounting.materially_unattributed());
}

/// The kinds the accounting consumes are load-bearing now, so a drifted
/// one is a loud error rather than a silently missing bucket.
#[test]
fn drifted_accounting_timing_lines_are_a_loud_error() {
    for drifted in [
        "click timing: function example_function twelve",
        "click timing: contract execution example_function 1.0",
        "click timing: contract claims example_function",
        "click timing: phase frontend eventually",
    ] {
        let output = format!("click timing: source examples/sample.click\n{drifted}\n");
        let message = parse_profile("sample", &output, Thresholds::default(), false)
            .expect_err(&format!("drifted line should be loud: {drifted}"));
        assert!(message.contains("has drifted"), "{message}");
    }
}

#[test]
fn retired_internal_tactic_names_are_timing_protocol_drift() {
    let output = "click timing: source examples/sample.click\n\
click timing: tactic example.contract 0 execute_step class smart statement 1 source 0 3.000000s\n";
    let message = parse_profile("sample", output, Thresholds::default(), false).unwrap_err();
    assert!(message.contains("timing format"), "{message}");
}

/// A step the verifier planned itself can name a tactic index the surface
/// proof does not have. That must cost the step its location, not the
/// whole profile — the proofs worth profiling are exactly the ones whose
/// loop phases are auto-planned.
#[test]
fn steps_without_a_source_location_are_reported_not_fatal() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 7 close_invariants class simple statement 3 source 7 4.000000s
click timing: function example_function 4.000s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.unresolved_positions.insert(
        "`example.contract` has no source tactic occurrence 7".to_string(),
        1,
    );

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(
        report.contains("STEPS WITHOUT A SOURCE LOCATION"),
        "{report}"
    );
    assert!(
        report.contains("examples/sample.click (no source location)"),
        "{report}"
    );
    assert!(report.contains("no source tactic occurrence 7"), "{report}");
    assert!(report.contains("4.000s"), "{report}");
}

#[test]
fn unrecognized_timing_kinds_are_counted_and_reported() {
    let output = r#"
click timing: source examples/sample.click
click timing: gadget alpha 1.000000s
click timing: gadget beta 2.000000s
click timing: widget 0.5s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("unknown kinds are a warning, not a parse failure");

    assert_eq!(profile.unknown_timing.len(), 2);
    assert_eq!(profile.unknown_timing["gadget"].count, 2);
    assert_eq!(
        profile.unknown_timing["gadget"].example,
        "click timing: gadget alpha 1.000000s"
    );
    assert_eq!(profile.unknown_timing["widget"].count, 1);

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(report.contains("UNRECOGNIZED TIMING LINES"));
    assert!(report.contains("2 lines of kind `gadget`"));
    assert!(report.contains("1 line of kind `widget`"));
    assert!(report.contains("click timing: gadget alpha 1.000000s"));
    assert!(
        report.contains("this green is not trustworthy"),
        "a report that skipped timing lines must not read as clean:\n{report}"
    );
    assert!(
        !report
            .contains("NEXT: no completed smart expansion candidates or simple engine bottlenecks")
    );
}

/// Drift in the kinds the profile is built from is a false green, not a
/// warning: the report would show no slow steps because it understood
/// none. These must fail loudly.
#[test]
fn drifted_tactic_timing_lines_are_a_loud_error() {
    for drifted in [
        // An extra trailing field.
        "click timing: tactic example.contract 0 step class simple statement 1 source 2 nested 3 1.000000s",
        // A renamed structural keyword.
        "click timing: tactic example.contract 0 step kind simple statement 1 source 2 1.000000s",
        // An unknown class.
        "click timing: tactic example.contract 0 step class hybrid statement 1 source 2 1.000000s",
        // A non-numeric elapsed time.
        "click timing: tactic example.contract 0 step class simple statement 1 source 2 slows",
        // The started variant, with a dropped field.
        "click timing: started tactic example.contract 0 step class simple statement 1 source",
        // An empty source path.
        "click timing: source ",
    ] {
        let output = format!("click timing: source examples/sample.click\n{drifted}\n");
        let message = parse_profile("sample", &output, Thresholds::default(), false)
            .expect_err(&format!("drifted line should be loud: {drifted}"));
        assert!(message.contains("has drifted"), "{message}");
        assert!(message.contains(drifted.trim_end()), "{message}");
    }
}

#[test]
fn finished_tactic_lines_tolerate_extra_whitespace_and_precision() {
    let output = "click timing: source examples/sample.click\n\
                      click timing:  tactic  example.contract 0 step class simple statement 1 source 2   0.75s  \n";
    let profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("whitespace variation is not format drift");

    assert_eq!(profile.slow_steps.len(), 1);
    assert_eq!(profile.slow_steps[0].elapsed, Duration::from_millis(750));
}

/// An example project directory carries a `README.md`; only a directory
/// with no Click sidecar under it is a directory of mdtests.
#[test]
fn targets_prefer_example_projects_over_stray_markdown() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let mdtest = manifest.join("mdtests/count_to_three_loop_invariants.md");
    assert_eq!(
        profile_targets(&mdtest),
        Ok(vec![mdtest.clone()]),
        "a `.md` argument names one mdtest"
    );

    let projects = profile_targets(&manifest.join("examples/input-cursor"))
        .expect("an example project with a README is still a project");
    assert_eq!(projects.len(), 1);
    assert!(projects[0].ends_with("input-cursor"), "{projects:?}");

    let mdtests = profile_targets(&manifest.join("mdtests"))
        .expect("a directory of markdown tests profiles all of them");
    assert!(mdtests.len() > 1);
    assert!(
        mdtests.iter().all(|path| looks_like_mdtest(path)),
        "{mdtests:?}"
    );

    let sidecar = manifest.join("examples/input-cursor/input_cursor.click");
    assert_eq!(
        profile_targets(&sidecar),
        Ok(vec![sidecar.clone()]),
        "a direct sidecar target is needed to profile an expanded artifact"
    );
}

/// Quarantine is a property of the gate, not of the file, so the profiler
/// must be able to extract and profile a quarantined mdtest.
#[test]
fn quarantined_mdtests_are_profileable() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/bubble_sort3_two_pass_sorted.md");
    let source = load_profiled_source(&path).expect("a quarantined mdtest still extracts");

    assert!(source.click_source.contains("bubble_sort3_two_pass"));
    assert!(!source.c_sources.is_empty());
    assert!(
        source.line_offset > 0,
        "positions inside an mdtest sidecar must be offset to the markdown file"
    );
}

#[test]
fn parses_profile_arguments() {
    assert_eq!(
        parse_arguments([
            "--simple-threshold".to_string(),
            "250ms".to_string(),
            "--smart-threshold".to_string(),
            "3s".to_string(),
            "--time-limit".to_string(),
            "2m".to_string(),
            "examples".to_string(),
        ]),
        Ok(Arguments {
            path: PathBuf::from("examples"),
            thresholds: Thresholds {
                smart: Duration::from_secs(3),
                simple: Duration::from_millis(250),
                control: Duration::from_secs(2),
            },
            time_limit: Duration::from_secs(120),
            top_attribution_rows: DEFAULT_TOP_ATTRIBUTION_ROWS,
        })
    );
}

#[test]
fn end_of_options_accepts_a_dash_prefixed_target() {
    let arguments = parse_arguments(["--".to_string(), "-example.click".to_string()]).unwrap();
    assert_eq!(arguments.path, PathBuf::from("-example.click"));
}

#[test]
fn generated_commands_quote_locations_and_artifacts() {
    let key = StepKey {
        source_path: PathBuf::from("examples/it's spaced.click"),
        claim: "claim".to_string(),
        tactic_index: 0,
        source_index: 0,
        tactic_name: "simp".to_string(),
        category: TacticCategory::Smart,
        statement_index: 0,
        position: None,
    };
    let mut output = String::new();
    render_expansion_command(
        &mut output,
        &key,
        SourcePosition { line: 2, column: 3 },
        Thresholds::default(),
        DEFAULT_TIME_LIMIT,
    );
    assert!(
        output.contains("'examples/it'\\''s spaced.click:2:3'"),
        "{output}"
    );
    assert!(
        output.contains("'examples/it'\\''s spaced.expanded.click'"),
        "{output}"
    );
}

#[test]
fn common_threshold_sets_every_tactic_class() {
    let arguments = parse_arguments([
        "--threshold".to_string(),
        "750ms".to_string(),
        "examples".to_string(),
    ])
    .expect("common threshold should parse");

    assert_eq!(
        arguments.thresholds,
        Thresholds {
            smart: Duration::from_millis(750),
            simple: Duration::from_millis(750),
            control: Duration::from_millis(750),
        }
    );
    assert_eq!(arguments.time_limit, DEFAULT_TIME_LIMIT);
    assert_eq!(arguments.top_attribution_rows, DEFAULT_TOP_ATTRIBUTION_ROWS);
}

#[test]
fn top_attribution_rows_are_configurable_and_positive() {
    let arguments =
        parse_arguments(["--top".to_string(), "3".to_string(), "examples".to_string()]).unwrap();
    assert_eq!(arguments.top_attribution_rows, 3);
    assert!(
        parse_arguments(["--top".to_string(), "0".to_string(), "examples".to_string(),]).is_err()
    );
}

#[test]
fn report_separates_actions_and_only_suggests_expanding_smart_tactics() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 step class simple statement 1 source 10 0.750000s
click timing: tactic example.contract 1 execute class smart statement 2 source 20 2.500000s
click timing: tactic example.contract 2 have class control statement 3 source 30 2.100000s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    for (index, step) in profile.slow_steps.iter_mut().enumerate() {
        step.key.position = Some(SourcePosition {
            line: index + 10,
            column: 5,
        });
    }

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(report.contains("SIMPLE — FIX THE ENGINE; DO NOT EXPAND"));
    assert!(report.contains("WARNING: expanding an enclosing smart tactic is not a fix"));
    assert!(report.contains("SMART — EXPAND ONLY FROM VERIFIED PROOFS"));
    assert!(report.contains("CONTROL — INSPECT NESTED STEPS"));
    assert!(report.contains("NEXT: fix or reduce the SIMPLE bottleneck first"));
    assert_eq!(report.matches("expand: click expand").count(), 1);
    assert!(report.contains("--time-limit 1m"));
    assert!(report.contains("sample.expanded.click"), "{report}");
    assert!(report.contains("verify: click verify"), "{report}");
    assert!(report.contains("reprofile: click profile"), "{report}");
    assert!(report.contains("--smart-threshold 2s"), "{report}");
}

#[test]
fn diagnoses_mixed_engine_search_certification_and_setup_findings() {
    let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.300000s
click timing: phase environment 0.010000s
click timing: tactic example.contract 0 step class simple statement 1 source 0 0.100000s
click timing: tactic example.contract 1 fold class simple statement 1 source 1 0.100000s
click timing: tactic example.contract 2 unfold class simple statement 1 source 2 0.100000s
click timing: tactic example.contract 3 simp class smart statement 1 source 3 3.000000s
click timing: contract execution example_function 1.000000s
click timing: contract claims example_function 1.000000s
click timing: claim paths example_function prepared 1 in 0.100000s
click timing: claim example_function Ensure(0) 0.100000s
click timing: function example_function 5.300s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.accounting.wall_total = Duration::from_secs(7);

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
    for diagnosis in [
        "SIMPLE ENGINE BUG",
        "SMART HOTSPOT",
        "CERTIFICATION BOTTLENECK",
        "SETUP BOTTLENECK",
    ] {
        assert!(report.contains(diagnosis), "missing {diagnosis}:\n{report}");
    }
    assert!(report.contains("PROCESS/DRIVER"), "{report}");
    assert!(!report.contains("UNEXPLAINED"), "{report}");
}

#[test]
fn diagnoses_large_healthy_aggregate_as_volume() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 simp class smart statement 1 source 0 0.400000s
click timing: tactic example.contract 1 simp class smart statement 1 source 1 0.400000s
click timing: tactic example.contract 2 simp class smart statement 1 source 2 0.400000s
click timing: function example_function 1.200s
"#;
    let profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
    assert!(report.contains("HEALTHY VOLUME"), "{report}");
    assert!(
        report.contains("NEXT: measured cost is HEALTHY VOLUME"),
        "{report}"
    );
}

#[test]
fn slow_failed_smart_search_is_not_an_expansion_candidate() {
    let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 0 simp class smart statement 1 source 0
click timing: tactic example.contract 0 simp class smart statement 1 source 0 3.000000s
click timing: failed tactic example.contract 0 simp class smart statement 1 source 0
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("a failed tactic outcome should parse");
    profile.slow_steps[0].key.position = Some(SourcePosition {
        line: 10,
        column: 5,
    });

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
    assert!(report.contains("SMART SEARCH LIMIT"), "{report}");
    assert!(report.contains("decompose the proof"), "{report}");
    assert!(
        report.contains("FAILED — no certificate to expand"),
        "{report}"
    );
    assert!(report.contains("0 succeeded,      1 failed"), "{report}");
    assert!(!report.contains("expand: click expand"), "{report}");
    assert!(report.contains("click-expand is not available"), "{report}");
    assert!(report.contains("decompose the failed"), "{report}");
}

#[test]
fn control_only_report_directs_attention_to_nested_steps() {
    let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 have class control statement 1 source 10 2.500000s
"#;
    let mut profile = parse_profile("sample", output, Thresholds::default(), false)
        .expect("the current timing format should parse");
    profile.slow_steps[0].key.position = Some(SourcePosition {
        line: 10,
        column: 5,
    });

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(report.contains("NEXT: inspect the nested timings inside the CONTROL container"));
    assert!(!report.contains("expand: click expand"));
}

#[test]
fn report_preserves_timings_when_another_project_fails_verification() {
    let mut successful = parse_profile(
        "successful",
        r#"
click timing: source examples/successful.click
click timing: tactic example.contract 0 execute class smart statement 1 source 10 2.500000s
"#,
        Thresholds::default(),
        false,
    )
    .expect("the current timing format should parse");
    successful.slow_steps[0].key.position = Some(SourcePosition {
        line: 12,
        column: 5,
    });
    let mut failed = parse_profile(
        "failed",
        "click timing: source examples/failed.click",
        Thresholds::default(),
        false,
    )
    .expect("the current timing format should parse");
    failed.verification_failure =
        Some("example sidecar failed: certificate did not replay".to_string());

    let report = render_profiles(
        &[failed, successful],
        Thresholds::default(),
        DEFAULT_TIME_LIMIT,
    );

    assert!(report.contains("VERIFICATION FAILURES"));
    assert!(report.contains("INCOMPLETE CORRECTNESS RUN"), "{report}");
    assert!(report.contains("certificate did not replay"));
    assert!(report.contains("examples/successful.click:12:5"));
    assert!(report.contains("fix the verification failure first"));
}

#[test]
fn failed_profile_records_hotspots_without_recommending_expansion() {
    let mut profile = parse_profile(
        "broken",
        r#"
click timing: source examples/broken.click
click timing: tactic example.contract 0 execute class smart statement 1 source 10 2.500000s
"#,
        Thresholds::default(),
        false,
    )
    .expect("the current timing format should parse");
    profile.slow_steps[0].key.position = Some(SourcePosition {
        line: 12,
        column: 5,
    });
    profile.verification_failure = Some("a later tactic failed".to_string());

    let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

    assert!(report.contains("INCOMPLETE CORRECTNESS RUN"), "{report}");
    assert!(report.contains("SMART HOTSPOT RECORDED"), "{report}");
    assert!(
        report.contains("INCOMPLETE RUN — restore verification before expansion"),
        "{report}"
    );
    assert!(
        report.contains("restore complete verification before expanding"),
        "{report}"
    );
    assert!(!report.contains("expand: click expand"), "{report}");
    assert!(
        report.contains("fix the verification failure first"),
        "{report}"
    );
}

#[test]
fn structured_events_do_not_require_text_parsing() {
    let events = vec![
        VerificationEvent::Source(PathBuf::from("example.click")),
        VerificationEvent::TacticFinished {
            tactic: TacticEvent {
                claim: "f.contract".to_string(),
                tactic_index: 0,
                tactic_name: "step".to_string(),
                class: "simple".to_string(),
                statement_index: 0,
                source_index: 0,
            },
            elapsed: Duration::from_secs(1),
        },
    ];
    let profile = profile_from_events("example", &events, Thresholds::default(), false)
        .expect("structured events should profile");
    assert_eq!(profile.slow_steps.len(), 1);
    assert!(profile.unknown_timing.is_empty());
}
