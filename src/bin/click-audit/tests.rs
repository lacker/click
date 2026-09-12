use super::*;
use click::surface::verify_c0_sources;

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
    assert_eq!(arguments.session_limit, Duration::from_secs(30));
    assert_eq!(arguments.expansion_limit, Duration::from_millis(250));
    assert_eq!(arguments.verification_limit, Duration::from_secs(120));
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
    let selected = select_claim_sites(&sites, &["alpha.ensures_0".to_string()]).unwrap();
    assert_eq!(selected.len(), 2);
    assert_eq!(selected[0].position.line, 1);
    assert_eq!(selected[1].position.line, 2);
    assert!(
        select_claim_sites(&sites, &["missing".to_string()])
            .unwrap_err()
            .contains("unknown audit claim")
    );

    let ambiguous = vec![
        site("a.click", "alpha.ensures_0", 1),
        site("b.click", "alpha.ensures_0", 1),
    ];
    assert!(
        select_claim_sites(&ambiguous, &["alpha.ensures_0".to_string()])
            .unwrap_err()
            .contains("ambiguous")
    );
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
        session_limit: Duration::from_secs(30),
        expansion_limit: Duration::from_secs(2),
        verification_limit: Duration::from_secs(3),
        performance_slack: Duration::from_millis(500),
        time_limit: Duration::from_secs(600),
        start_at: None,
        claims: vec!["example.ensures_0".to_string()],
        changed_since: Some("HEAD~1".to_string()),
        verbose: true,
        keep_going: false,
        max_sites: Some(1),
    };
    let location = SourceLocation {
        path: PathBuf::from("/tmp/example.click"),
        line: 12,
        column: 34,
    };
    assert_eq!(
        resume_command(&arguments, &location),
        "click audit --session-time-limit 30s --expansion-time-limit 2s \
             --verification-time-limit 3s --performance-slack 500ms --time-limit 10m \
             --verbose --claim example.ensures_0 --changed-since 'HEAD~1' --max-sites 1 \
             --start-at /tmp/example.click:12:34 'examples with spaces'"
    );
}

#[test]
fn end_of_options_accepts_a_dash_prefixed_target() {
    let arguments = parse_arguments(["--".to_string(), "-example.click".to_string()]).unwrap();
    assert_eq!(arguments.path, PathBuf::from("-example.click"));
}

#[test]
fn performance_comparison_requires_ratio_and_absolute_slack() {
    let slack = Duration::from_millis(500);
    assert!(!verification_regressed(
        Duration::from_secs(5),
        Duration::from_secs(9),
        slack,
    ));
    assert!(!verification_regressed(
        Duration::from_millis(100),
        Duration::from_millis(250),
        slack,
    ));
    assert!(verification_regressed(
        Duration::from_secs(1),
        Duration::from_millis(2_501),
        slack,
    ));
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
    let base = SiteTimings {
        expansion: Duration::from_millis(1),
        session_verification: Duration::from_millis(2),
        cold_verification: None,
        reexpansion: Duration::from_millis(5),
    };
    let skipped = render_site_timings(&base);
    assert!(skipped.contains("cold comparison not run"), "{skipped}");
    assert!(!skipped.contains("cold original 0"), "{skipped}");

    let measured = render_site_timings(&SiteTimings {
        cold_verification: Some((Duration::from_millis(3), Duration::from_millis(4))),
        ..base
    });
    assert!(measured.contains("cold original 3ms"), "{measured}");
    assert!(measured.contains("cold rewritten 4ms"), "{measured}");
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
    let limit = Duration::from_secs(10);
    let mut worker = AuditSessionWorker::start(&path, limit).unwrap();
    audit_site(
        site,
        &mut worker,
        limit,
        limit,
        Duration::from_secs(1),
        true,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("markdown audit retains extracted Click coordinates");
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
    branch {
        then { step(); simp(); }
        else {}
    }
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
        .find(|site| site.position.line == 7)
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
    let limit = Duration::from_secs(10);
    let mut worker = AuditSessionWorker::start(&path, limit).unwrap();
    // An active audit has already selected an immutable input. Any attempt to
    // reread the importer per tactic would now fail. A new audit must fail.
    fs::remove_file(directory.join("unit.i")).unwrap();
    for site in &sites {
        audit_site(
            site,
            &mut worker,
            limit,
            limit,
            Duration::from_secs(1),
            true,
            Instant::now() + Duration::from_secs(30),
        )
        .unwrap();
    }
    assert!(AuditSessionWorker::start(&path, limit).is_err());
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
    let click_source = r#"resource object_ref(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}

verifying "object_retain_many.c";

void object_retain_many(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires defined(1 + amount);
    owns object_ref(obj);
    produces amount of object_ref(obj);
} by {
    open(object_ref(obj)) {
        have 1 == obj->refs by simp;
        execute();
    }
    have 1 <= 1 + amount by {
        apply(int32_add_nonnegative_right_is_at_least_left(1, amount)) using {
            0 <= amount;
            defined(1 + amount);
        }
    }
    have amount <= 1 + amount by {
        apply(int32_add_nonnegative_left_is_at_least_right(1, amount)) using {
            defined(1 + amount);
        }
    }
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
    for needle in ["have 1 == obj->refs by simp;", "simp();\n}"] {
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
fn audit_reports_a_witness_the_expansion_cannot_spell() {
    // `mdtests/resource_witness_unfold_fold.md` reduced. The closer's
    // certificate has to cite the `where` fact of the resource's existential
    // witness, whose kernel value renders as the diagnostic
    // `symbolic-pointer:...@0`. Audit used to report only the parse error
    // that unparseable text produced (`unexpected character @`); the site now
    // fails with the language gap it actually hit.
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
    owns object(node);
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
    let error = expand_location(&format_location(&site_location(site)))
        .expect_err("the expansion needs a name the language does not give it");
    assert!(
        error.contains("the expansion needs a name for the witness `next` of `packed`"),
        "{error}"
    );
    assert!(
        !error.contains("unexpected character"),
        "the refusal should replace the parse error, not report it: {error}"
    );
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
        owns object(node);
        fact aligned(node, 8);
        let next: struct cell* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
        contains tagged(next);
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
        expanded.contains("if at(statement(5).entry, (load_uint64(byte_offset(node, 8)) & 1))"),
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
