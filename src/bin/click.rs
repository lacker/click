// Match the library trait-solver depth for its recursive shared proof types.
#![recursion_limit = "256"]

use std::env;

#[path = "click/git.rs"]
mod git;
#[path = "click/version_dispatch.rs"]
mod version_dispatch;
#[path = "click/version_manager.rs"]
mod version_manager;

#[path = "click-audit.rs"]
mod audit;
#[path = "click-capture.rs"]
mod capture;
#[path = "click-docs.rs"]
mod docs;
#[path = "click-expand.rs"]
mod expand;
#[path = "click-profile.rs"]
mod profile;
#[path = "click-verify.rs"]
mod verify;

const USAGE: &str = "\
usage: click <COMMAND> [OPTIONS]\n\n\
commands:\n  \
  verify   verify a sidecar, proof unit, project, or examples directory\n  \
  profile  measure verification and identify slow tactics\n  \
  expand   replace one smart tactic with its checked simple certificate\n  \
  audit    check expansion across a project or repository\n  \
  capture  record compiler output for verification\n  \
  docs     print the documentation for a tactic or topic\n  \
  upgrade  install the latest Click and make it the default\n  \
  add      add a language front end (cpp, rust); `languages` lists them\n  \
  remove   remove a language front end\n  \
  version  add, use, list, or remove installed Click versions";

fn main() {
    click::cli::enable_process_crash_containment();
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    match version_dispatch::maybe_dispatch("click", &arguments) {
        Ok(Some(status)) => std::process::exit(status),
        Ok(None) => {}
        Err(message) => report_error(message),
    }
    if let Err(message) = entry(arguments) {
        report_error(message);
    }
}

fn report_error(message: String) -> ! {
    // A Rust item prints as the path its sidecar writes.
    let message = click::surface::display_source_names(&message);
    if click::surface::VerificationOutcome::ALL
        .iter()
        .any(|outcome| {
            message
                .strip_prefix(outcome.label())
                .is_some_and(|rest| rest.starts_with(':') || rest.starts_with(" in `"))
        })
    {
        eprintln!("{message}");
    } else {
        eprintln!("click: {message}");
    }
    std::process::exit(1);
}

fn entry(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        return Err(USAGE.to_string());
    };
    if command == "--version" || command == "-V" {
        println!("click {}", env!("CARGO_PKG_VERSION"));
        return Ok(());
    }
    if command == "--help" || command == "-h" {
        println!("{USAGE}");
        return Ok(());
    }
    match command.as_str() {
        "verify" => verify::entry_with(arguments),
        "profile" => profile::entry_with(arguments),
        "expand" => expand::entry_with(arguments),
        "audit" => audit::entry_with(arguments),
        "capture" => capture::entry_with(arguments),
        "docs" => docs::entry_with(arguments),
        "version" | "upgrade" | "add" | "remove" | "languages" => {
            version_manager::entry_with(&command, arguments.collect())
        }
        _ => Err(format!("unknown command `{command}`\n{USAGE}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn rejects_unknown_subcommands() {
        let error = entry(["unknown".to_string()]).unwrap_err();
        assert!(error.contains("unknown command `unknown`"));
    }

    /// A view of a global cell borrows it for the call. A store into that
    /// cell must report the unproved separation from the borrowed range and
    /// locate the original C store.
    #[test]
    fn verify_refuses_a_store_into_a_viewed_global_with_the_separation_goal() {
        let directory =
            std::env::temp_dir().join(format!("click-viewed-global-store-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let sidecar = directory.join("viewed_global.click");
        fs::write(
            directory.join("viewed_global.c"),
            "int32 words[2];\nvoid set_second() { words[1] = 7; }\n",
        )
        .unwrap();
        fs::write(
            &sidecar,
            "verifying \"viewed_global.c\";\nvoid set_second() {\n    views words[1..2];\n    ensures words[1] == 7;\n}\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.contains("this write overlaps a live view"), "{error}");
        assert!(error.contains("\ngoal: separate("), "{error}");
        assert!(error.contains("words[1..2]"), "{error}");
        assert!(
            error.contains("C statement at viewed_global.c:2:21\n  `words[1] = 7;`"),
            "{error}"
        );
        assert!(!error.contains("outside the owned footprint"), "{error}");
        assert!(error.starts_with("unsuccessful search:"), "{error}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// A bare sidecar name has an empty `Path::parent`, which is not a
    /// directory. Every subcommand must resolve it against the current
    /// directory exactly as it resolves `./f.click`.
    ///
    /// This test changes the process working directory, which every other
    /// test sharing the process would observe. It therefore runs only under
    /// nextest's process-per-test mode, which `scripts/check.sh` always uses;
    /// the directory is restored before any assertion can unwind.
    #[test]
    fn every_cli_tool_accepts_a_bare_sidecar_name() {
        if std::env::var("NEXTEST_EXECUTION_MODE").as_deref() != Ok("process-per-test") {
            eprintln!("skipped: changing the working directory needs nextest process isolation");
            return;
        }
        let directory =
            std::env::temp_dir().join(format!("click-bare-sidecar-name-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("f.c"), "int32 f() { return 1; }\n").unwrap();
        fs::write(
            directory.join("f.click"),
            "verifying \"f.c\";\nint32 f() { ensures result == 1; }\n",
        )
        .unwrap();
        let original = std::env::current_dir().unwrap();
        std::env::set_current_dir(&directory).unwrap();
        let arguments = |words: &[&str]| {
            words
                .iter()
                .map(|word| word.to_string())
                .collect::<Vec<_>>()
        };
        let results = [
            entry(arguments(&["verify", "f.click"])),
            entry(arguments(&["verify", "f.click:2:13"])),
            entry(arguments(&["profile", "f.click"])),
            entry(arguments(&[
                "expand",
                "--claim",
                "f.ensures_0",
                "--output",
                "expanded.click",
                "f.click",
            ])),
            entry(arguments(&["audit", "--claim", "f.ensures_0", "f.click"])),
            entry(arguments(&["verify", "expanded.click"])),
        ];
        std::env::set_current_dir(original).unwrap();
        fs::remove_dir_all(&directory).unwrap();
        for result in results {
            result.unwrap();
        }
    }

    /// Each clause kind numbers its claims separately, so an `owns` clause
    /// does not renumber the `ensures` after it, and `--claim` (expand and
    /// audit) and `--trace-proof` also select a claim by a line its clause or
    /// proof covers.
    #[test]
    #[ignore = "nightly: 1.4s in the parallel gate"]
    fn claims_are_labelled_per_clause_kind_and_selected_by_line() {
        let directory =
            std::env::temp_dir().join(format!("click-claim-lines-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "void f(int *p) { p[0] = 1; }\nvoid g(int *p) { p[0] = 2; }\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\n\
             void f(int32* p) {\n\
             \x20   owns p[0..1];\n\
             \x20   ensures p[0] == 1 by {\n\
             \x20       step_until(function.exit);\n\
             \x20       solve();\n\
             \x20   }\n\
             }\n\
             void g(int32* p) { owns p[0..1]; ensures p[0] == 2; }\n",
        )
        .unwrap();
        let path = sidecar.display().to_string();
        let output = |name: &str| directory.join(name).display().to_string();
        let run = |words: &[&str]| entry(words.iter().map(|word| word.to_string()));
        let expand = |claim: &str, name: &str| {
            run(&["expand", "--claim", claim, "--output", &output(name), &path])
                .map(|()| fs::read_to_string(directory.join(name)).unwrap())
        };

        let by_label = expand("f.ensures_0", "ensures.click").unwrap();
        assert!(by_label.contains("    owns p[0..1];\n"), "{by_label}");
        assert!(
            !by_label.contains("step_until(function.exit);\n        solve();"),
            "{by_label}"
        );
        let by_line = expand(&format!("{path}:5"), "line.click").unwrap();
        assert_eq!(by_line, by_label);
        let owns = expand("f.owns_0", "owns.click").unwrap();
        assert!(owns.contains("    owns p[0..1] by {"), "{owns}");
        assert_eq!(
            expand(&format!("{path}:3:10"), "owns-line.click").unwrap(),
            owns
        );
        let shifted = expand("f.ensures_1", "missing.click").unwrap_err();
        assert!(
            shifted.contains("could not locate function claim `f.ensures_1`"),
            "{shifted}"
        );

        let uncovered = expand(&format!("{path}:1"), "none.click").unwrap_err();
        assert!(
            uncovered.contains(&format!(
                "{path}:1: no claim's clause or proof covers this line"
            )),
            "{uncovered}"
        );
        let grouped = expand(&format!("{path}:9"), "grouped.click").unwrap();
        assert_eq!(
            grouped,
            expand("g.contract", "grouped-label.click").unwrap()
        );
        run(&["verify", &output("grouped.click")]).unwrap();
        let elsewhere = expand("other.click:5", "elsewhere.click").unwrap_err();
        assert!(
            elsewhere.contains("`other.click:5` names a location in `other.click`"),
            "{elsewhere}"
        );

        run(&["audit", "--claim", &format!("{path}:9:40"), &path]).unwrap();
        let audit = run(&["audit", "--claim", &format!("{path}:1"), &path]).unwrap_err();
        assert!(
            audit.contains(&format!(
                "{path}:1: no claim's clause or proof covers this line"
            )),
            "{audit}"
        );
        run(&["verify", "--trace-proof", &format!("{path}:9:40"), &path]).unwrap();
        run(&["verify", "--trace-proof", &format!("{path}:4"), &path]).unwrap();
        let trace = run(&["verify", "--trace-proof", &format!("{path}:8"), &path]).unwrap_err();
        assert!(
            trace.contains(&format!(
                "{path}:8: no claim's clause or proof covers this line"
            )),
            "{trace}"
        );
        fs::remove_dir_all(&directory).unwrap();
    }

    /// A store Click steps over itself while preserving a loop's invariants
    /// is refused at the `loop` tactic that owns that phase, not at the
    /// claim's first tactic (the phase proof's own tactics count from zero),
    /// and the missing `can-store` is stated as the index bound over the
    /// source local with the facts consulted, never in kernel spelling.
    #[test]
    fn verify_names_the_loop_phase_and_index_bound_of_a_refused_loop_body_store() {
        let directory = std::env::temp_dir().join(format!(
            "click-loop-body-store-bound-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "int32 f() {\n    int32 items[4];\n    int32 i;\n    i = 0;\n    while (i < 5) {\n        items[i] = 7;\n        i = i + 1;\n    }\n    return 0;\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        let write_proof = |preserve: &str| {
            fs::write(
                &sidecar,
                format!(
                    "verifying \"f.c\";\nint32 f() {{\n    ensures result == 0;\n}} by {{\n    step(); step(); step();\n    loop {{ decreases 5 - i; invariant i >= 0; invariant i <= 4;{preserve} }}\n    step_until(function.exit); solve();\n}}\n"
                ),
            )
            .unwrap();
        };
        let bound = "  `step()` is missing prerequisite\n  the store to `items[i]` may write outside `items`\n  could not show `0 <= i && i < 4` from the facts `i <= 4`, `i >= 0`\n  C operation\n  *(items + i) = 7;\n  C statement at f.c:6:9\n  `items[i] = 7;`";

        write_proof("");
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.starts_with(&format!(
                "tactic error:\n  `f.contract` tactic 3 (`loop`), preserving the invariants through the loop body\n{bound}"
            )),
            "{error}"
        );
        assert!(
            error.contains("refused by: implicit step (loop preservation)"),
            "{error}"
        );

        write_proof(" maintain by { step(); step(); solve(); }");
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.starts_with(&format!(
                "tactic error:\n  `f.contract` tactic 3 (`loop`), `maintain` tactic 0\n{bound}"
            )),
            "{error}"
        );
        for kernel_spelling in ["can-store(", "state#", "local:items", "value A"] {
            assert!(!error.contains(kernel_spelling), "{error}");
        }
        fs::remove_dir_all(directory).unwrap();
    }

    /// A refused C step names the file, line, and column of the statement it
    /// checked and quotes the statement as written, not as Click lowered it:
    /// a struct-field store reads `items[i].x = 7;` rather than a byte
    /// offset, without its comment. A call names the call statement, an
    /// overflow names the statement whose arithmetic overflowed, a macro
    /// names and quotes its expansion site, and a header's inline body names
    /// the header line.
    #[test]
    fn verify_names_and_quotes_the_c_statement_a_step_refused() {
        let directory =
            std::env::temp_dir().join(format!("click-c-statement-sites-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("sum.h"),
            "#define SUM(a, b) ((a) + (b))\n\nstatic inline int32 twice(int32 x) {\n    int32 r;\n    r = x + x;\n    return r;\n}\n",
        )
        .unwrap();
        fs::write(
            directory.join("f.c"),
            "#include \"sum.h\"\n\nstruct item { int32 x; int32 y; };\n\nint32 store() {\n    struct item items[4];\n    int32 i;\n    i = 0;\n    while (i < 5) {\n        items[i].x = 7;   // the field store\n        i = i + 1;\n    }\n    return 0;\n}\n\nint32 add(int32 a, int32 b) {\n    int32 total;\n    total = a + b;\n    return total;\n}\n\nint32 callee(int32 n) {\n    return n;\n}\n\nint32 caller(int32 n) {\n    int32 r;\n    r = callee(n) + 1;\n    return r;\n}\n\nint32 summed(int32 a, int32 b) {\n    int32 total;\n    total = SUM(a, b);\n    return total;\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        let verify = |proof: &str| {
            fs::write(&sidecar, format!("verifying \"f.c\";\n{proof}")).unwrap();
            entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err()
        };
        let three_steps = "} by {\n    step(); step(); step(); solve();\n}\n";

        let store = verify(
            "int32 store() {\n    ensures result == 0;\n} by {\n    step(); step(); step();\n    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }\n    step_until(function.exit); solve();\n}\n",
        );
        assert!(
            store
                .contains("could not show `i < 4`\n  C statement at f.c:10:9\n  `items[i].x = 7;`"),
            "{store}"
        );
        assert!(!store.contains("the field store"), "{store}");

        let overflow = verify(&format!(
            "int32 add(int32 a, int32 b) {{\n    ensures result == a + b;\n{three_steps}"
        ));
        assert!(
            overflow.contains(
                "`step()` requires proof excluding signed overflow\n  C statement at f.c:18:5\n  `total = a + b;`\n"
            ),
            "{overflow}"
        );

        let call = verify(&format!(
            "int32 callee(int32 n) {{\n    requires n >= 0;\n    ensures result == n;\n}}\nint32 caller(int32 n) {{\n    ensures result == n + 1;\n{three_steps}"
        ));
        assert!(
            call.contains("`step()` requires an explicit prerequisite proof (precondition clause 1 of `callee`)"),
            "{call}"
        );
        assert!(
            call.contains("\n  C statement at f.c:28:5\n  `r = callee(n) + 1;`\n"),
            "{call}"
        );

        let macro_site = verify(&format!(
            "int32 summed(int32 a, int32 b) {{\n    ensures result == a + b;\n{three_steps}"
        ));
        assert!(
            macro_site.contains("\n  C statement at f.c:34:5\n  `total = SUM(a, b);`\n"),
            "{macro_site}"
        );

        let header = verify(&format!(
            "int32 twice(int32 x) {{\n    ensures result == x + x;\n{three_steps}"
        ));
        assert!(
            header.contains("\n  C statement at sum.h:5:5\n  `r = x + x;`\n"),
            "{header}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    // Refuse an explicit false fact after the original loop's two updates,
    // so the name regression stays negative when pointer reasoning improves.
    #[test]
    fn verify_trace_keeps_pointer_parameter_and_recorded_local_names() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("spell.c"),
            r#"unsigned long spell(const unsigned char *b, unsigned long n) {
    const unsigned char *v = b;
    unsigned long vl = n;
    while (4 <= vl) {
        v = v + 4;
        vl = vl - 4;
    }
    return vl;
}
"#,
        )
        .unwrap();
        let sidecar = directory.path().join("spell.click");
        fs::write(
            &sidecar,
            r#"verifying "spell.c";
uint64 spell(const uint8* b, uint64 n) {
    views b[0u64..n];
    ensures result < 4u64;
} by {
    step_until(loop(0).entry);
    loop {
        decreases vl;
        views b[0u64..n];
        invariant vl <= n;
        invariant v == b + (n - vl);
        maintain by {
            if 4u64 <= vl {
                step();
                step();
                have false by known();
            } else {
                step();
            }
        }
    }
    step_until(function.exit);
}
"#,
        )
        .unwrap();
        let trace = entry(vec![
            "verify".into(),
            "--trace-proof".into(),
            "spell".into(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(
            trace.contains("You must prove `false` in order to use the tactic `known()`."),
            "{trace}"
        );
        assert!(
            !trace.contains("semantic fact") && !trace.contains("proposition fact"),
            "{trace}"
        );
        assert!(trace.contains(" = b + uint64("), "{trace}");
        assert!(
            trace.contains(" = at(statement(2).statement(0).entry, v)"),
            "{trace}"
        );
        assert!(!trace.contains("external argument address base"), "{trace}");
        assert!(!trace.contains("<symbol "), "{trace}");
    }

    #[test]
    fn known_refusal_names_the_written_goal_at_its_program_point() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("read.c"),
            "int check(int* p) { return 0; }",
        )
        .unwrap();
        let sidecar = directory.path().join("read.click");
        fs::write(
            &sidecar,
            r#"verifying "read.c";
int32 check(int32* p) {
    ensures result == 0;
} by {
    have at(function.entry, defined(p[0])) by known();
}
"#,
        )
        .unwrap();
        let path = sidecar.display().to_string();
        for arguments in [
            vec!["verify".to_owned(), path.clone()],
            vec![
                "verify".to_owned(),
                "--trace-proof".to_owned(),
                "check".to_owned(),
                path,
            ],
        ] {
            let report = entry(arguments).unwrap_err();
            assert!(report.starts_with("tactic error:"), "{report}");
            assert!(report.contains("You must prove `at(function.entry, defined(p[0]))` in order to use the tactic `known()`."), "{report}");
            assert!(!report.contains("defined-read"), "{report}");
        }
    }

    #[test]
    fn verify_distinguishes_unsupported_callbacks_from_other_termination_failures() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (fixture, heading, detail) in [
            (
                "termination_callback_self_application_rejected.md",
                "unsupported:",
                "`spin` can call through a function pointer",
            ),
            (
                "termination_shadowed_callback_rejected.md",
                "incomplete proof:",
                "the recursive call to `spin` is ranked by no function-level `decreases` measure",
            ),
            (
                "program_entry_requires_loop_termination_before_completion.md",
                "incomplete proof:",
                "loop 0 declares no `decreases` measure",
            ),
            (
                "c_decreases_rejects_recursive_inline_helper.md",
                "incomplete proof:",
                "callee `step_down` has no termination evidence",
            ),
            (
                "diverges_named_contract_requires_marked_caller.md",
                "contract error:",
                "the named contract `Spinner` is declared `diverges`",
            ),
            (
                "loop_decreases_model_function_must_decrease.md",
                "unsuccessful search:",
                "remained open",
            ),
            (
                "termination_ordinary_proof_refuses_unproved_promise.md",
                "tactic error:",
                "in order to use the tactic `known()`",
            ),
            (
                "diverges_rejects_unjustified_marker.md",
                "contract error:",
                "remove the marker",
            ),
        ] {
            let report = entry([
                "verify".to_string(),
                root.join(fixture).display().to_string(),
            ])
            .unwrap_err();
            assert!(report.starts_with(heading), "{report}");
            assert!(report.contains(detail), "{report}");
        }
        let traced = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "program.termination".to_string(),
            root.join("termination_callback_self_application_rejected.md")
                .display()
                .to_string(),
        ])
        .unwrap_err();
        assert!(traced.starts_with("unsupported:"), "{traced}");
        assert!(traced.contains("proof refusal:"), "{traced}");
    }

    #[test]
    fn execution_region_depth_reports_unsupported() {
        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/proof_match_nesting_bound_named.md");
        let report = entry(["verify".to_string(), fixture.display().to_string()]).unwrap_err();
        assert!(report.starts_with("unsupported:"), "{report}");
        assert!(
            report.contains("checked execution-region recursion exceeds the supported depth"),
            "{report}"
        );
        assert!(!report.contains("tactic@"), "{report}");
    }

    #[test]
    fn contract_refinement_reports_the_specific_unsupported_capability() {
        let directory = tempfile::tempdir().unwrap();
        let sidecar = directory.path().join("refinement.click");
        for (contracts, callback, reason) in [
            (
                r#"contract int32 Raw(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
contract int32 Target(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}"#,
                "int32 (*)(int32)",
                "the source contract may throw",
            ),
            (
                r#"authorized resource Permit(pool: int32*) {}
contract void Raw(int32* pool) { ensures true; }
contract void Target(int32* pool) {
    owns authority(Permit(pool));
    owns Permit(pool);
    views *pool;
}"#,
                "void (*)(int32*)",
                "Click cannot frame a resource of family `population authority`",
            ),
        ] {
            fs::write(
                &sidecar,
                format!(
                    "{contracts}\n
theorem lift(callback: {callback}) {{
    requires Raw(callback);
    ensures Target(callback) by {{
        unfold(Raw(callback));
        unfold(Target(callback));
        solve();
    }}
}}
"
                ),
            )
            .unwrap();
            let report = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
            assert!(report.starts_with("unsupported:"), "{report}");
            assert!(report.contains(reason), "{report}");
        }
    }

    #[test]
    fn induction_in_an_execution_proof_reports_a_tactic_error() {
        let directory = tempfile::tempdir().unwrap();
        let sidecar = directory.path().join("f.click");
        fs::write(directory.path().join("f.c"), "int f(int n) { return n; }").unwrap();
        for prefix in ["", "step();"] {
            fs::write(
                &sidecar,
                format!(
                    "verifying \"f.c\";\nint32 f(int32 n) {{ requires n >= 0; ensures result == n; }} by {{\n    {prefix}\n    let ih = induct(n);\n    known();\n}}"
                ),
            )
            .unwrap();
            let report = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
            assert!(report.starts_with("tactic error:"), "{report}");
            assert!(
                report.contains("`induct` requires a pure theorem"),
                "{report}"
            );
            assert!(report.contains("let ih = induct(n);"), "{report}");
        }
    }

    #[test]
    fn a_nonrecursive_decreases_clause_is_a_contract_error() {
        let directory = tempfile::tempdir().unwrap();
        let sidecar = directory.path().join("f.click");
        fs::write(directory.path().join("f.c"), "int f(int n) { return n; }").unwrap();
        fs::write(
            &sidecar,
            r#"verifying "f.c";
int32 f(int32 n) {
    decreases n;
    ensures result == n;
}
"#,
        )
        .unwrap();
        let report = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(report.starts_with("contract error:"), "{report}");
        assert!(report.contains("has no recursive edge to rank"), "{report}");
    }

    #[test]
    fn invalid_loop_measures_report_contract_errors() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (name, detail) in [
            (
                "c_decreases_rejects_address_escaped_loop_measure.md",
                "has its address taken",
            ),
            (
                "loop_decreases_model_function_rejects_a_c_local.md",
                "reads a resource binder's model and also the C variable `n`",
            ),
        ] {
            let report = entry([
                "verify".to_owned(),
                fixtures.join(name).display().to_string(),
            ])
            .unwrap_err();
            assert!(report.starts_with("contract error:"), "{name}: {report}");
            assert!(report.contains(detail), "{name}: {report}");
        }
    }

    #[test]
    fn source_proof_tails_close_in_their_scope_and_expand_for_explicit_replay() {
        let source = r#"
            function successor(n: int32) -> int32 { n + 1 }
            theorem tail(x: int32, b: int32) {
                requires x == 3;
                ensures successor(x) == 4 by {
                    if b == 0 {
                        have successor(x) == 4 by { unfold(successor(x)); }
                    } else {
                        unfold(successor(x));
                    }
                }
            }
        "#;
        use click::surface::{verify_c_sources, without_implicit_solve};
        assert!(without_implicit_solve(|| verify_c_sources(source, &[])).is_err());
        verify_c_sources(source, &[]).unwrap();
        let expanded =
            click::surface::expand_c_claim_source_by_label(source, &[], "tail.ensures_0").unwrap();
        assert_ne!(expanded, source);
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    /// Every refused statement names its goal: the requirement it could not
    /// establish at its pre-state, in source names, with the explicit form
    /// that proves it. A refused call precondition, and an overflow that the
    /// implicit `solve` did not rule out, read alike; a trace repeats the goal
    /// in its proof refusal and leaves out verifier bookkeeping no proof can
    /// cite.
    #[test]
    fn verify_names_the_goal_of_a_refused_statement() {
        let directory =
            std::env::temp_dir().join(format!("click-statement-goals-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "int32 callee(int32 n) {\n    return n;\n}\n\nint32 caller(int32 n) {\n    int32 r;\n    r = callee(n) + 1;\n    return r;\n}\n\nint32 area(int32 w, int32 h) {\n    return w * h;\n}\n\nint32 frame(int32 w, int32 h) {\n    int32 inner = area(w, h);\n    return inner + 1;\n}\n\nint32 half(int32 x) {\n    return x / 2;\n}\n\nint32 halve_pair(int32 *p, int32 n) {\n    p[0] = n;\n    p[1] = half(p[0] * 2);\n    return p[1];\n}\n\nvoid set(int32 *p) {\n    p[0] = 1;\n}\n\nvoid lend_twice(int32 *p) {\n    set(p);\n    set(p + 1);\n}\n\nint32 next(int32 x) {\n    return x + 1;\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        let run = |proof: &str, arguments: &[&str]| {
            fs::write(&sidecar, format!("verifying \"f.c\";\n{proof}")).unwrap();
            let mut command = vec!["verify".to_string()];
            command.extend(arguments.iter().map(|argument| argument.to_string()));
            command.push(sidecar.display().to_string());
            entry(command).unwrap_err()
        };
        let help = "help: to prove the goal explicitly, step to this statement and prove it there with `have <goal> by { ... }`";

        let before_exit = run(
            "int32 half(int32 x) { ensures result == x / 2; } by { solve(); }",
            &[],
        );
        assert!(before_exit.starts_with("tactic error:\n"), "{before_exit}");
        assert!(
            before_exit.contains("step_until(function.exit)"),
            "{before_exit}"
        );

        for (body, arguments) in [
            ("", &[][..]),
            (" by { step_until(function.exit); solve(); }", &[][..]),
            (
                " by { step_until(function.exit); solve(); }",
                &["--trace-proof", "half"][..],
            ),
        ] {
            let miss = run(
                &format!("int32 half(int32 x) {{ ensures result == 17; }}{body}"),
                arguments,
            );
            assert!(miss.starts_with("unsuccessful search:\n"), "{miss}");
            assert!(miss.contains("\ngoal: "), "{miss}");
        }

        let call = run(
            "int32 callee(int32 n) {\n    requires n >= 0;\n    ensures result == n;\n}\nint32 caller(int32 n) {\n    ensures result == n + 1;\n} by {\n    step(); step(); step(); solve();\n}\n",
            &[],
        );
        assert!(
            call.contains(&format!("\ngoal: n >= 0\n{help}\n")),
            "{call}"
        );
        assert!(call.starts_with("unsuccessful search:\n"), "{call}");
        // A written `step()` is simple, but the implicit `solve` proves its
        // open requirements, so the refusal is that smart tactic's miss.
        assert!(
            call.contains(
                "\nrefused by: the implicit closer that proves this statement's requirements (smart: "
            ) && call.contains("\nsee: click docs tracing\n"),
            "{call}"
        );

        let frame = "int32 area(int32 w, int32 h) {\n    requires w >= 0 and w <= 1000;\n    requires h >= 0 and h <= 1000;\n    ensures to_integer(result) == to_integer(w * h);\n}\nint32 frame(int32 w, int32 h) {\n    requires w >= 0 and w <= 1000;\n    requires h >= 0 and h <= 1000;\n    ensures to_integer(result) == to_integer(w * h + 1);\n}\n";
        // Definedness now states both signed bounds over Integer arithmetic.
        let overflow_goal = |name: &str| {
            format!(
                "to_integer({name}) + 1 <= 2147483647 and to_integer({name}) + 1 >= -2147483648"
            )
        };
        let overflow = run(frame, &[]);
        assert!(
            overflow.contains("`step()` requires proof excluding signed overflow"),
            "{overflow}"
        );
        assert!(
            overflow.contains(&format!("\ngoal: {}\n{help}", overflow_goal("inner"))),
            "{overflow}"
        );
        assert!(!overflow.contains("<unnamed"), "{overflow}");
        let traced = run(frame, &["--trace-proof", "frame"]);
        // Traces preserve the checked width and Integer condition notation.
        let typed_goal = concat!(
            "(integer-condition((machine-integer<Int32>(inner)+1) <= 2147483647) is true",
            " ∧ integer-condition((machine-integer<Int32>(inner)+1) >= -2147483648) is true)",
        );
        assert!(
            traced.contains("\nproof refusal:\n")
                && traced.contains(&format!("\ngoal: {typed_goal}\n")),
            "{traced}"
        );

        let bookkeeping = run(
            "int32 half(int32 x) {\n    requires x >= 0 and x % 2 == 0;\n    ensures result >= 0;\n}\nint32 halve_pair(int32 *p, int32 n) {\n    owns p[0..2];\n    requires n >= 0 and n < 1000;\n    ensures result == n;\n}\n",
            &["--trace-proof", "halve_pair"],
        );
        assert!(
            bookkeeping.contains("\n  … <1 internal bookkeeping fact not shown>"),
            "{bookkeeping}"
        );
        // little_endian() is a citable fact, even under its typed trace name.
        // Other reserved predicates in this fixture are kernel bookkeeping.
        assert!(
            !bookkeeping
                .replace("__click_little_endian", "little_endian")
                .contains("__click_"),
            "{bookkeeping}"
        );

        // Definedness is one of a statement's requirements: under a written
        // `step()` the implicit `solve` proves it, so an unprovable one is
        // that smart tactic's miss.
        let overflow = run(
            "int32 next(int32 x) {\n    requires x >= 0;\n    ensures result == x + 1;\n} by {\n    step(); solve();\n}\n",
            &[],
        );
        assert!(
            overflow.contains(&format!("\ngoal: {}\n", overflow_goal("x")))
                && overflow.contains(
                    "\nrefused by: the implicit closer that proves this statement's requirements (smart: "
                ),
            "{overflow}"
        );

        let tail_miss = run(
            "function successor(n: int32) -> int32 { n + 1 }\ntheorem tail_miss(x: int32) {\n    requires x == 3;\n    ensures successor(x) == 5 by {\n        unfold(successor(x));\n    }\n}\n",
            &[],
        );
        assert!(
            tail_miss.starts_with("unsuccessful search:\n"),
            "{tail_miss}"
        );
        assert!(
            tail_miss.contains("goal: to_integer(x + 1) == 5"),
            "{tail_miss}"
        );
        assert!(!tail_miss.contains("refused by: `unfold`"), "{tail_miss}");

        // `normalize()` evaluates without context, so a goal that needs the
        // premise is outside what it does.
        let closer = run(
            "theorem needs_its_premise(x: int32) {\n    requires x == 1;\n    ensures x == 1 by {\n        normalize();\n    }\n}\n",
            &[],
        );
        assert!(
            closer.contains(
                "\nrefused by: `normalize` (simple: a refusal within its documented behavior is a bug)\nsee: click docs normalize\n"
            ),
            "{closer}"
        );

        let resource = run(
            "void set(int32 *p) {\n    owns p[0..1];\n}\nvoid lend_twice(int32 *p) {\n    owns p[0..1];\n}\n",
            &[],
        );
        assert!(
            resource.contains("\nrequired evidence: owns p[1]\n"),
            "{resource}"
        );

        // A sidecar that does not load reports that failure, not the
        // `--trace-proof` naming hint.
        let malformed = run(
            "int32 frame(int32 w, int32 h) {\n    requires w >=;\n}\n",
            &["--trace-proof", "frame"],
        );
        assert!(malformed.starts_with("syntax error:"), "{malformed}");
        assert!(!malformed.contains("--trace-proof` takes"), "{malformed}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// In an mdtest the refused statement is named at its line of the
    /// markdown file, the line a person edits.
    #[test]
    fn mdtest_c_statement_sites_name_the_markdown_line() {
        let directory = std::env::temp_dir().join(format!(
            "click-mdtest-statement-sites-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let path = directory.join("located.md");
        // The C block body starts on line 6; `total = a + b;` is line 8.
        fs::write(
            &path,
            "# Located\n\nProse before the blocks.\n\n```c filename=add.c\nint32 add(int32 a, int32 b) {\n    int32 total;\n    total = a + b;\n    return total;\n}\n```\n\n```click\nverifying \"add.c\";\nint32 add(int32 a, int32 b) {\n    ensures result == a + b;\n} by {\n    step(); step(); step(); solve();\n}\n```\n\n```expect\nfail: signed overflow\n```\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), path.display().to_string()]).unwrap_err();
        assert!(
            error.contains(
                "`step()` requires proof excluding signed overflow\n  C statement at located.md:8:5\n  `total = a + b;`\n"
            ),
            "{error}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    /// `click verify` takes an mdtest as `profile`, `expand`, and `audit` do:
    /// it verifies the fenced Click and C blocks, and every location it reads
    /// or reports is a line of the markdown file.
    #[test]
    fn verify_accepts_an_mdtest_with_markdown_locations() {
        let directory =
            std::env::temp_dir().join(format!("click-verify-mdtest-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let mdtest = |body: &str, expectation: &str| {
            format!(
                "# a markdown test\n\n```c filename=f.c\nint32 f() {{ return 1; }}\n```\n\n```click\nverifying \"f.c\";\n{body}\n```\n\n```expect\n{expectation}\n```\n"
            )
        };
        let passing = directory.join("passing.md");
        fs::write(
            &passing,
            mdtest("int32 f() { ensures result == 1; }", "pass"),
        )
        .unwrap();
        let failing = directory.join("failing.md");
        fs::write(
            &failing,
            mdtest(
                "int32 f() { ensures result == 1; } by { step(); step(); solve(); }",
                "fail: step",
            ),
        )
        .unwrap();
        let verify = |target: String| entry(["verify".to_string(), target]);

        verify(passing.display().to_string()).expect("a passing mdtest verifies");
        // Line 9 of the file is line 2 of the Click block.
        verify(format!("{}:9:13", passing.display())).expect("an mdtest location verifies");
        let outside = verify(format!("{}:2:1", passing.display())).unwrap_err();
        assert!(
            outside.contains("is not inside the ```click block"),
            "{outside}"
        );

        let error = verify(failing.display().to_string()).unwrap_err();
        assert!(error.starts_with("tactic error:"), "{error}");
        assert!(error.contains("tactic@9:"), "{error}");
        assert!(error.contains("\n  step();"), "{error}");
        assert!(!error.contains("-->"), "{error}");
        let changed = entry([
            "verify".to_string(),
            "--changed-since".to_string(),
            "HEAD".to_string(),
            passing.display().to_string(),
        ])
        .unwrap_err();
        assert!(changed.contains("does not take an mdtest"), "{changed}");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn execution_completion_uses_the_guarded_call_paths_facts() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("demo.c"),
            "void clear(int *p, const int *q) { if (p) *p = 0; }",
        )
        .unwrap();
        let sidecar = directory.path().join("demo.click");
        fs::write(
            &sidecar,
            r#"verifying "demo.c";
resource maybe_cell(p: int32*) {
    field value: int32;
    if p != 0 { owns p[0..1]; }
}
void clear(int32* p, const int32* q) {
    views q[0..1];
    owns cell: maybe_cell(p);
    requires p == 0 or separate(memory(p[0..1]), memory(q[0..1]));
}
contract void Clear(int32* p, const int32* q) {
    views q[0..1];
    owns cell: maybe_cell(p);
    requires p == 0 or separate(memory(p[0..1]), memory(q[0..1]));
}
theorem clear_has_contract() executes clear(int32* p, const int32* q) {
    ensures Clear(&clear) as { cell: c } by {
        if p != 0 {
            have separate(memory(p[0..1]), memory(q[0..1])) by {
                cases {
                    p == 0 => { contradiction(p == 0); }
                    separate(memory(p[0..1]), memory(q[0..1])) => { known(); }
                }
            }
            step(clear, { cell: c });
            solve();
        } else {
            step(clear, { cell: c });
            solve();
        }
    }
}
"#,
        )
        .unwrap();

        entry([
            "verify".to_owned(),
            "--trace-proof".to_owned(),
            "clear_has_contract".to_owned(),
            sidecar.display().to_string(),
        ])
        .expect("the nonnull path proves its write separate from the view");
    }

    #[test]
    fn verify_names_a_fold_arguments_unproved_read() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("fold.c"),
            "struct link { int *next; };\nint check(struct link *node) { int value = 0; return value; }",
        )
        .unwrap();
        let sidecar = directory.path().join("fold.click");
        fs::write(
            &sidecar,
            r#"resource tag(value: int32*) {}
verifying "fold.c";
int32 check(struct link* node) {
    ensures result == 0;
} by {
    step();
    fold(tag(node->next));
    step_until(function.exit);
    solve();
}
"#,
        )
        .unwrap();
        let path = sidecar.display().to_string();
        let ordinary = entry(["verify".to_owned(), path.clone()]).unwrap_err();
        assert!(
            ordinary.contains("could not lower resource `tag` argument 0"),
            "{ordinary}"
        );
        assert!(
            ordinary.contains("required evidence: defined(node->next)"),
            "{ordinary}"
        );

        let trace = entry([
            "verify".to_owned(),
            "--trace-proof".to_owned(),
            "check".to_owned(),
            path,
        ])
        .unwrap_err();
        let (_, failed) = trace
            .split_once("\nproof refusal:\n")
            .unwrap_or_else(|| panic!("{trace}"));
        assert!(
            failed.lines().any(|line| {
                line.starts_with("required evidence: defined-read(current, state#")
                    && line.ends_with(", node)")
            }),
            "{trace}"
        );
        assert!(!trace.contains("<unrecorded point"), "{trace}");
        assert!(!trace.contains("<pointer A>"), "{trace}");
    }

    #[test]
    fn verify_names_the_failed_simple_tactic() {
        let directory =
            std::env::temp_dir().join(format!("click-failed-step-report-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("f.c"), "int32 f() { return 1; }\n").unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by { step(); step(); solve(); }\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("tactic error:"), "{error}");
        assert!(error.contains("\n\ntactic@2:"), "{error}");
        assert!(
            error.contains("\n\nTo get a trace:\n  click verify --trace-proof f "),
            "{error}"
        );

        let traced = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "f".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(traced.starts_with("tactic error:\n"), "{traced}");
        assert!(traced.contains("\n\ntactic@2:"), "{traced}");
        assert!(!traced.contains("\n  --> "), "{traced}");
        assert!(
            traced.contains("\n\nproof trace (checked tactics and branch facts):"),
            "{traced}"
        );
        assert!(
            traced.contains("proof trace (checked tactics and branch facts)"),
            "{traced}"
        );
        assert!(traced.contains("steps through: return 1"), "{traced}");
        assert!(!traced.contains("error kind:"), "{traced}");
        assert!(traced.contains("proof refusal:"), "{traced}");
        assert!(traced.contains("stage: proof step"), "{traced}");
        assert!(!traced.contains("To get a trace:"), "{traced}");

        fs::write(
            directory.join("f.c"),
            "int32 f() { int32 x; x = 1; return x; }\n",
        )
        .unwrap();
        fs::write(
            &sidecar,
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by { step(); have 0 == 1 by { normalize(); } step(); solve(); }\n",
        )
        .unwrap();
        let nested = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "f".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(nested.contains("tactic@2:66:\n  normalize();"), "{nested}");
        assert!(
            nested.contains("location: tactic 1 > have body tactic 1"),
            "{nested}"
        );
        assert!(nested.contains("required evidence: 0 == 1"), "{nested}");
        assert!(nested.contains("steps through: declare x"), "{nested}");

        let wrong = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "missing".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(wrong.contains("is not a selected proof"), "{wrong}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// A failing tactic written in a proof `if`, `cases`, or `both` arm
    /// inside a `have` body, or in the body of a loop `initialize` phase
    /// helper `have`, is reported at its own line. Arm tactics used to be
    /// renumbered from the start of the `have` body and reported a sibling's
    /// line, and initialize-phase bodies reported no line at all.
    #[test]
    fn verify_locates_failed_tactics_in_have_arms_and_initialize_helpers() {
        let directory =
            std::env::temp_dir().join(format!("click-arm-locations-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("identity.c"),
            "int32 identity(int32 x) { return x; }\n",
        )
        .unwrap();
        fs::write(
                directory.join("count_up.c"),
                "int32 count_to_n(int32 n) {\n    int32 i;\n    i = 0;\n    while (i < n) {\n        i++;\n    }\n    return i;\n}\n",
            )
            .unwrap();
        let identity = |body: &str| {
            format!(
                "verifying \"identity.c\";\nint32 identity(int32 x) {{\n    ensures result == x;\n}} by {{\n    have x <= x by {{\n{body}    }}\n    step_until(function.exit);\n    solve();\n}}\n"
            )
        };
        let count_up = |phase: &str| {
            format!(
                "verifying \"count_up.c\";\nint32 count_to_n(int32 n) {{\n    requires n >= 0 and n <= 2147483647;\n    ensures result == n;\n}} by {{\n    step();\n    step();\n    loop {{\n        decreases n - i;\n        invariant i >= 0;\n        invariant i <= n;\n        initialize by {{\n{phase}        }}\n        maintain by {{\n            step();\n        }}\n    }}\n    step();\n    solve();\n}}\n"
            )
        };
        // Give each selected `known()` a false goal, so improvements to
        // reasoning about the surrounding true goal cannot make it pass.
        let cases = [
            (
                "if_arm",
                identity(
                    "        have x == x by solve();\n        if x > 0 {\n            solve();\n        } else {\n            known();\n        }\n",
                ),
                10,
            ),
            (
                "cases_arm",
                identity(
                    "        have x > 0 or not (x > 0) by {\n            if x > 0 {\n                known();\n            } else {\n                known();\n            }\n        }\n        cases { x > 0 => {\n            solve();\n        } not (x > 0) => {\n            known();\n        } }\n",
                ),
                16,
            ),
            (
                "if_continuation",
                identity(
                    "        if x > 0 {\n            have x == x by solve();\n            have x == x by solve();\n        } else {\n            have x == x by solve();\n        }\n        known();\n",
                ),
                12,
            ),
            (
                "initialize_helper",
                count_up(
                    "            have -1 < n by {\n                have n == n by solve();\n                known();\n            }\n            solve();\n",
                ),
                15,
            ),
            (
                "initialize_invariant_body",
                count_up(
                    "            have i >= 0 by solve();\n            have -1 < n by {\n                have n == n by solve();\n                known();\n            }\n",
                ),
                16,
            ),
            (
                "initialize_shared_script",
                count_up("            have n == n by solve();\n            known();\n"),
                14,
            ),
        ];
        for (name, source, line) in cases {
            let mut lines = source.lines().map(str::to_string).collect::<Vec<_>>();
            let target = &mut lines[line - 1];
            assert_eq!(target.trim(), "known();", "{name}");
            let indent = &target[..target.len() - target.trim_start().len()];
            *target = format!("{indent}have false by {{\n{indent}    known();\n{indent}}}");
            let source = lines.join("\n");
            let line = line + 1;
            let sidecar = directory.join(format!("{name}.click"));
            fs::write(&sidecar, &source).unwrap();
            let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
            assert_eq!(
                source.lines().nth(line - 1).map(str::trim),
                Some("known();"),
                "{name}"
            );
            assert!(
                error.contains(&format!("\n\ntactic@{line}:\n  known();")),
                "{name}: {error}"
            );
        }
        fs::remove_dir_all(directory).unwrap();
    }

    /// A type error names the declaration it rejects, so the report shows
    /// that declaration's line rather than no location at all.
    #[test]
    fn verify_locates_a_type_error_at_its_declaration() {
        let directory =
            std::env::temp_dir().join(format!("click-type-locations-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("apply.c"),
            "int32 keep(int32 x) { return x; }\nint32 apply(int32 (*callback)(int32), int32 value) {\n    return callback(value);\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("apply.click");
        fs::write(
            &sidecar,
            "verifying \"apply.c\";\n\ncontract int32 Binary(int32 left, int32 right) {\n    ensures result == left + right;\n}\n\nint32 keep(int32 x) {\n    ensures result == x;\n}\n\nint32 apply(int32 (*callback)(int32), int32 value) {\n    requires Binary(callback);\n}\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.contains("expects int32 (*)(int32, int32), got int32 (*)(int32)"),
            "{error}"
        );
        assert!(
            error.contains("apply.click:11:1")
                && error.contains("11 | int32 apply(int32 (*callback)(int32), int32 value) {"),
            "{error}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn trace_shows_the_whole_failed_multiline_tactic() {
        let directory =
            std::env::temp_dir().join(format!("click-whole-failed-tactic-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("f.c"), "int32 f() { return 1; }\n").unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by {\n    step();\n    have exists (x: int32) { x == 0 } by {\n        let x = obtain(\n            exists (k: int32) { k == 0 }\n        );\n    }\n    solve();\n}\n",
        )
        .unwrap();
        let traced = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "f".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(!traced.contains("prove it with `have` first"), "{traced}");
        assert!(
            traced.contains("requirement `exists (k: int32) { k == 0 }` not satisfied"),
            "{traced}"
        );
        assert!(
            traced.contains("requires: exists (k: int32) { k == 0 }"),
            "{traced}"
        );
        assert_eq!(
            traced.matches("\nrequired evidence:").count(),
            1,
            "{traced}"
        );
        assert!(
            traced
                .contains("tactic@5:\n  let x = obtain(\n      exists (k: int32) { k == 0 }\n  );"),
            "{traced}"
        );
        assert!(!traced.contains("\nstep: "), "{traced}");
        assert!(traced.contains("let x = obtain(\n"), "{traced}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// The implicit tail joins an early `return` with the rest of the
    /// function at exit. A claim that fails on the rest's outcome path shows
    /// that arm and the read it made, not `branch (joined)`; a failure on
    /// the early return's path shows the then arm.
    #[test]
    fn trace_of_a_terminal_join_shows_the_failing_paths_arm() {
        let directory =
            std::env::temp_dir().join(format!("click-terminal-join-trace-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("g.c"),
            "int g(int *p, int q) {\n    if (q == 0) return 1;\n    int v = *p;\n    return v;\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("g.click");
        for (ensures, path, arm, step) in [
            (
                "result == 1",
                "path 1",
                "branch (else arm)",
                "steps through: v = *p",
            ),
            (
                "result == 0",
                "path 0",
                "branch (then arm)",
                "steps through: return 1",
            ),
        ] {
            fs::write(
                &sidecar,
                format!(
                    "verifying \"g.c\";\n\nint32 g(int32 *p, int32 q) {{\n    views p[0..1];\n    requires defined(p[0]);\n    ensures {ensures};\n}}\n"
                ),
            )
            .unwrap();
            let traced = entry([
                "verify".to_string(),
                "--trace-proof".to_string(),
                "g".to_string(),
                sidecar.display().to_string(),
            ])
            .unwrap_err();
            assert!(
                traced.contains(&format!("`g.ensures_0` {path}")),
                "{traced}"
            );
            assert!(traced.contains(arm), "{traced}");
            assert!(traced.contains(step), "{traced}");
            assert!(!traced.contains("(joined)"), "{traced}");
        }
        fs::remove_dir_all(directory).unwrap();
    }

    const SHARED_POPULATION_FIXTURE: &str =
        include_str!("../../mdtests/shared_heap_population_certification.md");

    #[test]
    #[ignore = "nightly: 6s in the parallel gate"]
    fn tautological_ensure_preserves_population_certification() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join("shared_population.md");
        let tautology = "    ensures old(p->kid) == old(p->kid);\n";
        let baseline = SHARED_POPULATION_FIXTURE.replacen(tautology, "", 1);
        assert_ne!(baseline, SHARED_POPULATION_FIXTURE);

        for source in [baseline.as_str(), SHARED_POPULATION_FIXTURE] {
            fs::write(&fixture, source).unwrap();
            entry([
                "verify".to_string(),
                "--trace-proof".to_string(),
                "parent_detach".to_string(),
                fixture.display().to_string(),
            ])
            .unwrap();
        }
        entry(["verify".to_string(), fixture.display().to_string()]).unwrap();
    }

    // Simple claim closers must perform the same checked return exchange as
    // solve, including a consuming contract with no returned resource claim.
    #[test]
    #[ignore = "nightly: 10s in the parallel gate"]
    fn shared_population_release_expansion_retains_lifetime() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join("shared_population.md");
        let source = SHARED_POPULATION_FIXTURE;
        fs::write(&fixture, source).unwrap();
        entry(["verify".to_string(), fixture.display().to_string()]).unwrap();
        let click_start = source.find("```click\n").unwrap();
        let release_start =
            click_start + source[click_start..].find("void child_release(").unwrap();
        let release_end =
            release_start + source[release_start..].find("void parent_attach(").unwrap();
        let final_release = "        solve();\n    } else {";
        let final_closer = release_start
            + source[release_start..release_end]
                .find(final_release)
                .unwrap();
        let line = source[..final_closer]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        entry([
            "expand".to_string(),
            "--in-place".to_string(),
            format!("{}:{line}:9", fixture.display()),
        ])
        .unwrap();
        let expanded = fs::read_to_string(&fixture).unwrap();
        assert_ne!(expanded, source);
        entry(["verify".to_string(), fixture.display().to_string()]).unwrap();
    }

    #[test]
    fn verify_classifies_source_link_errors_and_failed_proof_splits() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (name, heading, detail) in [
            (
                "file_scope_incomplete_extern_array_link_errors.md",
                "type error",
                "has no definition",
            ),
            (
                "file_scope_tentative_array_link_errors.md",
                "type error",
                "conflicting declarations",
            ),
            (
                "cases_arms_that_do_not_rejoin_are_refused.md",
                "tactic error",
                "do not rejoin",
            ),
            (
                "loop_body_proof_match_missing_arm.md",
                "tactic error",
                "cover every constructor",
            ),
            (
                "population_rejects_nested_open.md",
                "tactic error",
                "population body is already open",
            ),
        ] {
            let error = entry([
                "verify".to_string(),
                fixtures.join(name).display().to_string(),
            ])
            .unwrap_err();
            assert!(error.starts_with(&format!("{heading}:")), "{error}");
            assert!(error.contains(detail), "{error}");
        }
    }

    #[test]
    fn verify_classifies_contract_closing_and_theorem_setup_failures() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (name, heading, detail) in [
            (
                "a_claim_that_cannot_lower_after_step_until_is_refused_with_its_cause.md",
                "incomplete proof",
                "requires owning authority",
            ),
            (
                "an_unbounded_variable_tag_does_not_preserve_a_pointer_relationship.md",
                "incomplete proof",
                "integer-to-pointer cast requires",
            ),
            (
                "loop_decreases_rejects_a_state_measure.md",
                "contract error",
                "a termination measure must be a function of the current state alone",
            ),
            (
                "algebraic_generic_theorem_rejects_cyclic_verification.md",
                "contract error",
                "circular theorem justification",
            ),
            (
                "c_contract_executes_signature.md",
                "contract error",
                "executes signature does not match",
            ),
            (
                "defined_of_a_match_owes_its_arms_operands_domains.md",
                "contract error",
                "condition of its evaluation",
            ),
            (
                "nested_loop_mark_invariant_diagnostic.md",
                "contract error",
                "cannot be used in a loop invariant",
            ),
            (
                "loop_entry_memory_capture_short_rejected.md",
                "incomplete proof",
                "loop declares a resource the enclosing function does not hold",
            ),
            (
                "resource_child_pure_arguments_non_c.md",
                "type error",
                "does not return a C value",
            ),
            (
                "loop_preserve_bare_instantiate_names_repair.md",
                "unsupported",
                "move the operation into `have proposition by { ... }`",
            ),
            (
                "named_contract_rejects_unheld_link_read.md",
                "contract error",
                "could not address resource clause",
            ),
            (
                "abbreviated_produced_view_ambiguous.md",
                "contract error",
                "matches multiple input views",
            ),
            (
                "while_guard_unreadable_operand_rejected.md",
                "tactic error",
                "the loop condition could not be evaluated on this path",
            ),
            (
                "a_closer_with_no_open_goal_is_refused.md",
                "tactic error",
                "has no goal to close",
            ),
            (
                "c_builtin_limits_conflicting_definition.md",
                "syntax error",
                "macro `INT_MAX` is redefined",
            ),
            (
                "conditional_compilation_rejects_expression.md",
                "unsupported",
                "unsupported conditional expression",
            ),
        ] {
            let error = entry([
                "verify".to_string(),
                fixtures.join(name).display().to_string(),
            ])
            .unwrap_err();
            assert!(error.starts_with(&format!("{heading}:")), "{name}: {error}");
            assert!(error.contains(detail), "{name}: {error}");
        }
    }

    #[test]
    fn verification_preserves_diagnoses_through_loop_and_contract_wrappers() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (name, heading, detail) in [
            (
                "mutex_guard_contract_rejects_false_unheld.md",
                "tactic error",
                "held cannot inspect an opaque contract protocol",
            ),
            (
                "refold_rechecks_the_opened_witness_fact.md",
                "internal error",
                "Click could not express the requirement for implicit proof search",
            ),
            (
                "cpp_virtual_override_rejects_narrower_requires.md",
                "contract error",
                "`0 <= scale and scale <= 10`",
            ),
            (
                "a_contract_that_cannot_be_applied_names_the_clause_that_refused.md",
                "type error",
                "cannot infer type argument T",
            ),
            (
                "exceptional_named_contract_rejects_throwing_implementation.md",
                "tactic error",
                "the target may throw, but the named contract promises it cannot throw",
            ),
            (
                "loop_invariant_viewable_range_false_at_entry_is_refused_at_entry.md",
                "unsuccessful search",
                "a memory range it states runs backwards",
            ),
            (
                "loop_binder_rejects_ambiguous_instance.md",
                "tactic error",
                "matches 2 owned `tag` instances",
            ),
        ] {
            let report = entry([
                "verify".to_owned(),
                fixtures.join(name).display().to_string(),
            ])
            .unwrap_err();
            assert!(
                report.starts_with(&format!("{heading}:")),
                "{name}: {report}"
            );
            assert!(report.contains(detail), "{name}: {report}");
        }
    }

    #[test]
    fn verification_separates_unprepared_safety_goals_from_unsupported_operations() {
        let fixture = |name: &str| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("mdtests")
                .join(name)
                .display()
                .to_string()
        };
        let error = entry([
            "verify".to_string(),
            fixture("a_symbolic_read_of_an_unwritten_local_element_is_uninitialized.md"),
        ])
        .unwrap_err();
        assert!(error.starts_with("internal error:"), "{error}");
        assert!(
            error.contains("generated statement safety obligation")
                && error.contains("read of uninitialized storage")
                && error.contains("x == 0"),
            "{error}"
        );

        let error = entry([
            "verify".to_string(),
            fixture("a_one_past_the_end_pointer_is_not_compared_with_another_object.md"),
        ])
        .unwrap_err();
        assert!(error.starts_with("unsupported:"), "{error}");
        assert!(
            error.contains("whether the two objects are adjacent is unspecified"),
            "{error}"
        );
        assert!(!error.contains("undefined behavior"), "{error}");
    }

    #[test]
    fn trace_includes_checked_prefix_before_a_statement_runtime_error() {
        let directory = std::env::temp_dir().join(format!(
            "click-trace-statement-runtime-error-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("f.c"), "int32 f() { int32 x; return x; }\n").unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\nint32 f() { ensures result == 0; } by { step(); step(); solve(); }\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("tactic error:"), "{error}");
        assert!(!error.contains("goal:"), "{error}");
        assert!(
            error.contains("\n\nTo get a trace:\n  click verify --trace-proof f "),
            "{error}"
        );
        let traced = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "f".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(traced.contains("read of uninitialized storage"), "{traced}");
        assert!(!traced.contains("\nstep: "), "{traced}");
        assert!(!traced.contains("error kind:"), "{traced}");
        assert!(traced.contains("tactic@2:41: step"), "{traced}");
        assert!(traced.contains("steps through: declare x"), "{traced}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// A refused `transport using` prints its own legend. The trace keeps
    /// that numbering, so the proof refusal's goal names the states and
    /// values the refusal defined; its cell walks print one per line; and a
    /// field of a named pointer prints as that name plus its offset.
    #[test]
    fn trace_of_a_transport_refusal_keeps_the_refusal_labels() {
        const C_SOURCE: &str = r#"struct rb_node { unsigned long __rb_parent_color; struct rb_node *rb_right; struct rb_node *rb_left; };
void recolor(struct rb_node *gparent) {
    struct rb_node *parent = gparent->rb_left;
    parent->__rb_parent_color = 1;
}
"#;
        const CLICK_SOURCE: &str = r#"verifying "recolor.c";
void recolor(struct rb_node* gparent) {
    owns gparent->rb_left;
    owns gparent->rb_left->__rb_parent_color;
} by {
    step(); step();
    mark before_store;
    step();
    have parent->__rb_parent_color == at(before_store, parent->__rb_parent_color) by {
        transport(at(before_store, parent->__rb_parent_color) == at(before_store, parent->__rb_parent_color),
                  parent->__rb_parent_color == at(before_store, parent->__rb_parent_color)) using {
            parent == gparent->rb_left;
        };
    }
    step_until(function.exit);
}
"#;
        let directory = std::env::temp_dir().join(format!(
            "click-trace-transport-labels-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("recolor.c"), C_SOURCE).unwrap();
        let sidecar = directory.join("recolor.click");
        fs::write(&sidecar, CLICK_SOURCE).unwrap();
        let report = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "recolor".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        let target = report
            .split_once("\n  checked target (wanted)\n  ")
            .and_then(|(_, rest)| rest.lines().next())
            .unwrap_or_else(|| panic!("{report}"));
        assert!(
            report.contains(&format!("\nrequired evidence: {target}\n")),
            "{report}"
        );
        assert!(report.contains("\n    address: value#"), "{report}");
        assert!(report.contains("= gparent + 16 bytes"), "{report}");
        assert!(!report.contains("\n  width\n"), "{report}");
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn trace_distinguishes_saved_call_argument_from_current_read() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("calls.c"),
            "void update(int *p, int x) { *p = 1; }\nvoid parent(int *p) { update(p, *p); }\n",
        )
        .unwrap();
        let sidecar = directory.path().join("calls.click");
        fs::write(
            &sidecar,
            r#"verifying "calls.c";
void update(int32* p, int32 x) {
    owns p[0..1];
    ensures defined(*p);
    ensures exists (z: int32) { z == x } by {
        step_until(function.exit);
        witness(x);
        normalize();
    }
}
void parent(int32* p) {
    owns p[0..1];
    ensures defined(*p);
} by {
    step(update);
    have exists (z: int32) { z == *p } by { known(); }
}
"#,
        )
        .unwrap();
        let report = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "parent".to_string(),
            sidecar.display().to_string(),
        ])
        .expect_err("the saved argument fact cannot close the current read goal");
        let (trace, failed_check) = report
            .split_once("\nproof refusal:\n")
            .unwrap_or_else(|| panic!("{report}"));
        let read_state = |section: &str, prefix: &str| {
            section
                .lines()
                .find_map(|line| {
                    let read = line.trim().strip_prefix(prefix)?;
                    let (state, _) = read.split_once(", pointer=p)")?;
                    state.parse::<u32>().ok()
                })
                .unwrap_or_else(|| panic!("{report}"))
        };
        read_state(
            trace,
            "adds: ∃z:ProgramInt32. int32 =(z, read<Bits32>(state#",
        );
        assert!(failed_check.contains("You must prove `exists (z: int32) { z == *p }` in order to use the tactic `known()`."), "{report}");
    }

    #[test]
    fn trace_shows_exact_checked_pointer_goal_after_rewrite() {
        let directory = std::env::temp_dir().join(format!(
            "click-trace-refined-pointer-goal-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let sidecar = directory.join("refined.click");
        fs::write(
            &sidecar,
            r#"
function tag(p: int32*) -> int32 { 0 }
theorem bad(p: int32*, q: int32*) {
    requires p == q;
    ensures tag(p) == 1 by {
        rewrite(p, q);
        known();
    }
}
"#,
        )
        .unwrap();
        let ordinary = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        let report = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "bad".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        let (_, refusal) = report.split_once("\nproof refusal:\n").unwrap();
        for diagnostic in [&ordinary, refusal] {
            assert!(
                diagnostic
                    .contains("You must prove `tag(q) == 1` in order to use the tactic `known()`."),
                "{diagnostic}"
            );
            assert!(!diagnostic.contains("array-ref<int32>"), "{diagnostic}");
        }
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn trace_accepts_an_exact_historical_call_guarantee() {
        let directory =
            std::env::temp_dir().join(format!("click-trace-call-guarantee-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("calls.c"),
            "extern int32 child(int32 *a, int32 *b, int32 n, int32 x);\nint32 parent(int32 *a, int32 *b, int32 n, int32 i) { return child(a, b, n, a[i]); }\n",
        )
        .unwrap();
        let sidecar = directory.join("calls.click");
        fs::write(
            &sidecar,
            r#"verifying "calls.c";
spec enum Path { Here }
function pick(x: int32, path: Path) -> int32 {
    match path { Path::Here => x }
}
extern int32 child(int32 *a, int32 *b, int32 n, int32 x) {
    views a[0..n];
    owns b[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures exists (path: Path) { pick(x, path) == x };
}
int32 parent(int32 *a, int32 *b, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    views a[0..n];
    owns b[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result == result;
} by {
    mark before_call;
    let { result: r } = step(child);
    have defined(at(before_call, a[i])) by {
        instantiate(at(before_call, forall (k: int32) {
            0 <= k and k < n implies defined(a[k])
        }), i);
        known();
    }
    have exists (path: Path) {
        pick(at(before_call, a[i]), path) == at(before_call, a[i])
    } by {
        known();
    }
    step(); solve();
}
"#,
        )
        .unwrap();
        entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "parent".to_string(),
            sidecar.display().to_string(),
        ])
        .expect("a call-produced existential has an exact historical spelling");
        entry(["verify".to_string(), sidecar.display().to_string()]).unwrap();
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn failed_call_names_the_c_operation_and_parameter_bindings() {
        let directory =
            std::env::temp_dir().join(format!("click-call-error-context-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("calls.c"),
            "void read(int32* p) { }\nvoid caller(int32* second) { read(second); }\n",
        )
        .unwrap();
        let sidecar = directory.join("calls.click");
        fs::write(
            &sidecar,
            "verifying \"calls.c\";\nvoid read(int32* p) { owns p[0..1]; }\nvoid caller(int32* second) { ensures second == second; } by { step(); solve(); }\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.contains("\n  C operation\n  read(second)"), "{error}");
        assert!(error.contains("\n  call bindings\n  p = second"), "{error}");
        assert!(!error.contains("proof context:"), "{error}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// An unclosed goal shows the facts bearing on it: the chain through `j`
    /// to the constant is listed, the fact about the unrelated `y` is not,
    /// and the whole-context section a step refusal carries stays hidden.
    #[test]
    fn an_unclosed_goal_shows_the_facts_bearing_on_it() {
        let directory =
            std::env::temp_dir().join(format!("click-goal-proof-context-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("goal.c"),
            "int32 bump(int32 x, int32 j, int32 y) { return x + 1; }\n",
        )
        .unwrap();
        let sidecar = directory.join("goal.click");
        fs::write(
            &sidecar,
            "verifying \"goal.c\";\nint32 bump(int32 x, int32 j, int32 y) {\n    requires 0 <= x and x <= j;\n    requires j < 10;\n    requires y > 3;\n    ensures result == x + 2;\n}\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.contains("\n  proof context\n  pure facts: [0 <= x, x <= j, j < 10]"),
            "{error}"
        );
        assert!(
            !error.contains("y > 3") && !error.contains("3 < y"),
            "{error}"
        );
        assert!(!error.contains("resource facts: []"), "{error}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// A goal refused inside one case of a proof `if` names that case, even
    /// though the case condition shares no term with the goal; an unrelated
    /// `requires` still stays out.
    #[test]
    fn an_unclosed_goal_in_a_proof_if_case_names_the_case() {
        let directory =
            std::env::temp_dir().join(format!("click-goal-case-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("case.c"),
            "int32 pick(int32 x, int32 y, int32 z) { return x; }\n",
        )
        .unwrap();
        let sidecar = directory.join("case.click");
        fs::write(
            &sidecar,
            "verifying \"case.c\";\nint32 pick(int32 x, int32 y, int32 z) {\n    requires x < 10;\n    requires z > 3;\n    ensures result == 0;\n} by {\n    if y > 3 { step_until(function.exit); solve(); } else { step_until(function.exit); solve(); }\n}\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.contains("\n  proof context\n  case: [y > 3]\n  pure facts: [x < 10]"),
            "{error}"
        );
        assert!(
            !error.contains("z > 3") && !error.contains("3 < z"),
            "{error}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    /// The command a failing theorem's report suggests is accepted, and a
    /// theorem is traced like a function: checked steps at their written
    /// lines up to the failing tactic, a `--trace-to` target in a passing
    /// proof, and only the named theorem verified.
    #[test]
    #[ignore = "nightly: 0.5s in the parallel gate"]
    fn trace_proof_accepts_a_pure_theorem() {
        let directory =
            std::env::temp_dir().join(format!("click-trace-theorem-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("f.c"), "int32 f() { return 1; }\n").unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            r#"verifying "f.c";
theorem good(x: int32, y: int32) {
    requires x == y;
    ensures y == x by {
        have y == x by { solve(); }
        known();
    }
}
theorem bad(x: int32, y: int32) {
    requires x == y;
    ensures x == 0 by {
        have y == x by { solve(); }
        have x == 0 by { normalize(); }
        known();
    }
}
theorem arms(x: int32) {
    ensures x == x by {
        if x == 0 {
            have x == 0 by { known(); }
        } else {
            have x != 0 by { known(); }
        }
        normalize();
    }
}
int32 f() { ensures result == 2; } by { step(); solve(); }
"#,
        )
        .unwrap();
        let path = sidecar.display().to_string();
        let trace = |arguments: &[&str]| {
            entry(
                ["verify", "--trace-proof"]
                    .iter()
                    .chain(arguments)
                    .map(|argument| argument.to_string())
                    .chain([path.clone()]),
            )
        };

        let error = entry(["verify".to_string(), path.clone()]).unwrap_err();
        assert!(error.contains("tactic@13:26:\n  normalize();"), "{error}");
        let hint = error
            .split_once("\n\nTo get a trace:\n  click ")
            .expect("a failing theorem suggests a trace")
            .1;
        assert_eq!(hint, format!("verify --trace-proof bad {path}"));
        // The suggested command, exactly as printed, is accepted.
        let traced = entry(hint.split(' ').map(str::to_string)).unwrap_err();
        assert!(!traced.contains("is not a selected proof"), "{traced}");
        assert!(
            traced.contains("\n\nproof trace (checked tactics and branch facts):\ntactic@12: have y == x\n  adds: y == x"),
            "{traced}"
        );
        assert!(traced.contains("tactic@13:26:\n  normalize();"), "{traced}");
        assert!(!traced.contains("tactic@14"), "{traced}");
        assert!(!traced.contains("To get a trace:"), "{traced}");
        assert!(traced.len() < 2_000, "{traced}");

        // A passing theorem is traced without verifying `bad` or `f`, whose
        // proofs fail.
        trace(&["good"]).expect("only the named theorem is verified");
        trace(&["good", "--trace-to", "6"]).expect("a written tactic of the theorem");
        trace(&["good", "--trace-to", "5:26"]).expect("a tactic inside a `have` body");
        let elsewhere = trace(&["good", "--trace-to", "12"]).unwrap_err();
        assert!(
            elsewhere.contains("tactic@12 has no recorded checked step on an accepted path"),
            "{elsewhere}"
        );
        // Both arms of a proof `if`, and the tactic after it, are reachable.
        trace(&["arms", "--trace-to", "20"]).expect("the then arm");
        trace(&["arms", "--trace-to", "22"]).expect("the else arm");
        trace(&["arms", "--trace-to", "24"]).expect("the tactic after the `if`");

        let wrong = trace(&["missing"]).unwrap_err();
        assert!(
            wrong.contains("`missing` is not a selected proof in ")
                && wrong.contains("takes the name of a function, theorem, or user-defined tactic"),
            "{wrong}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    /// The trace hint and `--trace-proof` resolve a name alike, which relies
    /// on one name never being both a C function and a theorem.
    #[test]
    fn a_name_is_not_both_a_c_function_and_a_theorem() {
        let directory =
            std::env::temp_dir().join(format!("click-trace-name-kinds-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("f.c"), "int32 f() { return 1; }\n").unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\ntheorem f(x: int32) { ensures x == x by { normalize(); } }\nint32 f() { ensures result == 1; } by { step(); solve(); }\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.contains("`f` is defined as both a theorem and a C function spec"),
            "{error}"
        );
        assert!(!error.contains("To get a trace:"), "{error}");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn trace_verifies_only_the_named_function() {
        let directory = std::env::temp_dir().join(format!(
            "click-trace-selects-one-function-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "int32 f() { return 1; } int32 g() { return 2; }\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by { step(); solve(); }\nint32 g() { ensures result == 2; } by { step(); step(); solve(); }\n",
        )
        .unwrap();
        assert!(entry(["verify".to_string(), sidecar.display().to_string()]).is_err());
        entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "f".to_string(),
            sidecar.display().to_string(),
        ])
        .expect("the selected function should verify independently");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn verify_reports_syntax_and_type_error_kinds() {
        let directory =
            std::env::temp_dir().join(format!("click-error-kinds-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "int32 read(int32 *p) { return p[0]; }\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        fs::write(&sidecar, "verifying \"f.c\"; int32 read(").unwrap();
        let syntax = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(syntax.starts_with("syntax error:"), "{syntax}");
        assert!(!syntax.contains("To get a trace:"), "{syntax}");

        fs::write(
            &sidecar,
            "verifying \"f.c\"; int32 read(const int32 *p) { ensures result == 0; }\n",
        )
        .unwrap();
        let type_error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(type_error.starts_with("type error:"), "{type_error}");
        assert!(!type_error.contains("To get a trace:"), "{type_error}");
        fs::remove_dir_all(directory).unwrap();
    }

    /// A syntax error inside an mdtest block names the line of the markdown
    /// file a person edits, not the line inside its fenced block.
    #[test]
    fn mdtest_syntax_errors_name_the_markdown_line() {
        let directory =
            std::env::temp_dir().join(format!("click-mdtest-lines-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let mdtest = |c_body: &str, click_body: &str| {
            format!(
                "# Located\n\nProse before the blocks.\n\n```c filename=inc.c\n{c_body}\n```\n\nMore prose.\n\n```click\n{click_body}\n```\n\n```expect\npass\n```\n"
            )
        };
        let valid_c = "int32 inc(int32 x) {\n    return x;\n}";
        let path = directory.join("located.md");
        let verify = || entry(["verify".to_string(), path.display().to_string()]).unwrap_err();

        // The C block body starts on line 6; its `return x +;` is line 7.
        fs::write(
            &path,
            mdtest(
                "int32 inc(int32 x) {\n    return x +;\n}",
                "verifying \"inc.c\";",
            ),
        )
        .unwrap();
        let c_error = verify();
        assert!(c_error.starts_with("syntax error:"), "{c_error}");
        assert!(c_error.contains("\n  located.md:7\n"), "{c_error}");

        // The Click block body starts on line 14; the `have` whose name
        // hides the parameter is its third line, line 16 of the file.
        fs::write(
            &path,
            mdtest(
                valid_c,
                "verifying \"inc.c\";\nint32 inc(int32 x) {\n    ensures result == x by { have x: x == x by { solve(); } step(); solve(); }\n}",
            ),
        )
        .unwrap();
        let click_error = verify();
        assert!(click_error.starts_with("syntax error:"), "{click_error}");
        assert!(click_error.contains("\n  located.md:16\n"), "{click_error}");

        // A token the tokenizer refuses is located the same way.
        fs::write(
            &path,
            mdtest(
                valid_c,
                "verifying \"inc.c\";\nint32 inc(int32 x) {\n    ensures !x;\n}",
            ),
        )
        .unwrap();
        let token_error = verify();
        assert!(
            token_error.contains("\n  located.md:16\n  expected `!=`"),
            "{token_error}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn dispatches_import_help_without_spawning() {
        entry(["capture".to_string(), "--help".to_string()]).unwrap();
    }

    #[test]
    fn dispatches_verify_help_without_spawning() {
        entry(["verify".to_string(), "--help".to_string()]).unwrap();
    }

    #[test]
    fn arithmetic_tools_agree_on_expanded_certificate() {
        let directory = std::env::temp_dir().join(format!(
            "click-arithmetic-tool-parity-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let source_path = directory.join("parity.click");
        let expanded_path = directory.join("parity-expanded.click");
        let source = r#"theorem arithmetic_tool_parity(n: int32) {
    requires n <= 10;
    ensures n <= 10 by {
        solve() using { n <= 10; }
    }
}
"#;
        fs::write(&source_path, source).unwrap();

        entry(["verify".to_string(), source_path.display().to_string()])
            .expect("click verify should accept the smart arithmetic request");
        entry([
            "expand".to_string(),
            "--claim".to_string(),
            "arithmetic_tool_parity.ensures_0".to_string(),
            "--output".to_string(),
            expanded_path.display().to_string(),
            source_path.display().to_string(),
        ])
        .expect("click expand should emit the ordinary arithmetic proof");
        let expanded = fs::read_to_string(&expanded_path).unwrap();
        assert!(expanded.contains("known();"), "{expanded}");
        assert!(!expanded.contains("solve() using"), "{expanded}");

        entry(["verify".to_string(), expanded_path.display().to_string()])
            .expect("click verify should recheck the expanded certificate");
        entry(["profile".to_string(), source_path.display().to_string()])
            .expect("click profile should verify the original arithmetic proof");
        entry(["profile".to_string(), expanded_path.display().to_string()])
            .expect("click profile should verify the expanded arithmetic proof");
        entry(["audit".to_string(), source_path.display().to_string()])
            .expect("click audit should reach the same expansion fixed point");

        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn integer_product_bounds_tools_agree_on_wide_ranges_and_retained_audit() {
        let mdtest = click::cli::parse_mdtest(
            std::path::Path::new("integer_product_bounds.md"),
            include_str!("../../mdtests/integer_product_bounds.md"),
        )
        .unwrap();
        let source = mdtest.click_source.unwrap();
        with_supported_boundary(
            "integer-product-bounds",
            source,
            |source_path, expanded_path| {
                for (name, source) in &mdtest.c_sources {
                    fs::write(source_path.parent().unwrap().join(name), source).unwrap();
                }
                entry(["verify".to_string(), source_path.display().to_string()])?;
                entry([
                    "expand".to_string(),
                    "--claim".to_string(),
                    "bounded_identity.contract".to_string(),
                    "--output".to_string(),
                    expanded_path.display().to_string(),
                    source_path.display().to_string(),
                ])?;
                let expanded = fs::read_to_string(expanded_path).unwrap();
                // The product bound is an ordinary arithmetic proof, not a
                // certificate naming its bounds.
                assert!(!expanded.contains("bounds ["), "{expanded}");
                assert!(
                    !expanded.contains("step_until(function.exit);"),
                    "the selected execution must expand"
                );
                entry(["verify".to_string(), expanded_path.display().to_string()])?;
                entry(["profile".to_string(), source_path.display().to_string()])?;
                entry([
                    "audit".to_string(),
                    "--claim".to_string(),
                    "bounded_identity.contract".to_string(),
                    source_path.display().to_string(),
                ])?;
                Ok(())
            },
        );
    }

    fn with_supported_boundary(
        label: &str,
        source: String,
        run: impl FnOnce(&std::path::Path, &std::path::Path) -> Result<(), String>,
    ) {
        let directory = std::env::temp_dir().join(format!(
            "click-surface-depth-cli-valid-{label}-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let source_path = directory.join("at-limit.click");
        let expanded_path = directory.join("at-limit-expanded.click");
        fs::write(&source_path, source).unwrap();

        run(&source_path, &expanded_path).expect("supported boundary command should succeed");

        fs::remove_dir_all(directory).unwrap();
    }

    fn exercise_supported_boundary(label: &str, source: String, claim: &str) {
        with_supported_boundary(label, source, |source_path, expanded_path| {
            entry(["verify".to_string(), source_path.display().to_string()])?;
            entry([
                "expand".to_string(),
                "--claim".to_string(),
                claim.to_string(),
                "--output".to_string(),
                expanded_path.display().to_string(),
                source_path.display().to_string(),
            ])?;
            entry(["profile".to_string(), source_path.display().to_string()])?;
            entry([
                "audit".to_string(),
                "--claim".to_string(),
                claim.to_string(),
                source_path.display().to_string(),
            ])?;
            Ok(())
        });
    }

    fn verify_and_expand_supported_boundary(label: &str, source: String, claim: &str) {
        with_supported_boundary(label, source, |source_path, expanded_path| {
            entry(["verify".to_string(), source_path.display().to_string()])?;
            entry([
                "expand".to_string(),
                "--claim".to_string(),
                claim.to_string(),
                "--output".to_string(),
                expanded_path.display().to_string(),
                source_path.display().to_string(),
            ])?;
            Ok(())
        });
    }

    fn profile_supported_boundary(label: &str, source: String) {
        with_supported_boundary(label, source, |source_path, _| {
            entry(["profile".to_string(), source_path.display().to_string()])?;
            Ok(())
        });
    }

    fn audit_supported_boundary(label: &str, source: String, claim: &str) {
        with_supported_boundary(label, source, |source_path, _| {
            entry([
                "audit".to_string(),
                "--claim".to_string(),
                claim.to_string(),
                source_path.display().to_string(),
            ])?;
            Ok(())
        });
    }

    fn supported_implication_boundary_source() -> String {
        const EXPRESSION_CHAIN_LIMIT: usize = 512;
        let implications = (0..EXPRESSION_CHAIN_LIMIT)
            .map(|_| "0 == 0")
            .collect::<Vec<_>>()
            .join(" implies ");
        format!("theorem at_limit_implication() {{ requires {implications}; ensures 0 == 0; }}\n")
    }

    fn verify_and_profile_supported_boundary(label: &str, source: String) {
        let directory = std::env::temp_dir().join(format!(
            "click-surface-depth-cli-valid-{label}-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let source_path = directory.join("at-limit.click");
        fs::write(&source_path, source).unwrap();

        entry(["verify".to_string(), source_path.display().to_string()])
            .expect("click verify should accept the supported boundary");
        entry(["profile".to_string(), source_path.display().to_string()])
            .expect("click profile should accept the supported boundary");

        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn every_cli_tool_accepts_the_supported_expression_boundary() {
        const EXPRESSION_CHAIN_LIMIT: usize = 512;
        let additions = (0..EXPRESSION_CHAIN_LIMIT)
            .map(|_| "0")
            .collect::<Vec<_>>()
            .join(" + ");
        exercise_supported_boundary(
            "expression",
            format!(
                "theorem at_limit_expression() {{ requires {additions} == 0; ensures 0 == 0; }}\n"
            ),
            "at_limit_expression.ensures_0",
        );
    }

    #[test]
    fn supported_implication_boundary_verifies_and_expands() {
        verify_and_expand_supported_boundary(
            "implication-verify-expand",
            supported_implication_boundary_source(),
            "at_limit_implication.ensures_0",
        );
    }

    #[test]
    fn supported_implication_boundary_profiles() {
        profile_supported_boundary(
            "implication-profile",
            supported_implication_boundary_source(),
        );
    }

    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn supported_implication_boundary_audits() {
        audit_supported_boundary(
            "implication-audit",
            supported_implication_boundary_source(),
            "at_limit_implication.ensures_0",
        );
    }

    #[test]
    fn every_cli_tool_accepts_the_supported_quantifier_boundary() {
        const STRUCTURAL_NESTING_LIMIT: usize = 32;
        let mut quantifier_body = String::from("0 == 0");
        for index in (0..STRUCTURAL_NESTING_LIMIT - 1).rev() {
            quantifier_body = format!("forall (q{index}: Integer) {{ {quantifier_body} }}");
        }
        exercise_supported_boundary(
            "quantifiers",
            format!(
                "theorem at_limit_quantifiers() {{ requires {quantifier_body}; ensures 0 == 0; }}\n"
            ),
            "at_limit_quantifiers.ensures_0",
        );
    }

    #[test]
    fn every_cli_tool_accepts_the_supported_conditional_boundary() {
        const STRUCTURAL_NESTING_LIMIT: usize = 32;
        let nested_conditionals = (0..STRUCTURAL_NESTING_LIMIT - 1)
            .fold("0".to_string(), |body, _| {
                format!("if 0 == 0 {{ {body} }} else {{ 0 }}")
            });
        exercise_supported_boundary(
            "conditionals",
            format!(
                "theorem at_limit_conditionals() {{ requires {nested_conditionals} == 0; ensures 0 == 0; }}\n"
            ),
            "at_limit_conditionals.ensures_0",
        );
    }

    #[test]
    fn supported_proof_boundary_verifies_and_profiles() {
        const STRUCTURAL_NESTING_LIMIT: usize = 32;
        let proof_goal = "0 == 0";
        let mut proof_body = String::from("normalize();");
        for _ in 0..STRUCTURAL_NESTING_LIMIT - 2 {
            proof_body = format!("have 0 == 0 by {{ {proof_body} }} normalize();");
        }
        verify_and_profile_supported_boundary(
            "proof",
            format!("theorem at_limit_proof() {{ ensures {proof_goal} by {{ {proof_body} }} }}\n"),
        );
    }

    #[test]
    fn every_cli_tool_accepts_the_supported_type_boundary() {
        const ALGEBRAIC_TYPE_NESTING_LIMIT: usize = 32;
        let nested_type = (0..ALGEBRAIC_TYPE_NESTING_LIMIT)
            .fold("Integer".to_string(), |type_name, _| {
                format!("BoundaryBox<{type_name}>")
            });
        exercise_supported_boundary(
            "type",
            format!(
                "spec enum BoundaryBox<T> {{ Wrapped(T) }}\n\
                 theorem at_limit_type(value: {nested_type}) {{ ensures 0 == 0; }}\n"
            ),
            "at_limit_type.ensures_0",
        );
    }

    #[test]
    fn every_cli_tool_reports_overdeep_surface_input_without_aborting() {
        const STRUCTURAL_LIMIT: usize = 32;
        const CONTRACT_LET_LIMIT: usize = 128;
        const ALGEBRAIC_TYPE_LIMIT: usize = 32;

        let nested_generic_type = (0..=ALGEBRAIC_TYPE_LIMIT)
            .fold("Integer".to_string(), |type_name, _| {
                format!("Box<{type_name}>")
            });
        let nested_generic_field = (0..=ALGEBRAIC_TYPE_LIMIT)
            .fold("Integer".to_string(), |type_name, _| {
                format!("Box<{type_name}>")
            });

        let directory =
            std::env::temp_dir().join(format!("click-surface-depth-cli-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();

        let sources = [
            (
                "not",
                format!(
                    "theorem too_deep_not() {{ requires {}0 == 0; ensures 0 == 0; }}\n",
                    "not ".repeat(128)
                ),
                "too_deep_not.ensures_0",
            ),
            (
                "implies",
                format!(
                    "theorem too_deep_implies() {{ requires {}; ensures 0 == 0; }}\n",
                    (0..=512)
                        .map(|_| "0 == 0")
                        .collect::<Vec<_>>()
                        .join(" implies ")
                ),
                "too_deep_implies.ensures_0",
            ),
            (
                "add",
                format!(
                    "theorem too_deep_add() {{ requires {} == 0; ensures 0 == 0; }}\n",
                    (0..=1024).map(|_| "0").collect::<Vec<_>>().join(" + ")
                ),
                "too_deep_add.ensures_0",
            ),
            (
                "let",
                format!(
                    "theorem too_deep_let() {{ requires {}; ensures 0 == 0; }}\n",
                    (0..=CONTRACT_LET_LIMIT)
                        .rev()
                        .fold("0 == 0".to_string(), |body, index| {
                            format!("let value{index} = 0; {body}")
                        })
                ),
                "too_deep_let.ensures_0",
            ),
            (
                "quantifier",
                format!(
                    "theorem too_deep_quantifier() {{ requires {}; ensures 0 == 0; }}\n",
                    (0..STRUCTURAL_LIMIT)
                        .rev()
                        .fold("0 == 0".to_string(), |body, index| {
                            format!("forall (q{index}: Integer) {{ {body} }}")
                        })
                ),
                "too_deep_quantifier.ensures_0",
            ),
            (
                "bracket",
                format!(
                    "theorem too_deep_bracket() {{ ensures {} == {}; }}\n",
                    (0..=STRUCTURAL_LIMIT).fold("0".to_string(), |expression, _| {
                        format!("[{expression}]")
                    }),
                    (0..=STRUCTURAL_LIMIT).fold("0".to_string(), |expression, _| {
                        format!("[{expression}]")
                    })
                ),
                "too_deep_bracket.ensures_0",
            ),
            (
                "proof",
                format!(
                    "theorem too_deep_proof() {{ ensures 0 == 0 by {{ {} }} }}\n",
                    (0..=STRUCTURAL_LIMIT).fold("normalize();".to_string(), |body, _| format!(
                        "all {{ true => {{ {body} }} true => {{ normalize(); }} }}"
                    ))
                ),
                "too_deep_proof.ensures_0",
            ),
            (
                "conditional",
                format!(
                    "theorem too_deep_conditional() {{ requires {}; ensures 0 == 0; }}\n",
                    (0..=STRUCTURAL_LIMIT).fold("0".to_string(), |body, _| {
                        format!("if 0 == 0 {{ {body} }} else {{ 0 }}")
                    })
                ),
                "too_deep_conditional.ensures_0",
            ),
            (
                "old",
                format!(
                    "theorem too_deep_old() {{ requires {} == 0; ensures 0 == 0; }}\n",
                    (0..=16).fold("0".to_string(), |expression, _| {
                        format!("old({expression})")
                    })
                ),
                "too_deep_old.ensures_0",
            ),
            (
                "at",
                format!(
                    "theorem too_deep_at() {{ requires {} == 0; ensures 0 == 0; }}\n",
                    (0..=16).fold("0".to_string(), |expression, _| {
                        format!("at(function.entry, {expression})")
                    })
                ),
                "too_deep_at.ensures_0",
            ),
            (
                "call",
                format!(
                    "theorem too_deep_call() {{ requires {} == 0; ensures 0 == 0; }}\n",
                    (0..=16).fold("0".to_string(), |expression, _| {
                        format!("identity({expression})")
                    })
                ),
                "too_deep_call.ensures_0",
            ),
            (
                "constructor",
                format!(
                    "theorem too_deep_constructor() {{ requires {} == 0; ensures 0 == 0; }}\n",
                    (0..=16).fold("0".to_string(), |expression, _| {
                        format!("Box::Wrapped({expression})")
                    })
                ),
                "too_deep_constructor.ensures_0",
            ),
            (
                "generic-type",
                format!(
                    "theorem too_deep_generic(value: {nested_generic_type}) {{ ensures 0 == 0; }}\n"
                ),
                "too_deep_generic.ensures_0",
            ),
            (
                "generic-field",
                format!(
                    "spec enum too_deep<T> {{ Wrapped({nested_generic_field}) }}\n\
                     theorem too_deep_field() {{ ensures 0 == 0; }}\n"
                ),
                "too_deep_field.ensures_0",
            ),
        ];

        for (name, source, claim) in sources {
            let path = directory.join(format!("{name}.click"));
            fs::write(&path, source).unwrap();
            let path_string = path.display().to_string();

            for command in ["verify", "expand", "audit"] {
                let arguments = match command {
                    "verify" => vec![command.to_string(), path_string.clone()],
                    "expand" => vec![
                        command.to_string(),
                        "--claim".to_string(),
                        claim.to_string(),
                        path_string.clone(),
                    ],
                    "audit" => vec![command.to_string(), path_string.clone()],
                    _ => unreachable!(),
                };
                let error = entry(arguments).expect_err("over-deep input must be rejected");
                assert_bounded_depth_error(name, command, &error);
            }

            let error = profile::verify_target_for_test(&path)
                .expect_err("profile must reject over-deep input through its verifier");
            assert_bounded_depth_error(name, "profile", &error);
        }

        fs::remove_dir_all(directory).unwrap();
    }

    fn assert_bounded_depth_error(family: &str, command: &str, error: &str) {
        assert!(
            error.contains("supported depth"),
            "{command} on {family} did not report a supported-depth diagnostic: {error}"
        );
        assert!(
            error.len() < 4096,
            "{command} on {family} produced an unexpectedly large diagnostic"
        );
        assert!(
            error.contains("line ") || error.contains(".click:"),
            "{command} on {family} did not preserve a source location: {error}"
        );
        assert!(
            !error.contains("stack overflow"),
            "{command} on {family} reported a stack overflow: {error}"
        );
    }

    /// A contract that cannot be set up at entry fails before any tactic or C
    /// statement, so the report shows where the contract is written.
    #[test]
    fn a_contract_setup_failure_shows_the_contract_declaration() {
        let directory = std::env::temp_dir().join(format!(
            "click-setup-failure-location-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "void release(int32 *x, int32 i, int32 j) {\n    return;\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        let contract = "verifying \"f.c\";\n\nvoid release(int32 *x, int32 i, int32 j) {\n    requires 0 <= i;\n    requires i <= j;\n    consumes x[0..(i + 1)];\n    consumes x[j..(j + 1)];\n}\n";
        fs::write(&sidecar, contract).unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("contract error:\n"), "{error}");
        assert!(error.contains("signed overflow"), "{error}");
        assert!(
            error.contains("could not open contract entry for `release.body_safety`"),
            "{error}"
        );
        assert!(
            error.contains(&format!(
                "\n  --> {}:3:1\n  3 | void release(int32 *x, int32 i, int32 j) {{\n",
                sidecar.display()
            )),
            "{error}"
        );
        fs::write(
            &sidecar,
            contract.replace(
                "requires i <= j;",
                "requires i <= j;\n    requires j < 100;",
            ),
        )
        .unwrap();
        entry(["verify".to_string(), sidecar.display().to_string()]).unwrap();
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn proven_entry_ownership_overlap_reports_a_contract_error() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for name in [
            "write_resources_reject_proven_overlap.md",
            "kept_pointer_aliases_do_not_duplicate_ownership.md",
            "two_folded_entry_instances_cannot_own_the_same_cell.md",
        ] {
            let path = fixtures.join(name);
            let error = entry(["verify".to_string(), path.display().to_string()]).unwrap_err();
            assert!(error.starts_with("contract error:\n"), "{name}: {error}");
            assert!(
                error.contains("overlapping owned memory resource facts"),
                "{name}: {error}"
            );
        }
    }

    #[test]
    fn symbolic_pointer_conditional_reports_unsupported_in_a_requirement() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("f.c"),
            "int f(int flag, int *p, int *q) { return 0; }\n",
        )
        .unwrap();
        let sidecar = directory.path().join("f.click");
        let verify = |requirement: &str| {
            fs::write(
                &sidecar,
                format!(
                    "verifying \"f.c\";\nint32 f(int32 flag, int32* p, int32* q) {{\n    requires {requirement};\n    ensures result == 0;\n}}\n",
                ),
            )
            .unwrap();
            entry(["verify".to_string(), sidecar.display().to_string()])
        };

        let conditional = "(if flag == 0 { p } else { q }) != 0";
        let error = verify(conditional).unwrap_err();
        assert!(error.starts_with("unsupported:\n"), "{error}");
        assert!(
            error.contains("symbolic choice between distinct pointers"),
            "{error}"
        );
        assert!(error.contains("using `or`"), "{error}");
        assert!(error.contains(conditional), "{error}");
        verify("(flag == 0 and p != 0) or (flag != 0 and q != 0)").unwrap();
        verify(&format!("true or {conditional}")).unwrap();
    }

    #[test]
    fn folded_input_view_overlap_reports_a_contract_error() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("f.c"),
            "void hold(int32 *x, int32 *y) {}\n",
        )
        .unwrap();
        let sidecar = directory.path().join("f.click");
        let verify = |clauses: &str| {
            fs::write(
                &sidecar,
                format!(
                    r#"verifying "f.c";
resource cell(p: int32*) {{ owns p[0]; }}
resource read_cell(p: int32*) {{ views p[0]; }}
resource wrapped_cell(p: int32*) {{ owns cell(p); }}
void hold(int32 *x, int32 *y) {{ {clauses} }}
"#
                ),
            )
            .unwrap();
            entry(["verify".to_string(), sidecar.display().to_string()])
        };
        for (clauses, owner, view) in [
            ("owns cell(x); views cell(x);", "cell(x)", "cell(x)"),
            ("views cell(x); owns cell(x);", "cell(x)", "cell(x)"),
            (
                "requires y == x; owns cell(x); views cell(y);",
                "cell(x)",
                "cell(y)",
            ),
            ("owns cell(x); views x[0];", "cell(x)", "x[0]"),
            (
                "owns cell(x); views read_cell(x);",
                "cell(x)",
                "read_cell(x)",
            ),
            (
                "requires y == x; owns wrapped_cell(x); views read_cell(y);",
                "wrapped_cell(x)",
                "read_cell(y)",
            ),
        ] {
            let error = verify(clauses).unwrap_err();
            assert!(error.starts_with("contract error:\n"), "{error}");
            assert!(error.contains(&format!("`views {view}`")), "{error}");
            assert!(error.contains(&format!("`owns {owner}`")), "{error}");
        }
        verify("views cell(x);").unwrap();
        verify("owns cell(x); views cell(y);").unwrap();
        verify("owns wrapped_cell(x); views read_cell(y);").unwrap();
    }

    #[test]
    fn documented_entry_restrictions_report_contract_errors() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (name, detail) in [
            (
                "program_entry_rejects_preconditions.md",
                "requires no parameters or preconditions",
            ),
            (
                "mutex_use_rejects_consume.md",
                "require preserving owned inputs",
            ),
            (
                "mutex_helper_transfers_rejects_missing_state.md",
                "requires one matching named protected state transfer",
            ),
        ] {
            let path = fixtures.join(name);
            let error = entry(["verify".to_string(), path.display().to_string()]).unwrap_err();
            assert!(error.starts_with("contract error:\n"), "{name}: {error}");
            assert!(error.contains(detail), "{name}: {error}");
        }

        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("startup.c"),
            "int x; int main(void) { return 0; }\n",
        )
        .unwrap();
        let sidecar = directory.path().join("startup.click");
        fs::write(
            &sidecar,
            r#"verifying "startup.c";
resource cell(p: int32*) { field tag: int32; owns p[0]; }
int main() { owns data: cell(&x); }
"#,
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("contract error:\n"), "{error}");
        assert!(
            error.contains("can name only the hosted stdout stream"),
            "{error}"
        );
    }

    #[test]
    fn contract_argument_read_reports_the_missing_view() {
        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/contract_owns_composite_argument_rejects_missing_access.md");
        let error = entry(["verify".to_string(), fixture.display().to_string()]).unwrap_err();
        assert!(error.starts_with("contract error:\n"), "{error}");
        assert!(error.contains("add `views node->left;`"), "{error}");

        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("f.c"),
            "struct node { struct node *left; int32 value; };\nvoid probe(struct node *node) {}\n",
        )
        .unwrap();
        let sidecar = directory.path().join("f.click");
        let verify = |views: &str| {
            fs::write(
                &sidecar,
                format!(
                    r#"verifying "f.c";
resource pair(node: struct node*) {{ owns node->left->left; }}
void probe(struct node *node) {{
    requires node != 0;
    {views}
    owns pair(node->left->left);
}}
"#
                ),
            )
            .unwrap();
            entry(["verify".to_string(), sidecar.display().to_string()])
        };
        for (views, missing) in [
            ("", "node->left"),
            ("views node->left;", "node->left->left"),
        ] {
            let error = verify(views).unwrap_err();
            assert!(error.starts_with("contract error:\n"), "{error}");
            assert!(error.contains("pair(node->left->left)"), "{error}");
            assert!(
                error.contains(&format!("add `views {missing};`")),
                "{error}"
            );
        }
        verify("views node->left;\nviews node->left->left;").unwrap();
    }

    #[test]
    fn contract_with_many_guards_reaches_the_return_obligation() {
        let directory = tempfile::tempdir().unwrap();
        let parameters = (0..14)
            .map(|index| format!("int32 n{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let clauses = (0..14)
            .map(|index| format!("    if n{index} > 0 {{ produces ticket({index}); }}"))
            .collect::<Vec<_>>()
            .join("\n");
        fs::write(
            directory.path().join("f.c"),
            format!("void f({parameters}) {{}}\n"),
        )
        .unwrap();
        let sidecar = directory.path().join("f.click");
        fs::write(
            &sidecar,
            format!(
                "verifying \"f.c\";\nabstract resource ticket(n: int32);\nvoid f({parameters}) {{\n{clauses}\n}}\n"
            ),
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("incomplete proof:\n"), "{error}");
        assert!(error.contains("ticket(0)"), "{error}");
    }

    #[test]
    fn contract_refinement_reports_the_reason_it_cannot_verify() {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
        for (fixture, heading, reason) in [
            (
                "c_named_contract_refinement_rejects_extra_effect.md",
                "contract error",
                "the target contract does not supply the resources required by the source contract",
            ),
            (
                "c_named_contract_refinement_rejects_insufficient_quantity.md",
                "contract error",
                "the target contract does not supply the resources required by the source contract",
            ),
            (
                "c_named_contract_refinement_rejects_unreturned_quantity.md",
                "contract error",
                "the source contract does not return the resources promised by the target contract",
            ),
            (
                "c_named_function_contract_refinement_theorem_requires_unfold.md",
                "tactic error",
                "requires explicit `unfold(contract(callback))` applications",
            ),
            (
                "c_named_function_contract_refinement_rejects_missing_rewrite.md",
                "tactic error",
                "`all` requires a conjunction goal",
            ),
            (
                "c_named_function_contract_refinement_theorem_rejects_false_claim.md",
                "unsuccessful search",
                "result > 0",
            ),
        ] {
            let path = fixtures.join(fixture);
            let error = entry(["verify".to_string(), path.display().to_string()]).unwrap_err();
            assert!(
                error.starts_with(&format!("{heading}:\n")),
                "{fixture}: {error}"
            );
            assert!(error.contains(reason), "{fixture}: {error}");
        }
    }

    #[test]
    fn contract_refinement_without_a_proof_is_incomplete() {
        let directory = tempfile::tempdir().unwrap();
        let sidecar = directory.path().join("f.click");
        fs::write(directory.path().join("f.c"), "int f(void) { return 0; }").unwrap();
        fs::write(
            &sidecar,
            r#"verifying "f.c";
contract int32 Zero() { ensures result == 0; }
int32 f() { ensures result == 0; }
theorem implements_zero() { ensures Zero(&f); }
"#,
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("incomplete proof:\n"), "{error}");
        assert!(
            error.contains("requires an explicit contract-refinement proof"),
            "{error}"
        );
    }

    #[test]
    fn return_clause_failures_report_incomplete_proofs() {
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("f.c");
        let sidecar = directory.path().join("f.click");
        for (c, contract, reason, detail) in [
            (
                "struct node { struct node *child; }; void f(struct node *p) {}",
                "abstract resource ticket(p: struct node*);\nvoid f(struct node* p) { requires p != 0; produces ticket(p->child); }",
                "could not evaluate returned resource `ticket(p->child)`",
                "missing pure fact",
            ),
            (
                "int *first(int *left, int *right) { return left; }",
                "int32* first(int32* left, int32* right) { views *left; views *right as right_input; produces view(*left) from right_input; ensures result == left; }",
                "The selected input `views right[0]` does not establish coverage of `views left[0]`",
                "Requires produces views left[0..1]",
            ),
        ] {
            fs::write(&source, c).unwrap();
            fs::write(&sidecar, format!("verifying \"f.c\";\n{contract}\n")).unwrap();
            let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
            assert!(error.starts_with("incomplete proof:\n"), "{error}");
            assert!(error.contains(reason), "{error}");
            assert!(error.contains(detail), "{error}");
        }
    }

    #[test]
    fn returned_memory_without_promised_initialization_is_an_incomplete_proof() {
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("f.c");
        fs::write(&source, "void init(int *p) {}\n").unwrap();
        let sidecar = directory.path().join("f.click");
        fs::write(
            &sidecar,
            r#"verifying "f.c";
                void init(int32* p) {
                    consumes uninitialized(p[0..1]);
                    produces p[0..1];
                }
            "#,
        )
        .unwrap();
        let verify = || entry(["verify".to_string(), sidecar.display().to_string()]);
        let error = verify().unwrap_err();
        assert!(error.starts_with("incomplete proof:\n"), "{error}");
        assert!(error.contains("has not initialized every byte"), "{error}");
        assert!(error.contains("Requires produces p[0]"), "{error}");

        fs::write(&source, "void init(int *p) { *p = 1; }\n").unwrap();
        verify().expect("the write supplies the promised initialized memory");
    }

    #[test]
    fn contract_closing_identifies_implicit_and_written_tactic_errors() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("f.c"),
            "int32 counter = 0;\nint32 f() { counter = 1; return 1; }\n",
        )
        .unwrap();
        let sidecar = directory.path().join("f.click");
        let verify = |proof: &str| {
            fs::write(
                &sidecar,
                format!("verifying \"f.c\";\nint32 f() {{ ensures result == 1; }}{proof}\n"),
            )
            .unwrap();
            entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err()
        };
        for proof in [
            "",
            " by { step_until(function.exit); }",
            " by { step_until(function.exit); known(); }",
        ] {
            let error = verify(proof);
            assert!(error.starts_with("tactic error:\n"), "{error}");
            assert!(error.contains("write to `&counter`"), "{error}");
            assert!(
                error.contains("refused by: implicit step (contract closing)"),
                "{error}"
            );
            assert!(!error.contains("tactic@"), "{error}");
        }
        let traced = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "f".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(traced.starts_with("tactic error:\n"), "{traced}");
        assert!(
            traced.contains("refused by: implicit step (contract closing)")
                && traced.contains("location: implicit step (contract closing)"),
            "{traced}"
        );

        let error =
            verify(" by { step_until(function.exit); known(); known(); known(); known(); }");
        assert!(error.starts_with("tactic error:\n"), "{error}");
        assert!(error.contains("write to `&counter`"), "{error}");
        assert!(error.contains("refused by: `known`"), "{error}");
        assert!(!error.contains("refused by: implicit step"), "{error}");
    }

    /// A failure at a C operation names that statement. A proof failure with
    /// no site of its own is located at the declaration being verified.
    #[test]
    fn proof_failures_show_the_c_statement_or_the_declaration() {
        let directory = std::env::temp_dir().join(format!(
            "click-ambient-failure-location-{}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("f.c"),
            "int32 leak() {\n    int32* item = malloc(4);\n    if (item == 0) {\n        return -1;\n    }\n    return 0;\n}\n",
        )
        .unwrap();
        let sidecar = directory.join("f.click");
        fs::write(
            &sidecar,
            "verifying \"f.c\";\n\nint32 leak() {\n    ensures result == -1 or result == 0;\n}\n",
        )
        .unwrap();
        let leak = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(leak.contains("neither returned nor freed"), "{leak}");
        assert!(
            leak.contains("\n  C statement at f.c:6:5\n  `return 0;`"),
            "{leak}"
        );

        fs::write(
            &sidecar,
            "theorem unequal(left: int32, right: int32) {\n    ensures left == right;\n}\n",
        )
        .unwrap();
        let theorem = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        fs::remove_dir_all(&directory).unwrap();
        assert!(
            theorem.contains(&format!(
                "\n  --> {}:1:1\n  1 | theorem unequal(left: int32, right: int32) {{\n",
                sidecar.display()
            )),
            "{theorem}"
        );
    }
}
