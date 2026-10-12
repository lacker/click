use std::env;

#[path = "click/git.rs"]
mod git;
#[path = "click/version_dispatch.rs"]
mod version_dispatch;
#[path = "click/version_manager.rs"]
mod version_manager;

#[path = "click-audit.rs"]
mod audit;
#[path = "click-expand.rs"]
mod expand;
#[path = "click-import.rs"]
mod import;
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
  import   prepare and lock compiler-selected sources\n  \
  install  download a Click version\n  \
  use      pin a version for the current project\n  \
  default  select the global fallback version\n  \
  versions list installed versions";

fn main() {
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
    let message = click::surface::display_rust_names(&message);
    if message.starts_with("proof error:")
        || message.starts_with("proof error in `")
        || message.starts_with("syntax error:")
        || message.starts_with("type error:")
        || message.starts_with("internal error:")
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
        "import" => import::entry_with(arguments),
        "install" | "use" | "default" | "versions" => {
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

    /// The command-line front end verifies under the shipped stable-view
    /// semantics: a `views` of a file-scope cell is a borrow for the call, so
    /// a store into it is refused as a conflict with that loan rather than as
    /// a store outside the owned footprint.
    #[test]
    fn verify_refuses_a_store_into_a_viewed_global_with_the_loan_message() {
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
            "verifying \"viewed_global.c\";\nvoid set_second() {\n    views words[1..2];\n    ensures words[1] == 7 by auto;\n}\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.contains("stable-view memory access conflicts with an active loan"),
            "{error}"
        );
        assert!(!error.contains("outside the owned footprint"), "{error}");
        assert!(error.starts_with("proof error:"), "{error}");
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
            "verifying \"f.c\";\nint32 f() { ensures result == 1 by auto; }\n",
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
             \x20       execute();\n\
             \x20       simp();\n\
             \x20   }\n\
             }\n\
             void g(int32* p) { owns p[0..1]; ensures p[0] == 2 by { execute(); simp(); } }\n",
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
            !by_label.contains("execute();\n        simp();"),
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
        let several = expand(&format!("{path}:9"), "several.click").unwrap_err();
        assert!(
            several.contains(&format!(
                "{path}:9: 2 claims cover this line; add the column of one of them:\n  {path}:9:20 `g.owns_0`\n  {path}:9:34 `g.ensures_0`"
            )),
            "{several}"
        );
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
                    "verifying \"f.c\";\nint32 f() {{\n    ensures result == 0;\n}} by {{\n    step(); step(); step();\n    loop {{ decreases 5 - i; invariant i >= 0; invariant i <= 4;{preserve} }}\n    execute(); simp();\n}}\n"
                ),
            )
            .unwrap();
        };
        let bound = "  `step()` is missing prerequisite\n  the store to `items[i]` may write outside `items`\n  could not show `0 <= i && i < 4` from the facts `i <= 4`, `i >= 0`\n  C operation\n  *(items + i) = 7;\n  C statement at f.c:6:9\n  `items[i] = 7;`";

        write_proof("");
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.starts_with(&format!(
                "proof error:\n  `f.contract` tactic 3 (`loop`), preserving the invariants through the loop body\n{bound}"
            )),
            "{error}"
        );

        write_proof(" preserve by { step(); step(); simp(); }");
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(
            error.starts_with(&format!(
                "proof error:\n  `f.contract` tactic 3 (`loop`), `preserve` tactic 0\n{bound}"
            )),
            "{error}"
        );
        for kernel_spelling in ["can-store(", "snapshot#", "local:items", "value A"] {
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
        let three_steps = "} by {\n    step(); step(); step(); simp();\n}\n";

        let store = verify(
            "int32 store() {\n    ensures result == 0;\n} by {\n    step(); step(); step();\n    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }\n    execute(); simp();\n}\n",
        );
        assert!(
            store.contains(
                "could not show `i >= 0 && i < 4` from the facts `i <= 4`, `i >= 0`\n  C statement at f.c:10:9\n  `items[i].x = 7;`"
            ),
            "{store}"
        );
        assert!(!store.contains("the field store"), "{store}");

        let overflow = verify(&format!(
            "int32 add(int32 a, int32 b) {{\n    ensures result == a + b;\n{three_steps}"
        ));
        assert!(
            overflow.contains(
                "`step()` produced undefined behavior\n  signed overflow\n  C statement at f.c:18:5\n  `total = a + b;`\n"
            ),
            "{overflow}"
        );

        let call = verify(&format!(
            "int32 callee(int32 n) {{\n    requires n >= 0;\n    ensures result == n;\n}}\nint32 caller(int32 n) {{\n    ensures result == n + 1;\n{three_steps}"
        ));
        assert!(
            call.contains("`step()` is missing prerequisite (callee precondition)"),
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
            "# Located\n\nProse before the blocks.\n\n```c filename=add.c\nint32 add(int32 a, int32 b) {\n    int32 total;\n    total = a + b;\n    return total;\n}\n```\n\n```click\nverifying \"add.c\";\nint32 add(int32 a, int32 b) {\n    ensures result == a + b;\n} by {\n    step(); step(); step(); simp();\n}\n```\n\n```expect\nfail: signed overflow\n```\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), path.display().to_string()]).unwrap_err();
        assert!(
            error.contains(
                "\n  signed overflow\n  C statement at located.md:8:5\n  `total = a + b;`\n"
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
            mdtest("int32 f() { ensures result == 1 by auto; }", "pass"),
        )
        .unwrap();
        let failing = directory.join("failing.md");
        fs::write(
            &failing,
            mdtest(
                "int32 f() { ensures result == 1; } by { step(); step(); simp(); }",
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
        assert!(error.starts_with("proof error:"), "{error}");
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
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by { step(); step(); simp(); }\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("proof error:"), "{error}");
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
        assert!(traced.starts_with("proof error:\n"), "{traced}");
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
        assert!(!traced.contains("stage: proof step"), "{traced}");
        assert!(!traced.contains("To get a trace:"), "{traced}");

        fs::write(
            directory.join("f.c"),
            "int32 f() { int32 x; x = 1; return x; }\n",
        )
        .unwrap();
        fs::write(
            &sidecar,
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by { step(); have 0 == 1 by { normalize(); } step(); simp(); }\n",
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
        assert!(!nested.contains("have body tactic"), "{nested}");
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
                "verifying \"identity.c\";\nint32 identity(int32 x) {{\n    ensures result == x;\n}} by {{\n    have x <= x by {{\n{body}    }}\n    execute();\n    simp();\n}}\n"
            )
        };
        let count_up = |phase: &str| {
            format!(
                "verifying \"count_up.c\";\nint32 count_to_n(int32 n) {{\n    requires n >= 0 and n <= 2147483647;\n    ensures result == n;\n}} by {{\n    step();\n    step();\n    loop {{\n        decreases n - i;\n        invariant i >= 0;\n        invariant i <= n;\n        initialize by {{\n{phase}        }}\n        preserve by {{\n            step();\n            close_invariants();\n        }}\n    }}\n    step();\n    simp();\n}}\n"
            )
        };
        // Each case's `assumption()` must fail. A goal that is a mirrored
        // spelling of a fact (`0 <= n` beside `requires n >= 0`, or `i <= n`
        // with `i == 0`) is closed by `assumption`, so the loop cases ask for
        // `-1 < n`, which is true but no spelling of any fact.
        let cases = [
            (
                "if_arm",
                identity(
                    "        have x == x by simp;\n        if x > 0 {\n            simp();\n        } else {\n            assumption();\n        }\n",
                ),
                10,
            ),
            (
                "cases_arm",
                identity(
                    "        have x > 0 or not (x > 0) by {\n            if x > 0 {\n                assumption();\n            } else {\n                assumption();\n            }\n        }\n        cases { x > 0 => {\n            simp();\n        } not (x > 0) => {\n            assumption();\n        } }\n",
                ),
                16,
            ),
            (
                "if_continuation",
                identity(
                    "        if x > 0 {\n            have x == x by simp;\n            have x == x by simp;\n        } else {\n            have x == x by simp;\n        }\n        assumption();\n",
                ),
                12,
            ),
            (
                "initialize_helper",
                count_up(
                    "            have -1 < n by {\n                have n == n by simp;\n                assumption();\n            }\n            simp();\n",
                ),
                15,
            ),
            (
                "initialize_invariant_body",
                count_up(
                    "            have i >= 0 by simp;\n            have -1 < n by {\n                have n == n by simp;\n                assumption();\n            }\n",
                ),
                16,
            ),
            (
                "initialize_shared_script",
                count_up("            have n == n by simp;\n            assumption();\n"),
                14,
            ),
        ];
        for (name, source, line) in cases {
            let sidecar = directory.join(format!("{name}.click"));
            fs::write(&sidecar, &source).unwrap();
            let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
            assert_eq!(
                source.lines().nth(line - 1).map(str::trim),
                Some("assumption();"),
                "{name}"
            );
            assert!(
                error.contains(&format!("\n\ntactic@{line}:\n  assumption();")),
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
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by {\n    step();\n    have exists (x: int32) { x == 0 } by {\n        obtain (x: int32) {\n            x == 0\n        };\n    }\n    simp();\n}\n",
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
            traced.contains("requirement `exists (x: int32) { x == 0 }` not satisfied"),
            "{traced}"
        );
        assert!(
            traced.contains("requires: exists (x: int32) { x == 0 }"),
            "{traced}"
        );
        assert_eq!(traced.matches("\ngoal:").count(), 1, "{traced}");
        assert!(
            traced.contains("tactic@5:\n  obtain (x: int32) {\n      x == 0\n  };"),
            "{traced}"
        );
        assert!(!traced.contains("\nstep: "), "{traced}");
        assert!(traced.contains("obtain (x: int32) {\n"), "{traced}");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    #[ignore = "nightly: 6s in the parallel gate"]
    fn tautological_ensure_preserves_population_certification() {
        let directory =
            std::env::temp_dir().join(format!("click-certification-trace-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("shared_parent.c"),
            include_str!("../../design/shared-heap-probes/shared_parent.c"),
        )
        .unwrap();
        let sidecar = directory.join("shared_parent.click");
        let source = include_str!("../../design/shared-heap-probes/shared_parent.click");
        let source = source.replacen(
            "    produces p->kid;\n",
            "    produces p->kid;\n    ensures old(p->kid) == old(p->kid);\n",
            1,
        );
        assert!(source.contains("ensures old(p->kid) == old(p->kid);"));
        fs::write(&sidecar, source).unwrap();
        entry(["verify".to_string(), sidecar.display().to_string()]).unwrap();
        entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "parent_detach".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap();
        fs::remove_dir_all(directory).unwrap();
    }

    // Simple claim closers must perform the same checked return exchange as
    // simp, including a consuming contract with no returned resource claim.
    #[test]
    #[ignore = "nightly: 10s in the parallel gate"]
    fn shared_population_release_expansion_retains_lifetime() {
        let directory = std::env::temp_dir().join(format!(
            "click-population-release-expansion-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        fs::write(
            directory.join("shared_parent.c"),
            include_str!("../../design/shared-heap-probes/shared_parent.c"),
        )
        .unwrap();
        let sidecar = directory.join("shared_parent.click");
        let source = include_str!("../../design/shared-heap-probes/shared_parent.click");
        fs::write(&sidecar, source).unwrap();
        entry(["verify".to_string(), sidecar.display().to_string()]).unwrap();
        let release_end = source.find("void parent_attach(").unwrap();
        let simp = source[..release_end].rfind("        simp();").unwrap();
        let line = source[..simp].bytes().filter(|byte| *byte == b'\n').count() + 1;
        entry([
            "expand".to_string(),
            "--in-place".to_string(),
            format!("{}:{line}:9", sidecar.display()),
        ])
        .unwrap();
        entry(["verify".to_string(), sidecar.display().to_string()]).unwrap();
        fs::remove_dir_all(directory).unwrap();
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
            "verifying \"f.c\";\nint32 f() { ensures result == 0; } by { step(); step(); simp(); }\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(error.starts_with("proof error:"), "{error}");
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

    #[test]
    fn trace_names_source_values_and_distinguishes_saved_loads() {
        let directory =
            std::env::temp_dir().join(format!("click-trace-source-names-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("calls.c"),
            "int32 child(int32 *a, int32 *visited, int32 x) { visited[0] = 1; return 1; }\nint32 parent(int32 *a, int32 *visited, int32 cur) { return child(a, visited, a[cur]); }\n",
        )
        .unwrap();
        let sidecar = directory.join("calls.click");
        fs::write(
            &sidecar,
            r#"verifying "calls.c";
int32 child(int32 *a, int32 *visited, int32 x) {
    views a[0..2];
    owns visited[0..1];
    requires separate(memory(a[0..2]), memory(visited[0..1]));
    ensures result == 1 by { execute(); simp(); }
    ensures result != 0 implies exists (z: int32) { z == x } by {
        execute(); intro(); witness { z: x }; normalize();
    }
}
int32 parent(int32 *a, int32 *visited, int32 cur) {
    views a[0..2];
    owns visited[0..1];
    requires separate(memory(a[0..2]), memory(visited[0..1]));
    requires 0 <= cur;
    requires cur < 2;
    ensures result == 1;
} by {
    let r = step(child(a, visited, a[cur]), { });
    have r != 0 by { simp(); }
    have defined(a[cur]) by { simp(); }
    have exists (z: int32) { z == a[cur] } by {
        extract(exists (z: int32) { z == a[cur] });
        assumption();
    }
    step(); simp();
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
        .unwrap_err();
        assert!(report.contains("goal: ∃z:CInt32."), "{report}");
        assert!(!report.contains("recent premises"), "{report}");
        assert!(report.contains("adds: r == 1"), "{report}");
        assert!(
            report.contains("tactic@19: let r = step(child("),
            "{report}"
        );
        // Both facts are now printed. Keep the saved read's snapshot visible
        // in the implication rather than confusing it with the current goal.
        assert!(report.contains("adds: validated-composition"), "{report}");
        assert!(report.contains("is false ⇒ ∃z:CInt32."), "{report}");
        assert!(report.contains("read<Bits32>(snapshot#"), "{report}");
        assert!(
            !report.contains("checked fact(s) with no exact Click spelling"),
            "{report}"
        );
        assert_eq!(report.matches("goal: ∃z:CInt32.").count(), 1, "{report}");
        assert!(
            !report.contains("snapshot identity (internal):"),
            "{report}"
        );
        assert!(!report.contains("v1000001"), "{report}");
        fs::remove_dir_all(directory).unwrap();
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
        rewrite(p == q);
        assumption();
    }
}
"#,
        )
        .unwrap();
        let ordinary = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        let ordinary_goal = ordinary
            .lines()
            .find_map(|line| line.trim().strip_prefix("goal: "))
            .unwrap();
        let report = entry([
            "verify".to_string(),
            "--trace-proof".to_string(),
            "bad".to_string(),
            sidecar.display().to_string(),
        ])
        .unwrap_err();
        assert!(
            report.contains(&format!("goal: {ordinary_goal}")),
            "{report}"
        );
        assert_eq!(report.matches("goal:").count(), 1, "{report}");
        let checked = report.lines().find(|line| line.contains("goal:")).unwrap();
        assert!(checked.contains("tag("), "{report}");
        assert!(checked.contains("array-ref<int32>(snapshot#1,"), "{report}");
        assert!(checked.contains("ptr<int32*>("), "{report}");
        assert!(
            report.contains("snapshot#1 = initial empty memory"),
            "{report}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
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
    let r = step(child(a, b, n, a[i]), {});
    have defined(at(before_call, a[i])) by { simp(); }
    have exists (path: Path) {
        pick(at(before_call, a[i]), path) == at(before_call, a[i])
    } by {
        assumption();
    }
    step(); simp();
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
            "verifying \"calls.c\";\nvoid read(int32* p) { owns p[0..1]; } by { execute(); simp(); }\nvoid caller(int32* second) { ensures second == second; } by { step(); simp(); }\n",
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
            "verifying \"goal.c\";\nint32 bump(int32 x, int32 j, int32 y) {\n    requires 0 <= x and x <= j;\n    requires j < 10;\n    requires y > 3;\n    ensures result == x + 2;\n} by { execute(); simp(); }\n",
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
            "verifying \"case.c\";\nint32 pick(int32 x, int32 y, int32 z) {\n    requires x < 10;\n    requires z > 3;\n    ensures result == 0;\n} by {\n    if y > 3 { execute(); simp(); } else { execute(); simp(); }\n}\n",
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
        have y == x by { simp(); }
        assumption();
    }
}
theorem bad(x: int32, y: int32) {
    requires x == y;
    ensures x == 0 by {
        have y == x by { simp(); }
        have x == 0 by { normalize(); }
        assumption();
    }
}
theorem arms(x: int32) {
    ensures x == x by {
        if x == 0 {
            have x == 0 by { assumption(); }
        } else {
            have x != 0 by { assumption(); }
        }
        normalize();
    }
}
int32 f() { ensures result == 2; } by { step(); simp(); }
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
                && wrong.contains("takes the name of a function or theorem"),
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
            "verifying \"f.c\";\ntheorem f(x: int32) { ensures x == x by { normalize(); } }\nint32 f() { ensures result == 1; } by { step(); simp(); }\n",
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
            "verifying \"f.c\";\nint32 f() { ensures result == 1; } by { step(); simp(); }\nint32 g() { ensures result == 2; } by { step(); step(); simp(); }\n",
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

        // The Click block body starts on line 14; the labeled `have` is
        // its third line, line 16 of the file.
        fs::write(
            &path,
            mdtest(
                valid_c,
                "verifying \"inc.c\";\nint32 inc(int32 x) {\n    ensures result == x by { have same: x == x by { simp(); } step(); simp(); }\n}",
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
        entry(["import".to_string(), "--help".to_string()]).unwrap();
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
        arithmetic() using { n <= 10; }
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
        .expect("click expand should emit the checked arithmetic certificate");
        let expanded = fs::read_to_string(&expanded_path).unwrap();
        assert!(expanded.contains("arithmetic_certificate"), "{expanded}");
        assert!(!expanded.contains("arithmetic()"), "{expanded}");

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
                assert!(expanded.contains("integer_product_bounds bounds [0, 1, 2, 3]"));
                assert!(
                    !expanded.contains("execute();"),
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
        format!(
            "theorem at_limit_implication() {{ requires {implications}; ensures 0 == 0 by auto; }}\n"
        )
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
                "theorem at_limit_expression() {{ requires {additions} == 0; ensures 0 == 0 by auto; }}\n"
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
                "theorem at_limit_quantifiers() {{ requires {quantifier_body}; ensures 0 == 0 by auto; }}\n"
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
                "theorem at_limit_conditionals() {{ requires {nested_conditionals} == 0; ensures 0 == 0 by auto; }}\n"
            ),
            "at_limit_conditionals.ensures_0",
        );
    }

    #[test]
    fn supported_proof_boundary_verifies_and_profiles() {
        const STRUCTURAL_NESTING_LIMIT: usize = 32;
        let mut proof_goal = String::from("0 == 0");
        let mut proof_body = String::from("normalize();");
        for _ in 0..STRUCTURAL_NESTING_LIMIT - 2 {
            proof_goal.push_str(" and 0 == 0");
            proof_body = format!("both {{ {proof_body} }} and {{ normalize(); }}");
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
                 theorem at_limit_type(value: {nested_type}) {{ ensures 0 == 0 by auto; }}\n"
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
                        "both {{ {body} }} and {{ normalize(); }}"
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
        fs::write(
            &sidecar,
            "verifying \"f.c\";\n\nvoid release(int32 *x, int32 i, int32 j) {\n    requires 0 <= i;\n    requires i <= j;\n    consumes x[0..(i + 1)];\n    consumes x[j..(j + 1)];\n} by {\n    execute();\n    simp();\n}\n",
        )
        .unwrap();
        let error = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        fs::remove_dir_all(&directory).unwrap();
        assert!(
            error.starts_with("proof error:\n  `release.contract` setup failed\n"),
            "{error}"
        );
        assert!(
            error.contains(&format!(
                "\n  --> {}:3:1\n  3 | void release(int32 *x, int32 i, int32 j) {{\n",
                sidecar.display()
            )),
            "{error}"
        );
    }

    /// A proof failure with no site of its own is located by what was being
    /// verified: the written tactic being checked, or else the declaration.
    #[test]
    fn a_proof_failure_without_a_site_shows_the_tactic_or_the_declaration() {
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
            "verifying \"f.c\";\n\nint32 leak() {\n    ensures result == -1 or result == 0;\n} by {\n    execute();\n    simp();\n}\n",
        )
        .unwrap();
        let leak = entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();
        assert!(leak.contains("neither returned nor freed"), "{leak}");
        assert!(leak.contains("\n\ntactic@7:\n  simp();"), "{leak}");

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
