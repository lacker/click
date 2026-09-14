use std::env;

#[path = "click-audit.rs"]
#[allow(dead_code)]
mod audit;
#[path = "click-expand.rs"]
#[allow(dead_code)]
mod expand;
#[path = "click-import.rs"]
#[allow(dead_code)]
mod import;
#[path = "click-profile.rs"]
#[allow(dead_code)]
mod profile;
#[path = "click-verify.rs"]
#[allow(dead_code)]
mod verify;

const USAGE: &str = "\
usage: click <COMMAND> [OPTIONS]\n\n\
commands:\n  \
  verify   verify a sidecar, proof unit, project, or examples directory\n  \
  profile  measure verification and identify slow tactics\n  \
  expand   replace one smart tactic with its checked simple certificate\n  \
  audit    check expansion across a project or repository\n  \
  import   prepare and lock compiler-selected sources";

fn main() {
    if let Err(message) = entry(env::args().skip(1)) {
        eprintln!("click: {message}");
        std::process::exit(1);
    }
}

fn entry(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        return Err(USAGE.to_string());
    };
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

    #[test]
    fn rejects_an_unknown_view_semantics_selection() {
        assert!(
            click::cli::parse_view_semantics(Some("stable_loans"))
                .unwrap_err()
                .contains("CLICK_VIEW_SEMANTICS must be `legacy` or `stable-loans`")
        );
    }

    /// `CLICK_VIEW_SEMANTICS` reaches ordinary command verification, not only
    /// the fixture harnesses (`issues/fix-views.md`, finding F15). The sidecar
    /// below is refused in both modes, but for different reasons: legacy frames
    /// the store by the owned footprint, while the candidate stable-view
    /// semantics reports the conflict with the contract input view's loan. A
    /// command that ignored the variable would print the legacy message twice.
    #[test]
    fn verify_honors_the_view_semantics_environment_variable() {
        let directory = std::env::temp_dir().join(format!(
            "click-view-semantics-switch-{}",
            std::process::id()
        ));
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
        let run = || entry(["verify".to_string(), sidecar.display().to_string()]).unwrap_err();

        // SAFETY: the gate runs every test in its own nextest process
        // (`scripts/check.sh`), so nothing else in this process reads the
        // environment while these two calls change it, and no verification
        // thread has been started yet at either call.
        unsafe { env::remove_var(click::cli::VIEW_SEMANTICS_VARIABLE) };
        let stable = run();
        unsafe { env::set_var(click::cli::VIEW_SEMANTICS_VARIABLE, "legacy") };
        let legacy = run();
        unsafe { env::remove_var(click::cli::VIEW_SEMANTICS_VARIABLE) };

        assert!(legacy.contains("outside the owned footprint"), "{legacy}");
        assert!(
            !legacy.contains("conflicts with an active loan"),
            "{legacy}"
        );
        assert!(
            stable.contains("stable-view memory access conflicts with an active loan"),
            "{stable}"
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
}
