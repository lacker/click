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
}
