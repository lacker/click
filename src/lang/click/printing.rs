use super::diagnostics::{
    describe_code_region_ref, describe_contract_expression, describe_contract_segment,
};
use super::*;

pub(super) fn source_click_proposition(proposition: &ClickProposition) -> String {
    fn at_precedence(proposition: &ClickProposition, required: u8) -> String {
        let (precedence, source) = match proposition {
            ClickProposition::Implies(left, right) => (
                1,
                format!(
                    "{} implies {}",
                    at_precedence(left, 2),
                    at_precedence(right, 1)
                ),
            ),
            ClickProposition::Or(left, right) => (
                2,
                format!("{} or {}", at_precedence(left, 2), at_precedence(right, 3)),
            ),
            ClickProposition::And(left, right) => (
                3,
                format!("{} and {}", at_precedence(left, 3), at_precedence(right, 4)),
            ),
            ClickProposition::Not(body) => (4, format!("not {}", at_precedence(body, 4))),
            ClickProposition::ForAll { c_type, name, body } => (
                5,
                format!(
                    "forall ({name}: {}) {{ {} }}",
                    describe_c0_type(*c_type),
                    at_precedence(body, 0)
                ),
            ),
            ClickProposition::Exists { c_type, name, body } => (
                5,
                format!(
                    "exists ({name}: {}) {{ {} }}",
                    describe_c0_type(*c_type),
                    at_precedence(body, 0)
                ),
            ),
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => (
                5,
                format!(
                    "({}..{}).all(|{item}| {{ {} }})",
                    describe_contract_expression(start),
                    describe_contract_expression(end),
                    at_precedence(body, 0)
                ),
            ),
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => (
                5,
                format!(
                    "({}..{}).any(|{item}| {{ {} }})",
                    describe_contract_expression(start),
                    describe_contract_expression(end),
                    at_precedence(body, 0)
                ),
            ),
            proposition => (
                5,
                super::diagnostics::describe_click_proposition(proposition),
            ),
        };
        if precedence < required {
            format!("({source})")
        } else {
            source
        }
    }

    at_precedence(proposition, 0)
}

pub fn format_proof_tactics(tactics: &[ProofTactic]) -> Result<String, CertificateError> {
    let certificate = SimpleProof::from_proof_tactics(tactics)?;
    Ok(format_simple_proof(&certificate))
}

pub(super) fn format_partial_tactic_sequence(tactics: &[ProofTactic]) -> String {
    let mut output = String::new();
    write_tactics(&mut output, tactics, 0);
    output.pop();
    output
}

pub fn format_simple_proof(certificate: &SimpleProof) -> String {
    let mut output = String::from("by {\n");
    write_tactics(&mut output, &certificate.to_proof_tactics(), 1);
    output.push('}');
    output
}

fn write_tactics(output: &mut String, tactics: &[ProofTactic], indent: usize) {
    for tactic in tactics {
        write_tactic(output, tactic, indent);
    }
}

fn write_tactic(output: &mut String, tactic: &ProofTactic, indent: usize) {
    let prefix = "    ".repeat(indent);
    match tactic {
        ProofTactic::Mark(name) => line(output, &prefix, &format!("mark {name};")),
        ProofTactic::Step => line(output, &prefix, "step();"),
        ProofTactic::StepUsing(premises) => {
            line(output, &prefix, "step() using {");
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::UnfoldPredicate(name) => {
            line(output, &prefix, &format!("unfold({name});"));
        }
        ProofTactic::UnfoldResource(resource) => line(
            output,
            &prefix,
            &format!("unfold({});", format_resource_call(resource)),
        ),
        ProofTactic::FoldResource(resource) => line(
            output,
            &prefix,
            &format!("fold({});", format_resource_call(resource)),
        ),
        ProofTactic::Induct {
            parameter,
            hypothesis,
        } => line(
            output,
            &prefix,
            &format!("induct({parameter}) as {hypothesis};"),
        ),
        ProofTactic::ApplyInduction {
            hypothesis,
            argument,
        } => line(
            output,
            &prefix,
            &format!(
                "apply({hypothesis}({}));",
                describe_contract_expression(argument)
            ),
        ),
        ProofTactic::CloseInduction => line(output, &prefix, "simp();"),
        ProofTactic::ApplyTheorem(application) => line(
            output,
            &prefix,
            &format!("apply({});", format_theorem_application(application)),
        ),
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "apply({}) using {{",
                    format_theorem_application(application)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Have(have) => {
            output.push_str(&prefix);
            output.push_str("have ");
            output.push_str(&source_click_proposition(&have.proposition));
            output.push(' ');
            write_proof(output, &have.proof, indent);
            output.push('\n');
        }
        ProofTactic::Open(open) => {
            line(
                output,
                &prefix,
                &format!("open({}) {{", format_resource_call(&open.resource)),
            );
            write_tactics(output, &open.tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::If(proof_if) => {
            output.push_str(&prefix);
            output.push_str("if ");
            output.push_str(&source_click_proposition(&proof_if.condition));
            output.push_str(" {\n");
            write_tactics(output, &proof_if.then_tactics, indent + 1);
            line(output, &prefix, "} else {");
            write_tactics(output, &proof_if.else_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Cases(proof_cases) => {
            output.push_str(&prefix);
            output.push_str("cases (");
            output.push_str(&source_click_proposition(&proof_cases.disjunction));
            output.push_str(") {\n");
            write_tactics(output, &proof_cases.left_tactics, indent + 1);
            line(output, &prefix, "} {");
            write_tactics(output, &proof_cases.right_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Branch(proof_branch) => {
            line(output, &prefix, "branch {");
            if let Some(assertions) = &proof_branch.ensuring {
                line(output, &"    ".repeat(indent + 1), "ensuring {");
                for assertion in assertions {
                    let text = match assertion {
                        ProofAssertion::Fact(fact) => {
                            format!("fact {};", source_click_proposition(fact))
                        }
                        ProofAssertion::Resource(resource) => format!(
                            "{} {};",
                            match resource_access(resource) {
                                ResourceAccessMode::Own => "owns",
                                ResourceAccessMode::View => "views",
                            },
                            format_resource_target(resource)
                        ),
                    };
                    line(output, &"    ".repeat(indent + 2), &text);
                }
                line(output, &"    ".repeat(indent + 1), "}");
            }
            line(output, &"    ".repeat(indent + 1), "then {");
            write_tactics(output, &proof_branch.then_tactics, indent + 2);
            line(output, &"    ".repeat(indent + 1), "}");
            line(output, &"    ".repeat(indent + 1), "else {");
            write_tactics(output, &proof_branch.else_tactics, indent + 2);
            line(output, &"    ".repeat(indent + 1), "}");
            line(output, &prefix, "}");
        }
        ProofTactic::Loop(loop_clause) => {
            line(
                output,
                &prefix,
                &format!(
                    "loop{} {{",
                    loop_clause
                        .label()
                        .map(|label| format!(" as {label}"))
                        .unwrap_or_default()
                ),
            );
            let body_prefix = "    ".repeat(indent + 1);
            if let Some(decreases) = loop_clause.decreases() {
                line(
                    output,
                    &body_prefix,
                    &format!("decreases {};", describe_contract_expression(decreases)),
                );
            }
            for item in loop_clause.items() {
                match item.kind() {
                    StructuralItemKind::Invariant => {
                        output.push_str(&body_prefix);
                        output.push_str("invariant");
                        output.push(' ');
                        output.push_str(&source_click_proposition(
                            item.proposition().expect("proposition structural item"),
                        ));
                        if item.kind() == StructuralItemKind::Invariant {
                            output.push_str(";\n");
                        } else {
                            output.push(' ');
                            write_proof(output, item.proof(), indent + 1);
                            output.push('\n');
                        }
                    }
                    StructuralItemKind::Effect => {
                        write_structural_effect(output, item, indent + 1);
                    }
                    StructuralItemKind::StepEffect => {
                        line(output, &body_prefix, "step {");
                        write_structural_effect(output, item, indent + 2);
                        line(output, &body_prefix, "}");
                    }
                }
            }
            if let Some(proof) = loop_clause.initialize_proof() {
                output.push_str(&body_prefix);
                output.push_str("initialize ");
                write_proof(output, proof, indent + 1);
                output.push('\n');
            }
            if let Some(proof) = loop_clause.preserve_proof() {
                output.push_str(&body_prefix);
                output.push_str("preserve ");
                write_proof(output, proof, indent + 1);
                output.push('\n');
            }
            line(output, &prefix, "}");
        }
        ProofTactic::ObserveResource(resource) => line(
            output,
            &prefix,
            &format!("observe({});", format_resource_call(resource)),
        ),
        ProofTactic::Witness(witness) => line(
            output,
            &prefix,
            &format!(
                "witness({} = {});",
                witness.name,
                describe_contract_expression(&witness.value)
            ),
        ),
        ProofTactic::Choose(choice) => line(
            output,
            &prefix,
            &format!(
                "choose({} from {});",
                choice.name,
                format_fact_source(&choice.source)
            ),
        ),
        ProofTactic::Assumption => line(output, &prefix, "assumption();"),
        ProofTactic::Extract(proposition) => line(
            output,
            &prefix,
            &format!("extract({});", source_click_proposition(proposition)),
        ),
        ProofTactic::Normalize => line(output, &prefix, "normalize();"),
        ProofTactic::Intro => line(output, &prefix, "intro();"),
        ProofTactic::Split => line(output, &prefix, "split();"),
        ProofTactic::Left => line(output, &prefix, "left();"),
        ProofTactic::Right => line(output, &prefix, "right();"),
        ProofTactic::Enumerate => line(output, &prefix, "enumerate();"),
        ProofTactic::Contradiction(fact) => line(
            output,
            &prefix,
            &format!("contradiction({});", source_click_proposition(fact)),
        ),
        ProofTactic::SimpUsing(simp) => {
            write_using_premises(output, "simp()", &simp.premises, indent)
        }
        ProofTactic::CloseInvariants => line(output, &prefix, "close_invariants();"),
        ProofTactic::Rewrite(equality) => line(
            output,
            &prefix,
            &format!("rewrite({});", source_click_proposition(equality)),
        ),
        ProofTactic::Transport { source, target } => line(
            output,
            &prefix,
            &format!(
                "transport({}, {});",
                source_click_proposition(source),
                source_click_proposition(target)
            ),
        ),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "transport({}, {}) using {{",
                    source_click_proposition(source),
                    source_click_proposition(target)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::InstantiateUsing {
            quantified,
            argument,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "instantiate({}, {}) using {{",
                    source_click_proposition(quantified),
                    describe_contract_expression(argument)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::FrameUsing { region, premises } => {
            line(
                output,
                &prefix,
                &format!(
                    "frame({}) using {{",
                    region
                        .as_ref()
                        .map(describe_code_region_ref)
                        .unwrap_or_default()
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::SmartStep => line(output, &prefix, "step();"),
        ProofTactic::SmartExecute
        | ProofTactic::SmartExecuteAllPaths
        | ProofTactic::ExecuteUntil(_)
        | ProofTactic::SmartFrame(_)
        | ProofTactic::Simp => unreachable!("certificate validation rejects this tactic"),
    }
}

fn write_structural_effect(output: &mut String, item: &StructuralItem, indent: usize) {
    let prefix = "    ".repeat(indent);
    let effect = item.effect().expect("effect structural item");
    match effect {
        Effect::Immutable => output.push_str(&format!("{prefix}immutable")),
        Effect::Mutable(segments) => {
            output.push_str(&format!("{prefix}mutable "));
            output.push_str(
                &segments
                    .iter()
                    .map(describe_contract_segment)
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        }
    }
    output.push(' ');
    write_proof(output, item.proof(), indent);
    output.push('\n');
}

fn write_proof(output: &mut String, proof: &Proof, indent: usize) {
    let Proof::Script(tactics) = proof else {
        unreachable!("certificate validation requires an explicit proof script")
    };
    output.push_str("by {\n");
    write_tactics(output, tactics, indent + 1);
    output.push_str(&"    ".repeat(indent));
    output.push('}');
}

fn write_using_premises(
    output: &mut String,
    name: &str,
    premises: &[ClickProposition],
    indent: usize,
) {
    let prefix = "    ".repeat(indent);
    line(output, &prefix, &format!("{name} using {{"));
    write_premise_list(output, premises, indent + 1);
    line(output, &prefix, "}");
}

fn write_premise_list(output: &mut String, facts: &[ClickProposition], indent: usize) {
    let prefix = "    ".repeat(indent);
    for fact in facts {
        line(
            output,
            &prefix,
            &format!("{};", source_click_proposition(fact)),
        );
    }
}

fn format_resource_call(resource: &ResourceClause) -> String {
    let ResourceClause::Declared {
        name, arguments, ..
    } = resource
    else {
        unreachable!("fold, unfold, and observe use declared resources")
    };
    format!(
        "{name}({})",
        arguments
            .iter()
            .map(describe_contract_expression)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn format_resource_target(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Quantified { quantity, resource } => format!(
            "{} of {}",
            describe_contract_expression(quantity),
            format_resource_target(resource)
        ),
        ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
            describe_contract_segment(segment)
        }
        ResourceClause::Declared { .. } => format_resource_call(resource),
    }
}

fn resource_access(resource: &ResourceClause) -> ResourceAccessMode {
    match resource {
        ResourceClause::Quantified { resource, .. } => resource_access(resource),
        ResourceClause::Read(_) => ResourceAccessMode::View,
        ResourceClause::Write(_) => ResourceAccessMode::Own,
        ResourceClause::Declared { access, .. } => *access,
    }
}

fn format_theorem_application(application: &TheoremApplication) -> String {
    format!(
        "{}({})",
        application.name,
        application
            .arguments
            .iter()
            .map(describe_contract_expression)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn format_fact_source(source: &ProofFactSource) -> String {
    match source {
        ProofFactSource::Requirement(index) => format!("requirement {index}"),
        ProofFactSource::RequirementLabel(label) => format!("requirement {label}"),
    }
}

fn line(output: &mut String, prefix: &str, text: &str) {
    output.push_str(prefix);
    output.push_str(text);
    output.push('\n');
}
