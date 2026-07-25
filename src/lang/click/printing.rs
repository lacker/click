use super::diagnostics::{
    describe_click_proposition, describe_code_region_ref, describe_contract_expression,
    describe_contract_segment, describe_program_point_ref,
};
use super::*;

pub fn format_proof_tactics(tactics: &[ProofTactic]) -> Result<String, CertificateError> {
    let certificate = TacticCertificate::from_proof_tactics(tactics)?;
    Ok(format_tactic_certificate(&certificate))
}

pub(super) fn format_partial_tactic_sequence(tactics: &[ProofTactic]) -> String {
    let mut output = String::new();
    write_tactics(&mut output, tactics, 0);
    output.pop();
    output
}

pub fn format_tactic_certificate(certificate: &TacticCertificate) -> String {
    let mut output = String::from("by {\n");
    write_tactics(&mut output, certificate.tactics(), 1);
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
        ProofTactic::Step => line(output, &prefix, "step();"),
        ProofTactic::StepUsing(premises) => {
            line(output, &prefix, "step using {");
            write_fact_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::ApplyLoopSummary(region) => line(
            output,
            &prefix,
            &format!("apply_loop_summary({});", describe_code_region_ref(region)),
        ),
        ProofTactic::ApplyLoopSummaryUsing { region, premises } => {
            line(
                output,
                &prefix,
                &format!(
                    "apply_loop_summary({}) using {{",
                    describe_code_region_ref(region)
                ),
            );
            write_fact_list(output, premises, indent + 1);
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
            write_fact_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Have(have) => {
            output.push_str(&prefix);
            output.push_str("have ");
            output.push_str(&describe_click_proposition(&have.proposition));
            output.push_str(" ");
            write_proof(output, &have.proof, indent);
            output.push('\n');
        }
        ProofTactic::If(proof_if) => {
            output.push_str(&prefix);
            output.push_str("if ");
            output.push_str(&describe_click_proposition(&proof_if.condition));
            output.push_str(" {\n");
            write_tactics(output, &proof_if.then_tactics, indent + 1);
            line(output, &prefix, "} else {");
            write_tactics(output, &proof_if.else_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Advance(advance) => {
            line(
                output,
                &prefix,
                &format!(
                    "advance({}) ensuring {{",
                    describe_program_point_ref(&advance.target)
                ),
            );
            for assertion in &advance.assertions {
                let text = match assertion {
                    ProofAssertion::Fact(fact) => {
                        format!("fact {};", describe_click_proposition(fact))
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
                line(output, &"    ".repeat(indent + 1), &text);
            }
            line(output, &prefix, "} by {");
            write_tactics(output, &advance.tactics, indent + 1);
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
        ProofTactic::Normalize => line(output, &prefix, "normalize();"),
        ProofTactic::Intro => line(output, &prefix, "intro();"),
        ProofTactic::Conjunction => line(output, &prefix, "conjunction();"),
        ProofTactic::Left => line(output, &prefix, "left();"),
        ProofTactic::Right => line(output, &prefix, "right();"),
        ProofTactic::DoubleNegation => line(output, &prefix, "double_negation();"),
        ProofTactic::Vacuous => line(output, &prefix, "vacuous();"),
        ProofTactic::Contradiction(fact) => line(
            output,
            &prefix,
            &format!("contradiction({});", describe_click_proposition(fact)),
        ),
        ProofTactic::Derive(derive) => write_derivation(output, "derive", derive, indent),
        ProofTactic::Calculate(derive) => write_derivation(output, "calculate", derive, indent),
        ProofTactic::Rewrite(equality) => line(
            output,
            &prefix,
            &format!("rewrite({});", describe_click_proposition(equality)),
        ),
        ProofTactic::Transport { source, target } => line(
            output,
            &prefix,
            &format!(
                "transport({}, {});",
                describe_click_proposition(source),
                describe_click_proposition(target)
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
                    describe_click_proposition(source),
                    describe_click_proposition(target)
                ),
            );
            write_fact_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Frame(region) => line(
            output,
            &prefix,
            &format!(
                "frame({});",
                region
                    .as_ref()
                    .map(describe_code_region_ref)
                    .unwrap_or_default()
            ),
        ),
        ProofTactic::ExecuteStep => line(output, &prefix, "execute_step();"),
        ProofTactic::CertifiedStatementStep(_)
        | ProofTactic::CertifiedLoopSummaryStep(_)
        | ProofTactic::CertifiedStatementReplay(_)
        | ProofTactic::ExecuteThenStep
        | ProofTactic::ExecuteElseStep
        | ProofTactic::ExecuteRest
        | ProofTactic::ExecuteUntil(_)
        | ProofTactic::BoundedExecute
        | ProofTactic::ContextualFrame
        | ProofTactic::ExactPropositionDerivation(_)
        | ProofTactic::CertifiedFactTransport { .. }
        | ProofTactic::FinishCertifiedFactTransports(_)
        | ProofTactic::CertifiedPathAssumption { .. }
        | ProofTactic::CertifiedFrame(_)
        | ProofTactic::CertifiedAlternatives(_)
        | ProofTactic::Simp => unreachable!("certificate validation rejects this tactic"),
    }
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

fn write_derivation(output: &mut String, name: &str, derive: &ProofDerive, indent: usize) {
    let prefix = "    ".repeat(indent);
    line(
        output,
        &prefix,
        &format!(
            "{name}({}) using {{",
            describe_click_proposition(&derive.proposition)
        ),
    );
    write_fact_list(output, &derive.premises, indent + 1);
    line(output, &prefix, "}");
}

fn write_fact_list(output: &mut String, facts: &[ClickProposition], indent: usize) {
    let prefix = "    ".repeat(indent);
    for fact in facts {
        line(
            output,
            &prefix,
            &format!("fact {};", describe_click_proposition(fact)),
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
        ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
            describe_contract_segment(segment)
        }
        ResourceClause::Declared { .. } => format_resource_call(resource),
    }
}

fn resource_access(resource: &ResourceClause) -> ResourceAccessMode {
    match resource {
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
