use super::diagnostics::{
    describe_contract_expression, describe_contract_segment, describe_snapshot_selector,
};
use super::*;

pub(in crate::surface) fn source_click_proposition(proposition: &ClickProposition) -> String {
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
            ClickProposition::At {
                selector,
                proposition,
            } => (
                5,
                format!(
                    "at({}, {})",
                    describe_snapshot_selector(selector),
                    at_precedence(proposition, 0)
                ),
            ),
            ClickProposition::ForAll {
                click_type: c_type,
                name,
                body,
                ..
            } => (
                5,
                format!(
                    "forall ({name}: {}) {{ {} }}",
                    validation::describe_click_type(c_type),
                    at_precedence(body, 0)
                ),
            ),
            ClickProposition::Exists {
                click_type: c_type,
                name,
                body,
                ..
            } => (
                5,
                format!(
                    "exists ({name}: {}) {{ {} }}",
                    validation::describe_click_type(c_type),
                    at_precedence(body, 0)
                ),
            ),
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
                ..
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
                ..
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
    let certificate = ProofCertificate::from_proof_tactics(tactics)?;
    Ok(format_proof_certificate(&certificate))
}

pub(super) fn format_partial_tactic_sequence(tactics: &[ProofTactic]) -> String {
    let mut output = String::new();
    write_tactics(&mut output, tactics, 0);
    output.pop();
    output
}

pub fn format_proof_certificate(certificate: &ProofCertificate) -> String {
    let mut output = String::from("by {\n");
    write_tactics(&mut output, &certificate.to_proof_tactics(), 1);
    output.push('}');
    output
}

/// A whole proof block holding `tactics`, as [`format_proof_certificate`]
/// writes a certificate's.
pub(in crate::surface) fn format_proof_block(tactics: &[ProofTactic]) -> String {
    let mut output = String::from("by {\n");
    write_tactics(&mut output, tactics, 1);
    output.push('}');
    output
}

/// The assertions of a join's `ensuring` block, one per line.
fn write_join_interface(output: &mut String, assertions: &[ProofAssertion], indent: usize) {
    let prefix = "    ".repeat(indent);
    for assertion in assertions {
        let text = match assertion {
            ProofAssertion::Fact(fact) => format!("fact {};", source_click_proposition(fact)),
            ProofAssertion::Resource(resource) => format!(
                "{} {};",
                match resource_access(resource) {
                    ResourceAccessMode::Own => "owns",
                    ResourceAccessMode::View => "views",
                },
                format_resource_target(resource)
            ),
        };
        line(output, &prefix, &text);
    }
}

fn write_tactics(output: &mut String, tactics: &[ProofTactic], indent: usize) {
    for tactic in tactics {
        write_tactic(output, tactic, indent);
    }
}

fn write_tactic(output: &mut String, tactic: &ProofTactic, indent: usize) {
    let prefix = "    ".repeat(indent);
    match tactic {
        // A synthetic tactic was never written; it prints as what it wraps.
        ProofTactic::Synthetic(inner) => write_tactic(output, inner, indent),
        ProofTactic::Mark(name) => line(output, &prefix, &format!("mark {name};")),
        ProofTactic::Sorry => line(output, &prefix, "sorry();"),
        ProofTactic::Step => line(output, &prefix, "step();"),
        ProofTactic::StepContract(name) => line(output, &prefix, &format!("step({name});")),
        ProofTactic::StepBind(name) => line(output, &prefix, &format!("let {name} = step();")),
        ProofTactic::StepCall(transport) => line(output, &prefix, &format!("{transport};")),
        ProofTactic::UserTactic(application) => line(
            output,
            &prefix,
            &format!("{};", application.tactic_spelling()),
        ),
        ProofTactic::UnfoldPredicate(name) => {
            line(output, &prefix, &format!("unfold({name});"));
        }
        ProofTactic::UnfoldFunction(application) => line(
            output,
            &prefix,
            &format!(
                "unfold({});",
                format_click_function_application(application)
            ),
        ),
        ProofTactic::PeelFunction {
            application,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "peel({}) using {{",
                    format_click_function_application(application)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::UnfoldResource(resource @ ResourceClause::Named { binding, .. })
            if binding.child_bindings.is_some() =>
        {
            let children = binding
                .child_bindings
                .as_ref()
                .unwrap()
                .iter()
                .map(|(slot, name, _)| format!("{slot}: {name}"))
                .collect::<Vec<_>>()
                .join(", ");
            line(
                output,
                &prefix,
                &format!(
                    "let {{ {children} }} = unfold({});",
                    format_resource_call(resource)
                ),
            );
        }
        ProofTactic::UnfoldResource(resource) => line(
            output,
            &prefix,
            &format!(
                "unfold({});",
                if matches!(resource, ResourceClause::Named { .. }) {
                    format_resource_call(resource)
                } else {
                    format_resource_target(resource)
                }
            ),
        ),
        ProofTactic::FoldResource(ResourceClause::Named { binding, resource })
            if binding.fold_fields.is_some() =>
        {
            // Hidden record fields are reconstructed from the child map by
            // the parser. Their dotted internal names are not field labels.
            let fields = binding.fold_fields.as_ref().unwrap();
            let only_hidden =
                !fields.is_empty() && fields.iter().all(|(name, _)| name.contains('.'));
            let children = binding
                .child_bindings
                .as_ref()
                .map(|children| {
                    children
                        .iter()
                        .map(|(slot, name, _)| format!("{slot}: {name}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            let inputs = if only_hidden {
                format!("{{ {children} }}")
            } else {
                let visible = fields
                    .iter()
                    .filter(|(name, _)| !name.contains('.'))
                    .map(|(name, value)| format!("{name}: {}", describe_contract_expression(value)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "{{ {visible} }}{}",
                    if children.is_empty() {
                        String::new()
                    } else {
                        format!(", {{ {children} }}")
                    }
                )
            };
            let result = if binding.name.starts_with('#') {
                String::new()
            } else {
                format!("let {} = ", binding.name)
            };
            line(
                output,
                &prefix,
                &format!(
                    "{result}fold({}, {inputs});",
                    format_resource_target(resource)
                ),
            );
        }
        ProofTactic::FoldResource(resource) => line(
            output,
            &prefix,
            &format!(
                "fold({});",
                if matches!(resource, ResourceClause::Named { .. }) {
                    format_resource_call(resource)
                } else {
                    format_resource_target(resource)
                }
            ),
        ),
        ProofTactic::ConstructResource(resource) => line(
            output,
            &prefix,
            &format!("construct({});", format_resource_target(resource)),
        ),
        ProofTactic::Induct {
            parameter,
            hypothesis,
        } => line(
            output,
            &prefix,
            &format!("induct({parameter}) as {hypothesis};"),
        ),
        ProofTactic::Match(proof_match) => {
            let scrutinee = describe_contract_expression(&proof_match.scrutinee);
            if let Some(assertions) = &proof_match.ensuring {
                line(output, &prefix, &format!("match {scrutinee} ensuring {{"));
                write_join_interface(output, assertions, indent + 1);
                line(output, &prefix, "} {");
            } else {
                line(output, &prefix, &format!("match {scrutinee} {{"));
            }
            for arm in &proof_match.arms {
                let arguments = if arm.bindings.is_empty() {
                    String::new()
                } else {
                    format!("({})", arm.bindings.join(", "))
                };
                line(
                    output,
                    &format!("{prefix}    "),
                    &format!("{}::{}{arguments} => {{", arm.type_name, arm.variant),
                );
                for tactic in &arm.tactics {
                    write_tactic(output, tactic, indent + 2);
                }
                line(output, &format!("{prefix}    "), "}");
            }
            line(output, &prefix, "}");
        }
        ProofTactic::StructuralInduct {
            parameter,
            hypothesis,
            arms,
        } => {
            line(
                output,
                &prefix,
                &format!("induct({parameter}) as {hypothesis} {{"),
            );
            for arm in arms {
                let pattern = if arm.bindings.is_empty() {
                    format!("{}::{}", arm.type_name, arm.variant)
                } else {
                    format!(
                        "{}::{}({})",
                        arm.type_name,
                        arm.variant,
                        arm.bindings.join(", ")
                    )
                };
                line(
                    output,
                    &format!("{prefix}    "),
                    &format!("{pattern} => {{"),
                );
                for tactic in &arm.tactics {
                    write_tactic(output, tactic, indent + 2);
                }
                line(output, &format!("{prefix}    "), "}");
            }
            line(output, &prefix, "}");
        }
        ProofTactic::ApplyInduction {
            hypothesis,
            arguments,
        } => line(
            output,
            &prefix,
            &format!(
                "apply({hypothesis}({}));",
                describe_induction_arguments(arguments)
            ),
        ),
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            arguments,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "apply({hypothesis}({})) using {{",
                    describe_induction_arguments(arguments)
                ),
            );
            for premise in premises {
                line(
                    output,
                    &format!("{prefix}    "),
                    &format!("{};", source_click_proposition(premise)),
                );
            }
            line(output, &prefix, "}");
        }
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
            if let Some(assertions) = &proof_if.ensuring {
                output.push_str(" ensuring {\n");
                write_join_interface(output, assertions, indent + 1);
                line(output, &prefix, "} then {");
            } else {
                output.push_str(" {\n");
            }
            write_tactics(output, &proof_if.then_tactics, indent + 1);
            line(output, &prefix, "} else {");
            write_tactics(output, &proof_if.else_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Both(both) => {
            line(output, &prefix, "both {");
            write_tactics(output, &both.left_tactics, indent + 1);
            line(output, &prefix, "} and {");
            write_tactics(output, &both.right_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Cases(proof_cases) => {
            line(output, &prefix, "cases {");
            let arm_prefix = "    ".repeat(indent + 1);
            for arm in proof_cases.arms() {
                line(
                    output,
                    &arm_prefix,
                    &format!("{} => {{", source_click_proposition(arm.assumption())),
                );
                write_tactics(output, arm.tactics(), indent + 2);
                line(output, &arm_prefix, "}");
            }
            line(output, &prefix, "}");
        }
        ProofTactic::Branch(proof_branch) => {
            if let Some(assertions) = &proof_branch.ensuring {
                line(output, &prefix, "branch ensuring {");
                write_join_interface(output, assertions, indent + 1);
                line(output, &prefix, "} then {");
            } else {
                line(output, &prefix, "branch then {");
            }
            write_tactics(output, &proof_branch.then_tactics, indent + 1);
            line(output, &prefix, "} else {");
            write_tactics(output, &proof_branch.else_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::CallOutcomes(outcomes) => {
            let arm_prefix = "    ".repeat(indent + 1);
            line(output, &prefix, "outcomes {");
            line(output, &arm_prefix, "returned => {");
            write_tactics(output, &outcomes.returned_tactics, indent + 2);
            line(output, &arm_prefix, "}");
            line(output, &arm_prefix, "threw => {");
            write_tactics(output, &outcomes.threw_tactics, indent + 2);
            line(output, &arm_prefix, "}");
            line(output, &prefix, "}");
        }
        ProofTactic::Loop(loop_clause) => {
            line(
                output,
                &prefix,
                &format!(
                    "loop{}{} {{",
                    loop_clause
                        .label()
                        .map(|label| format!(" as {label}"))
                        .unwrap_or_default(),
                    if loop_clause.diverges() {
                        " diverges"
                    } else {
                        ""
                    }
                ),
            );
            let body_prefix = "    ".repeat(indent + 1);
            if let Some(decreases) = loop_clause.decreases() {
                let components = decreases
                    .components()
                    .iter()
                    .map(describe_contract_expression)
                    .collect::<Vec<_>>();
                let rendered = if components.len() == 1 {
                    components[0].clone()
                } else {
                    format!("({})", components.join(", "))
                };
                line(output, &body_prefix, &format!("decreases {rendered};"));
            }
            for resource in loop_clause.resources() {
                if matches!(resource, ResourceClause::Conditional { .. }) {
                    line(output, &body_prefix, &format_resource_target(resource));
                    continue;
                }
                let keyword = match resource_access(resource) {
                    ResourceAccessMode::Own => "owns",
                    ResourceAccessMode::View => "views",
                };
                line(
                    output,
                    &body_prefix,
                    &format!("{keyword} {};", format_resource_target(resource)),
                );
            }
            for item in loop_clause.items() {
                output.push_str(&body_prefix);
                output.push_str("invariant");
                output.push(' ');
                output.push_str(&source_click_proposition(item.proposition()));
                output.push_str(";\n");
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
            &format!("observe({});", format_resource_target(resource)),
        ),
        ProofTactic::Iterated(tactic) => line(
            output,
            &prefix,
            &format!("{};", describe_iterated_tactic(tactic)),
        ),
        ProofTactic::Witness(witness) => line(
            output,
            &prefix,
            &format!(
                "witness {{ {} }}",
                witness
                    .bindings()
                    .map(|(name, value)| format!("{name}: {}", describe_contract_expression(value)))
                    .collect::<Vec<_>>()
                    .join(", ")
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
        ProofTactic::LetSatisfy(binding) => {
            let bindings = binding
                .bindings
                .iter()
                .map(|(name, click_type)| {
                    format!("{name}: {}", validation::describe_click_type(click_type))
                })
                .collect::<Vec<_>>()
                .join(", ");
            let (snapshot, mut body) = match &binding.proposition {
                ClickProposition::At {
                    selector,
                    proposition,
                } => (Some(selector), proposition.as_ref()),
                proposition => (None, proposition),
            };
            for _ in &binding.bindings {
                let ClickProposition::Exists { body: inner, .. } = body else {
                    unreachable!("let-satisfy source contains its declared binders")
                };
                body = inner;
            }
            let body = if let Some(selector) = snapshot {
                format!(
                    "at({}, {})",
                    describe_snapshot_selector(selector),
                    source_click_proposition(body)
                )
            } else {
                source_click_proposition(body)
            };
            line(
                output,
                &prefix,
                &format!("obtain ({bindings}) {{ {body} }}"),
            );
        }
        ProofTactic::Assumption => line(output, &prefix, "assumption();"),
        ProofTactic::Extract(proposition) => line(
            output,
            &prefix,
            &format!("extract({});", source_click_proposition(proposition)),
        ),
        ProofTactic::Normalize => line(output, &prefix, "normalize();"),
        ProofTactic::NormalizeUsing(premises) => {
            write_using_premises(output, "normalize()", premises, indent)
        }
        ProofTactic::ArithmeticUsing(premises) if premises.is_empty() => {
            line(output, &prefix, "arithmetic();")
        }
        ProofTactic::ArithmeticUsing(premises) => {
            write_using_premises(output, "arithmetic()", premises, indent)
        }
        ProofTactic::Intro => line(output, &prefix, "intro();"),
        ProofTactic::IntroAs(name) => line(output, &prefix, &format!("intro() as {name};")),
        ProofTactic::Enumerate => line(output, &prefix, "enumerate();"),
        ProofTactic::Contradiction(fact) => line(
            output,
            &prefix,
            &format!("contradiction({});", source_click_proposition(fact)),
        ),
        ProofTactic::SimpUsing(simp) => {
            write_using_premises(output, "simp()", &simp.premises, indent)
        }
        ProofTactic::ArithmeticCertificate(certificate) => {
            write_arithmetic_certificate(output, certificate, indent)
        }
        ProofTactic::CloseInvariants => line(output, &prefix, "close_invariants();"),
        ProofTactic::CloseInvariantsBy(body) => {
            line(output, &prefix, "close_invariants by {");
            write_tactics(output, body, indent + 1);
            line(output, &prefix, "}");
        }
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
            let instantiate = format!(
                "instantiate({}, {})",
                source_click_proposition(quantified),
                describe_contract_expression(argument)
            );
            match premises {
                Some(premises) => {
                    line(output, &prefix, &format!("{instantiate} using {{"));
                    write_premise_list(output, premises, indent + 1);
                    line(output, &prefix, "}");
                }
                None => line(output, &prefix, &format!("{instantiate};")),
            }
        }
        ProofTactic::SmartExecute
        | ProofTactic::ExecuteUntil(_)
        | ProofTactic::Simp
        | ProofTactic::AutoClose => {
            unreachable!("certificate validation rejects this tactic")
        }
    }
}

fn write_arithmetic_certificate(
    output: &mut String,
    certificate: &ArithmeticCertificate,
    indent: usize,
) {
    if let ArithmeticCertificateFamily::SignedInt32(certificate) = &certificate.family {
        write_signed_int32_certificate(output, certificate, indent);
        return;
    }
    if let ArithmeticCertificateFamily::Special(certificate) = &certificate.family {
        write_special_arithmetic_certificate(output, certificate, indent);
        return;
    }
    let ArithmeticCertificateFamily::Integer(certificate) = &certificate.family else {
        unreachable!("signed_int32 certificates are printed above")
    };
    let prefix = "    ".repeat(indent);
    line(output, &prefix, "arithmetic_certificate {");
    let body = "    ".repeat(indent + 1);
    for node in &certificate.nodes {
        let text = match node {
            IntegerCertificateNode::Premise {
                index,
                proposition,
                result,
            } => format!(
                "premise {index}: {} => {};",
                source_click_proposition(proposition),
                source_click_proposition(result)
            ),
            IntegerCertificateNode::Scale {
                source,
                coefficient,
                result,
            } => format!(
                "scale {source} by {} => {};",
                describe_contract_expression(coefficient),
                source_click_proposition(result)
            ),
            IntegerCertificateNode::Add {
                left,
                right,
                result,
            } => format!(
                "add {left}, {right} => {};",
                source_click_proposition(result)
            ),
            IntegerCertificateNode::EqualityToLessEqual {
                source,
                reverse,
                result,
            } => format!(
                "less_equal_from_equal {source}{} => {};",
                if *reverse { " reverse" } else { "" },
                source_click_proposition(result)
            ),
            IntegerCertificateNode::EqualityFromBounds {
                lower,
                upper,
                result,
            } => format!(
                "equal_from_bounds {lower}, {upper} => {};",
                source_click_proposition(result)
            ),
            IntegerCertificateNode::Trivial { result } => {
                format!("trivial => {};", source_click_proposition(result))
            }
            IntegerCertificateNode::NegatedGoal { result } => {
                format!("negated_goal => {};", source_click_proposition(result))
            }
            IntegerCertificateNode::Divide {
                source,
                divisor,
                result,
            } => format!(
                "divide {source} by {} => {};",
                describe_contract_expression(divisor),
                source_click_proposition(result)
            ),
        };
        line(output, &body, &text);
    }
    line(
        output,
        &body,
        &format!("conclusion {};", certificate.conclusion),
    );
    line(output, &prefix, "}");
}

fn write_special_arithmetic_certificate(
    output: &mut String,
    certificate: &SpecialArithmeticCertificate,
    indent: usize,
) {
    let prefix = "    ".repeat(indent);
    line(output, &prefix, "arithmetic_certificate rules {");
    let body = "    ".repeat(indent + 1);
    for (index, premise) in certificate.premises.iter().enumerate() {
        line(
            output,
            &body,
            &format!(
                "premise {index}: {} => {};",
                source_click_proposition(premise),
                source_click_proposition(premise)
            ),
        );
    }
    for node in &certificate.nodes {
        let text = match node {
            SpecialArithmeticNode::IntegerCastIdentity { bounds, result } => format!(
                "integer_cast_identity bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerProductBounds { bounds, result } => format!(
                "integer_product_bounds bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerDivisionBounds { bounds, result } => format!(
                "integer_division_bounds bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerMultiplyOrder { bounds, result } => format!(
                "integer_multiply_order bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerQuotientBound { bounds, result } => format!(
                "integer_quotient_bound bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerBoundExclusion { bounds, result } => format!(
                "integer_bound_exclusion bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerRelationTransport { bounds, result } => format!(
                "integer_relation_transport bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerPolynomialIdentity { bounds, result } => format!(
                "integer_polynomial_identity bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::IntegerQuotientShift { bounds, result } => format!(
                "integer_quotient_shift bounds [{}] => {};",
                bounds
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::PointerTranslation {
                relation,
                bounds,
                result,
            } => format!(
                "pointer_translation relation {relation} bounds [{}] => {};",
                bounds
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::PointerAlignment { premise, result } => format!(
                "pointer_alignment premise {} => {};",
                premise.map_or_else(|| "intrinsic".to_owned(), |i| i.to_string()),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::PointerWordEquality {
                relation,
                alignments,
                result,
            } => format!(
                "pointer_word_equality relation {relation} alignments [{}] => {};",
                alignments
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::PointerWordFromAlignment { alignments, result } => format!(
                "pointer_word_from_alignment alignments [{}] => {};",
                alignments
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::FloatReflexive { finite, result } => format!(
                "float_reflexive finite {finite} => {};",
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::UnsignedSumBound { bounds, result } => format!(
                "unsigned_sum_bound bounds [{}] => {};",
                bounds
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
            SpecialArithmeticNode::SignedDefined {
                width,
                bounds,
                result,
            } => format!(
                "{}_defined bounds [{}] => {};",
                width.name(),
                bounds
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                source_click_proposition(result)
            ),
        };
        line(output, &body, &text);
    }
    line(
        output,
        &body,
        &format!("conclusion {};", certificate.conclusion),
    );
    line(output, &prefix, "}");
}

fn write_signed_int32_certificate(
    output: &mut String,
    certificate: &SignedInt32Certificate,
    indent: usize,
) {
    let prefix = "    ".repeat(indent);
    line(output, &prefix, "arithmetic_certificate signed_int32 {");
    let body = "    ".repeat(indent + 1);
    for node in &certificate.nodes {
        let text = match node {
            SignedArithmeticStep::Premise {
                index,
                proposition,
                result,
            } => format!(
                "premise {index}: {} => {};",
                source_click_proposition(proposition),
                source_click_proposition(result)
            ),
            SignedArithmeticStep::Scale {
                source,
                coefficient,
                result,
            } => format!(
                "scale {source} by {} => {};",
                describe_contract_expression(coefficient),
                source_click_proposition(result)
            ),
            SignedArithmeticStep::Add {
                left,
                right,
                result,
            } => format!(
                "add {left}, {right} => {};",
                source_click_proposition(result)
            ),
            SignedArithmeticStep::EqualityToLessEqual {
                source,
                reverse,
                result,
            } => format!(
                "less_equal_from_equal {source}{} => {};",
                if *reverse { " reverse" } else { "" },
                source_click_proposition(result)
            ),
            SignedArithmeticStep::EqualityFromBounds {
                lower,
                upper,
                result,
            } => format!(
                "equal_from_bounds {lower}, {upper} => {};",
                source_click_proposition(result)
            ),
            SignedArithmeticStep::StrictFromDisequal {
                bound,
                disequal,
                result,
            } => format!(
                "less_than_from_not_equal {bound}, {disequal} => {};",
                source_click_proposition(result)
            ),
            SignedArithmeticStep::Trivial { result } => {
                format!("trivial => {};", source_click_proposition(result))
            }
            SignedArithmeticStep::Int32Range { result } => {
                format!("int32_range => {};", source_click_proposition(result))
            }
            SignedArithmeticStep::IntervalFromAffine {
                source,
                term,
                lower,
                upper,
            } => format!(
                "interval_from_affine {source} ({}) ({lower}) ({upper});",
                describe_contract_expression(term)
            ),
            SignedArithmeticStep::IntervalFromAffineDirect {
                source,
                term,
                lower,
                upper,
            } => format!(
                "interval_from_affine_direct {source} ({}) ({lower}) ({upper});",
                describe_contract_expression(term)
            ),
            SignedArithmeticStep::IntervalAtom { term, lower, upper } => format!(
                "interval_atom ({}) ({lower}) ({upper});",
                describe_contract_expression(term)
            ),
            SignedArithmeticStep::DefinedPremise { index, term } => {
                format!("defined {index} ({});", describe_contract_expression(term))
            }
            SignedArithmeticStep::IntervalIntersect {
                left,
                right,
                result,
            } => format!(
                "interval_intersect {left}, {right} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalAdd {
                left,
                right,
                defined,
                result,
            } => format!(
                "interval_add {left}, {right} {defined} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalAddBounded {
                left,
                right,
                result,
            } => format!(
                "interval_add_bounded {left}, {right} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalSubtract {
                left,
                right,
                defined,
                result,
            } => format!(
                "interval_subtract {left}, {right} {defined} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalMultiply {
                left,
                right,
                defined,
                result,
            } => format!(
                "interval_multiply {left}, {right} {defined} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalRemainderAdd {
                operand,
                remainder,
                addend,
                divisor,
                result,
            } => format!(
                "interval_remainder_add {operand}, {remainder} ({addend}) ({divisor}) ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalRemainder {
                operand,
                divisor,
                defined,
                result,
            } => format!(
                "interval_remainder {operand} {divisor} {defined} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalShiftLeft {
                operand,
                shift,
                defined,
                result,
            } => format!(
                "interval_shift_left {operand} {shift} {defined} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalArithmeticShiftRight {
                operand,
                shift,
                result,
            } => format!(
                "interval_arithmetic_shift_right {operand} {shift} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalBitwiseAnd {
                operand,
                mask,
                result,
            } => format!(
                "interval_bitwise_and {operand} {mask} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalSignBitFlip { operand, result } => format!(
                "interval_sign_bit_flip {operand} ({}) ({});",
                result.lower, result.upper
            ),
            SignedArithmeticStep::IntervalNarrowedCast {
                operand,
                source,
                destination,
                result,
            } => format!(
                "interval_narrowed_cast {operand} {} {} ({}) ({});",
                machine_integer_type_name(*source),
                machine_integer_type_name(*destination),
                result.lower,
                result.upper
            ),
            SignedArithmeticStep::IntervalCompare {
                left,
                right,
                comparison,
                result,
            } => format!(
                "interval_compare {left}, {right} {} => {};",
                signed_comparison_name(*comparison),
                source_click_proposition(result)
            ),
            SignedArithmeticStep::AffinePremise {
                source,
                left_evidence,
                right_evidence,
                result,
            } => format!(
                "affine_premise {source} {left_evidence} {right_evidence} => {};",
                source_click_proposition(result)
            ),
            SignedArithmeticStep::AffineConclusion {
                source,
                evidence,
                result,
            } => format!(
                "affine_conclusion {source} {evidence} => {};",
                source_click_proposition(result)
            ),
            SignedArithmeticStep::AffineConclusionWithEvidence {
                source,
                left_evidence,
                right_evidence,
                result,
            } => format!(
                "affine_conclusion_pair {source} {left_evidence} {right_evidence} => {};",
                source_click_proposition(result)
            ),
        };
        line(output, &body, &text);
    }
    line(
        output,
        &body,
        &format!("conclusion {};", certificate.conclusion),
    );
    line(output, &prefix, "}");
}

/// The Click spelling of an integer type in certificate text.
pub(in crate::surface) fn machine_integer_type_name(
    ty: crate::kernel::MachineIntegerType,
) -> &'static str {
    use crate::kernel::MachineIntegerType as Ty;
    match ty {
        Ty::Int8 => "int8",
        Ty::UInt8 => "uint8",
        Ty::Int16 => "int16",
        Ty::UInt16 => "uint16",
        Ty::Int32 => "int32",
        Ty::UInt32 => "uint32",
        Ty::Int64 => "int64",
        Ty::UInt64 => "uint64",
        Ty::Int128 => "int128",
        Ty::UInt128 => "uint128",
    }
}

pub(in crate::surface) fn machine_integer_type_from_name(
    name: &str,
) -> Option<crate::kernel::MachineIntegerType> {
    use crate::kernel::MachineIntegerType as Ty;
    [
        Ty::Int8,
        Ty::UInt8,
        Ty::Int16,
        Ty::UInt16,
        Ty::Int32,
        Ty::UInt32,
        Ty::Int64,
        Ty::UInt64,
        Ty::Int128,
        Ty::UInt128,
    ]
    .into_iter()
    .find(|ty| machine_integer_type_name(*ty) == name)
}

fn signed_comparison_name(comparison: SignedInt32Comparison) -> &'static str {
    match comparison {
        SignedInt32Comparison::LessThan => "lt",
        SignedInt32Comparison::LessEqual => "le",
        SignedInt32Comparison::Equal => "eq",
        SignedInt32Comparison::Disequal => "ne",
    }
}

fn write_proof(output: &mut String, proof: &SourceProof, indent: usize) {
    let SourceProof::Script(tactics) = proof else {
        unreachable!("certificate validation requires an explicit proof script")
    };
    output.push_str("by {\n");
    if tactics.is_empty() {
        // A `by` block must hold a tactic. A generated proof with no step,
        // such as the `initialize` phase of a loop with no invariant, keeps
        // `assumption();`, the step a phase with nothing to prove is
        // checked by.
        line(output, &"    ".repeat(indent + 1), "assumption();");
    }
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

pub(in crate::surface) fn format_resource_call(resource: &ResourceClause) -> String {
    if let ResourceClause::Named { binding, resource } = resource {
        return if binding.name.starts_with('#') {
            format_resource_call(resource)
        } else {
            binding.name.clone()
        };
    }
    let ResourceClause::Declared {
        name,
        arguments,
        type_schema: _,
        resource_type_arguments,
        resource_arguments,
        ..
    } = resource
    else {
        unreachable!("fold, unfold, and observe use declared resources")
    };
    format!(
        "{name}({})",
        arguments
            .iter()
            .map(describe_contract_expression)
            .chain(
                resource_arguments
                    .iter()
                    .map(|reference| reference.name.clone())
            )
            .chain(resource_type_arguments.iter().map(format_resource_call))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// One iterated-ownership tactic as it is written: `take(data[j..j + 1])`.
pub(in crate::surface) fn describe_iterated_tactic(tactic: &IteratedTactic) -> String {
    format!(
        "{}({})",
        tactic.name(),
        match tactic {
            IteratedTactic::Take(segment) | IteratedTactic::Give(segment) => {
                describe_contract_segment(segment)
            }
            IteratedTactic::Gather(resource) | IteratedTactic::Scatter(resource) => {
                format_resource_target(resource)
            }
        }
    )
}

fn format_resource_target(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => format!(
            "if {} {{ {} {}; }}",
            source_click_proposition(condition),
            if resource_access(resource) == ResourceAccessMode::Own {
                "owns"
            } else {
                "views"
            },
            format_resource_target(resource)
        ),
        ResourceClause::Named { binding, resource } => {
            if binding.name.starts_with('#') {
                format_resource_target(resource)
            } else {
                format!("{}: {}", binding.name, format_resource_target(resource))
            }
        }
        ResourceClause::Quantified { quantity, resource } => format!(
            "{} of {}",
            describe_contract_expression(quantity),
            format_resource_target(resource)
        ),
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            describe_contract_segment(segment)
        }
        ResourceClause::MemoryAggregate { segments, .. } => format!(
            "aggregate {{{}}}",
            segments
                .iter()
                .map(describe_contract_segment)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ResourceClause::Declared { .. } => format_resource_call(resource),
        ResourceClause::Iterated(clause) => {
            crate::surface::lowering::describe_iterated_clause(clause)
        }
    }
}

fn resource_access(resource: &ResourceClause) -> ResourceAccessMode {
    match resource {
        ResourceClause::Conditional { resource, .. } => resource_access(resource),
        ResourceClause::Named { .. } => ResourceAccessMode::Own,
        ResourceClause::Quantified { resource, .. } => resource_access(resource),
        ResourceClause::ViewMemory(_) => ResourceAccessMode::View,
        ResourceClause::OwnMemory(_) => ResourceAccessMode::Own,
        ResourceClause::MemoryAggregate { access, .. } => *access,
        ResourceClause::Declared { access, .. } => *access,
        ResourceClause::Iterated(_) => ResourceAccessMode::Own,
    }
}

/// An induction hypothesis is applied at the theorem's parameter list, so its
/// arguments print exactly like an ordinary theorem application's.
fn describe_induction_arguments(arguments: &[ContractExpression]) -> String {
    arguments
        .iter()
        .map(describe_contract_expression)
        .collect::<Vec<_>>()
        .join(", ")
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

fn format_click_function_application(application: &ClickFunctionApplication) -> String {
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
        ProofFactSource::Invariant(index) => format!("invariant {index}"),
    }
}

fn line(output: &mut String, prefix: &str, text: &str) {
    output.push_str(prefix);
    output.push_str(text);
    output.push('\n');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn marked_conjunction_uses_parseable_click_connectives() {
        let equality = |name: &str| ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable(name.to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable(name.to_string())),
        };
        let proposition = ClickProposition::At {
            selector: SnapshotSelector::Mark("checkpoint".to_string()),
            proposition: Box::new(ClickProposition::And(
                Box::new(equality("left")),
                Box::new(equality("right")),
            )),
        };

        assert_eq!(
            source_click_proposition(&proposition),
            "at(checkpoint, left == left and right == right)"
        );
    }
}
