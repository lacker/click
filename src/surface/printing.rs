use super::diagnostics::{
    describe_contract_expression, describe_contract_segment, describe_snapshot_selector,
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
        ProofTactic::StepContract(name) => line(output, &prefix, &format!("step({name});")),
        ProofTactic::StepCall(transport) => line(output, &prefix, &format!("{transport};")),
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
                    "unfold({}) as {{ {children} }};",
                    format_resource_call(resource)
                ),
            );
        }
        ProofTactic::UnfoldResource(resource) => line(
            output,
            &prefix,
            &format!("unfold({});", format_resource_call(resource)),
        ),
        ProofTactic::FoldResource(ResourceClause::Named { binding, resource })
            if binding.fold_fields.is_some() =>
        {
            line(
                output,
                &prefix,
                &format!(
                    "let {} = fold({}, {{ {} }}{});",
                    binding.name,
                    format_resource_target(resource),
                    binding
                        .fold_fields
                        .as_ref()
                        .unwrap()
                        .iter()
                        .map(|(name, value)| format!(
                            "{name}: {}",
                            describe_contract_expression(value)
                        ))
                        .collect::<Vec<_>>()
                        .join(", "),
                    binding
                        .child_bindings
                        .as_ref()
                        .filter(|children| !children.is_empty())
                        .map(|children| format!(
                            ", {{ {} }}",
                            children
                                .iter()
                                .map(|(slot, name, _)| format!("{slot}: {name}"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ))
                        .unwrap_or_default(),
                ),
            )
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
            line(
                output,
                &prefix,
                &format!(
                    "match {} {{",
                    describe_contract_expression(&proof_match.scrutinee)
                ),
            );
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
            argument,
        } => line(
            output,
            &prefix,
            &format!(
                "apply({hypothesis}({}));",
                describe_contract_expression(argument)
            ),
        ),
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            argument,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "apply({hypothesis}({})) using {{",
                    describe_contract_expression(argument)
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
            output.push_str(" {\n");
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
        ProofTactic::SmartExecute
        | ProofTactic::SmartExecuteAllPaths
        | ProofTactic::ExecuteUntil(_)
        | ProofTactic::Simp => unreachable!("certificate validation rejects this tactic"),
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
                "eq_to_le {source}{} => {};",
                if *reverse { " reverse" } else { "" },
                source_click_proposition(result)
            ),
            IntegerCertificateNode::EqualityFromBounds {
                lower,
                upper,
                result,
            } => format!(
                "eq_from_bounds {lower}, {upper} => {};",
                source_click_proposition(result)
            ),
            IntegerCertificateNode::Trivial { result } => {
                format!("trivial => {};", source_click_proposition(result))
            }
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
                "eq_to_le {source}{} => {};",
                if *reverse { " reverse" } else { "" },
                source_click_proposition(result)
            ),
            SignedArithmeticStep::EqualityFromBounds {
                lower,
                upper,
                result,
            } => format!(
                "eq_from_bounds {lower}, {upper} => {};",
                source_click_proposition(result)
            ),
            SignedArithmeticStep::Trivial { result } => {
                format!("trivial => {};", source_click_proposition(result))
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
            SignedArithmeticStep::AffineConclusion {
                source,
                evidence,
                result,
            } => format!(
                "affine_conclusion {source} {evidence} => {};",
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
    if let ResourceClause::Named { binding, .. } = resource {
        return binding.name.clone();
    }
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
        ResourceClause::Named { binding, resource } => {
            format!("{}: {}", binding.name, format_resource_target(resource))
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
    }
}

fn resource_access(resource: &ResourceClause) -> ResourceAccessMode {
    match resource {
        ResourceClause::Named { .. } => ResourceAccessMode::Own,
        ResourceClause::Quantified { resource, .. } => resource_access(resource),
        ResourceClause::ViewMemory(_) => ResourceAccessMode::View,
        ResourceClause::OwnMemory(_) => ResourceAccessMode::Own,
        ResourceClause::MemoryAggregate { access, .. } => *access,
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
        ProofFactSource::RequirementLabel(label) => format!("requirement {label}"),
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
