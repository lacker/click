//! Language diagnostics and smart-search policy over kernel proof-fact reasoning.

use super::*;

pub(crate) use crate::kernel::proof::fact_reasoning::*;

pub(super) fn negate_click_proposition(proposition: &ClickProposition) -> ClickProposition {
    match proposition {
        ClickProposition::Comparison {
            operator: ComparisonOperator::In,
            ..
        } => ClickProposition::Not(Box::new(proposition.clone())),
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ClickProposition::Comparison {
            left: left.clone(),
            operator: match operator {
                ComparisonOperator::Equal => ComparisonOperator::NotEqual,
                ComparisonOperator::NotEqual => ComparisonOperator::Equal,
                ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
                ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
                ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
                ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
                ComparisonOperator::In => unreachable!("handled above"),
            },
            right: right.clone(),
        },
        ClickProposition::Not(body) => body.as_ref().clone(),
        proposition => ClickProposition::Not(Box::new(proposition.clone())),
    }
}

pub(in crate::surface) fn describe_condition_search_miss(
    proposition: &Proposition,
    available: &[Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let candidates = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .cloned()
        .collect::<Vec<_>>();
    // The goal and every premise searched are spelled with their operands,
    // through the same names, so the reader can see what was compared.
    format!(
        "condition-certificate premise search did not derive `{}` from {} ambient condition facts: {}; smart search tries individual facts and pairs and is heuristic, so split the execution into smaller steps or provide the exact premises with simple tactics",
        crate::surface::diagnostics::describe_stated_fact(proposition, parameter_binding),
        candidates.len(),
        crate::surface::diagnostics::describe_pure_facts_for_diagnostic(
            &candidates,
            parameter_binding
        ),
    )
}

/// Why a statement's premise had no checkable derivation, spelled over the
/// locals of `state`, the state the statement runs from.
pub(super) fn describe_derivation_failure(
    proposition: &Proposition,
    available: &[Proposition],
    state: &ExecutionState,
    environment: &ExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
) -> String {
    let (parameters, arguments) = crate::surface::diagnostics::local_naming_tables(state);
    if let Proposition::ConditionIs(condition, value) = proposition {
        // A condition the consulted facts decide against is refuted, not
        // underived: a narrowing bound the facts contradict, say. The
        // search's miss is then not the news, and neither smaller steps nor
        // listed premises would supply the condition.
        let consulted = available
            .iter()
            .cloned()
            .fold(PureFactContext::new(), PureFactContext::assume_proposition);
        if consulted.decide(condition) == Some(!*value) {
            return crate::surface::diagnostics::describe_refuted_condition(
                proposition,
                available,
                ParameterBinding::new(&parameters, &arguments),
            );
        }
        describe_condition_search_miss(
            proposition,
            available,
            ParameterBinding::new(&parameters, &arguments),
        )
    } else if matches!(
        proposition,
        Proposition::Predicate { name, .. }
            if crate::kernel::FunctionContract::surface_name_from_predicate(name).is_some()
    ) {
        // A named-contract prerequisite the kernel refused is where the
        // automatic formation route ends. Print the explicit theorem that
        // replaces it rather than only the refusal.
        describe_pure_fact_with_environment(
            proposition,
            ParameterBinding::new(&parameters, &arguments),
            environment,
            predicate_environment,
        )
    } else {
        // Every other shape goes through the same bounded sentence the rest
        // of the proof diagnostics use. `Debug` here dumped the kernel
        // proposition, schemas and states included.
        describe_pure_fact(proposition, ParameterBinding::new(&parameters, &arguments))
    }
}

/// The most facts a source-term prerequisite refusal lists.
const PREREQUISITE_FACT_LIMIT: usize = 6;

/// [`describe_derivation_failure`] for a prerequisite of executing
/// `statement`, stated in the source terms of the C operation that needed it
/// when it is one a proof supplies through ordinary facts: an access's
/// element bound, or a bounds check the C frontend lowered to an assertion.
/// Each names the source condition that was not shown and the consulted
/// facts about its variables, leaving out `path_facts`, the assumptions of
/// the refused path itself (on an assertion's failing path, the negation of
/// what it asserts). Every other prerequisite keeps the generic sentence.
pub(super) fn describe_statement_prerequisite_failure(
    proposition: &Proposition,
    available: &[Proposition],
    path_facts: &[Proposition],
    state: &ExecutionState,
    statement: &ProgramStatement,
    environment: &ExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
) -> String {
    // The context records a path fact in derived forms too (an unsigned
    // comparison as its signed bounds); those restate the refused path's
    // own assumption, not a consulted fact.
    let derived = path_facts
        .iter()
        .fold(crate::kernel::PureFactContext::new(), |context, fact| {
            context.assume_proposition(fact.clone())
        })
        .pure_facts();
    let consulted = available
        .iter()
        .filter(|fact| !path_facts.contains(fact) && !derived.contains(fact))
        .cloned()
        .collect::<Vec<_>>();
    let refusal = describe_access_bound_prerequisite(proposition, &consulted, state, statement)
        .or_else(|| describe_assertion_prerequisite(proposition, &consulted, state, statement))
        .unwrap_or_else(|| {
            describe_derivation_failure(
                proposition,
                available,
                state,
                environment,
                predicate_environment,
            )
        });
    format!(
        "{refusal}{}",
        crate::surface::diagnostics::describe_execution_statement_site()
    )
}

/// "the store to `items[i]` may write outside `items`: could not show
/// `0 <= i && i < 4` from the facts ...", then the C operation.
fn describe_access_bound_prerequisite(
    proposition: &Proposition,
    available: &[Proposition],
    state: &ExecutionState,
    statement: &ProgramStatement,
) -> Option<String> {
    let (access, verb, memory, pointer, byte_width) = match proposition {
        Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => ("store to", "write", memory, pointer, *byte_width),
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } => ("read of", "read", memory, base, bytes.as_const()?),
        _ => return None,
    };
    let (parameters, arguments) = crate::surface::diagnostics::local_naming_tables(state);
    let object = crate::surface::diagnostics::describe_memory_block(
        &pointer.block,
        ParameterBinding::new(&parameters, &arguments),
    )?;
    let bound = crate::kernel::memory_access_element_bound(memory, pointer, byte_width)?;
    let spell = |term: &MachineTerm| {
        let spelled = crate::surface::diagnostics::describe_bitvector_with_context(
            term,
            ParameterBinding::new(&parameters, &arguments),
        );
        match spelled
            .strip_prefix('(')
            .and_then(|inner| inner.strip_suffix(')'))
        {
            Some(inner) if balanced_parentheses(inner) => inner.to_string(),
            _ => spelled,
        }
    };
    let (index, count) = (spell(&bound.index), spell(&bound.count));
    let element = if bound.stride == byte_width {
        format!("`{object}[{index}]`")
    } else {
        format!(
            "{byte_width} bytes of element `{object}[{index}]` ({}-byte elements)",
            bound.stride
        )
    };
    // The locals the index is written over, which the consulted facts must
    // mention to bear on it.
    let names = index
        .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .filter(|word| word.starts_with(|first: char| first.is_ascii_alphabetic() || first == '_'))
        .collect::<Vec<_>>();
    // A source statement can lower to several kernel ones (a bounds check
    // before the access); name the store itself when there is one.
    let mut operation = statement;
    let mut pending = vec![statement];
    while let Some(next) = pending.pop() {
        match next {
            ProgramStatement::Seq(statements) => {
                pending.extend(statements.iter().rev().map(|statement| statement.as_ref()))
            }
            ProgramStatement::Store { .. } | ProgramStatement::TypedStore { .. }
                if verb == "write" =>
            {
                operation = next;
                break;
            }
            _ => {}
        }
    }
    let bound = format!("0 <= {index} && {index} < {count}");
    let reason = if names.is_empty() {
        format!("`{bound}` does not hold")
    } else {
        format!(
            "could not show `{bound}` from {}",
            describe_consulted_facts_mentioning(available, state, &names)
        )
    };
    Some(format!(
        "the {access} {element} may {verb} outside `{object}`: {reason}\n  C operation: {}",
        crate::surface::diagnostics::describe_execution_statement_head(operation),
    ))
}

/// A bounds check the C frontend lowered to `assert`, refused on the path
/// where its condition is false: the prerequisite left there is the
/// truthiness obligation `0 = 1`, and the condition is what a proof must
/// show.
fn describe_assertion_prerequisite(
    proposition: &Proposition,
    available: &[Proposition],
    state: &ExecutionState,
    statement: &ProgramStatement,
) -> Option<String> {
    let condition = asserted_condition(proposition, statement)?;
    let mut names = Vec::new();
    collect_program_expression_variables(condition, &mut names);
    // A Rust panic check asserts over the lowering's own temporaries, which
    // no proof can name and no fact mentions: state the condition as the
    // pre-state evaluates it, over the source locals it reads.
    if names.iter().any(|name| name.starts_with("__rust_"))
        && let Some(goal) = asserted_condition_goal(state, condition)
    {
        let goal = crate::surface::diagnostics::describe_stated_fact_over_locals(&goal, state);
        let locals = state
            .locals()
            .object_values()
            .filter(|(name, _)| !name.starts_with("__rust_"))
            .map(|(name, _)| crate::kernel::program_local_source_name(name).to_string())
            .collect::<Vec<_>>();
        let names = goal
            .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .filter(|word| locals.iter().any(|local| local == word))
            .collect::<Vec<_>>();
        // A condition over no source local (a lowering flag, such as a
        // storage lifetime) keeps its lowered spelling, which names it.
        if !names.is_empty() {
            return Some(format!(
                "could not show `{goal}` from {}",
                describe_consulted_facts_mentioning(available, state, &names)
            ));
        }
    }
    let names = names.iter().map(String::as_str).collect::<Vec<_>>();
    let condition = describe_program_conjunction(condition);
    // A check over constants alone is simply false: no fact bears on it.
    if names.is_empty() {
        return Some(format!("`{condition}` does not hold"));
    }
    Some(format!(
        "could not show `{condition}` from {}",
        describe_consulted_facts_mentioning(available, state, &names)
    ))
}

/// The condition of the `assert` in `statement` when `proposition` is the
/// truthiness obligation an assertion leaves on its false path.
pub(in crate::surface) fn asserted_condition<'s>(
    proposition: &Proposition,
    statement: &'s ProgramStatement,
) -> Option<&'s ProgramExpression> {
    if !matches!(
        proposition,
        Proposition::Equal(Term::ProgramValue(_), Term::ProgramValue(one)) if *one == int32(1)
    ) {
        return None;
    }
    let mut pending = vec![statement];
    loop {
        match pending.pop()? {
            ProgramStatement::Seq(statements) => {
                pending.extend(statements.iter().rev().map(|statement| statement.as_ref()))
            }
            ProgramStatement::Assert { condition, .. } => return Some(condition),
            _ => {}
        }
    }
}

/// The goal an assertion's false-path truthiness obligation (`0 == 1`)
/// stands for: its condition as the pre-state evaluates it, which the
/// implicit `solve` tries and a proof states with `have`.
pub(in crate::surface) fn asserted_condition_goal(
    state: &ExecutionState,
    condition: &ProgramExpression,
) -> Option<Proposition> {
    // Over no facts, so the evaluation splits on the condition rather than
    // deciding it from the false path's own assumption. The goal is the
    // fact on the path where the condition holds, with that path's
    // polarity: `x > 0` may be recorded as `x <= 0` being false.
    let evaluation = crate::kernel::prove_symbolic_program_condition_evaluation(
        state.clone(),
        condition.clone(),
        crate::kernel::PureFactContext::new(),
    );
    evaluation
        .paths()
        .iter()
        .filter(|path| matches!(path.outcome(), crate::kernel::ConditionOutcome::Value(true)))
        .find_map(|path| {
            path.facts()
                .iter()
                .rev()
                .find_map(|fact| match fact.proposition() {
                    Proposition::ConditionIs(..) => Some(fact.proposition().clone()),
                    _ => None,
                })
        })
}

/// A condition as a proof states it: a conjunction joined by `&&` without
/// the expression printer's parentheses around each operand.
fn describe_program_conjunction(condition: &ProgramExpression) -> String {
    if let ProgramExpression::And(left, right) = condition {
        return format!(
            "{} && {}",
            describe_program_conjunction(left),
            describe_program_conjunction(right)
        );
    }
    let rendered = crate::surface::diagnostics::describe_program_expression(condition);
    match rendered
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))
    {
        Some(inner) if balanced_parentheses(inner) => inner.to_string(),
        _ => rendered,
    }
}

fn balanced_parentheses(text: &str) -> bool {
    let mut depth = 0usize;
    for character in text.chars() {
        match character {
            '(' => depth += 1,
            ')' => match depth.checked_sub(1) {
                Some(next) => depth = next,
                None => return false,
            },
            _ => {}
        }
    }
    depth == 0
}

fn collect_program_expression_variables(expression: &ProgramExpression, names: &mut Vec<String>) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            ProgramExpression::Variable(name) => {
                if !names.contains(name) {
                    names.push(name.clone());
                }
            }
            ProgramExpression::Value(_)
            | ProgramExpression::FunctionAddress(_)
            | ProgramExpression::StepResult { .. } => {}
            ProgramExpression::Cast { expression, .. }
            | ProgramExpression::FloatNegate(expression)
            | ProgramExpression::FloatClassification { expression, .. }
            | ProgramExpression::AddressOf(expression)
            | ProgramExpression::CheckedObjectAddress(expression)
            | ProgramExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | ProgramExpression::Subobject {
                pointer: expression,
                ..
            }
            | ProgramExpression::Not(expression)
            | ProgramExpression::BitwiseNot(expression)
            | ProgramExpression::Load(expression)
            | ProgramExpression::TypedLoad {
                pointer: expression,
                ..
            }
            | ProgramExpression::EnumField {
                value: expression, ..
            }
            | ProgramExpression::EnumIs {
                value: expression, ..
            } => pending.push(expression),
            ProgramExpression::EnumConstruct { fields, .. } => pending.extend(fields.iter().rev()),
            ProgramExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            crate::kernel::binary_c_expression!(left, right) => {
                pending.push(right);
                pending.push(left);
            }
        }
    }
}

/// The consulted condition facts whose source spelling names one of `names`,
/// bounded, as `the facts `a`, `b``.
fn describe_consulted_facts_mentioning(
    available: &[Proposition],
    state: &ExecutionState,
    names: &[&str],
) -> String {
    let mentions = |text: &str| {
        text.split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .any(|word| names.contains(&word))
    };
    let mut described = Vec::new();
    let mut omitted = 0usize;
    for fact in available {
        if !matches!(fact, Proposition::ConditionIs(_, _)) {
            continue;
        }
        let text = crate::surface::diagnostics::describe_stated_fact_over_locals(fact, state);
        if !mentions(&text) || described.contains(&text) {
            continue;
        }
        if described.len() == PREREQUISITE_FACT_LIMIT {
            omitted += 1;
            continue;
        }
        described.push(text);
    }
    if described.is_empty() {
        let names = names
            .iter()
            .map(|name| format!("`{name}`"))
            .collect::<Vec<_>>()
            .join(", ");
        return format!("no fact about {names}");
    }
    let mut listed = described
        .iter()
        .map(|fact| format!("`{fact}`"))
        .collect::<Vec<_>>()
        .join(", ");
    if omitted > 0 {
        listed.push_str(&format!(" and {omitted} more"));
    }
    let noun = if described.len() == 1 && omitted == 0 {
        "the fact"
    } else {
        "the facts"
    };
    format!("{noun} {listed}")
}
