//! The refusal a statement gets when one condition of its own evaluation is
//! not established where the statement is written.
//!
//! A proposition or expression that reads memory, or converts a partial
//! machine term to a mathematical `Integer`, is meaningful only where the
//! conditions of that evaluation hold. The kernel emits them as mandatory
//! obligations, and this module writes the message for the first one the
//! premises in scope do not prove.
//!
//! Everything printed here comes from the lowering's own inputs: the written
//! clause, the names the lowering was given for the kernel's values, the state
//! it ran at, and the premise set it consulted. Nothing is searched for, and no
//! proving decision is made or changed — the message reports the decision the
//! caller already reached.

use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;
use crate::surface::proof_diagnostics::render;

#[cfg(test)]
mod tests;

/// How many premises one refusal lists before saying how many it omitted.
const PREMISE_LIMIT: usize = 12;
/// How many already-established conditions one refusal names.
const ESTABLISHED_LIMIT: usize = 4;

/// What was being lowered, in the spelling the user wrote.
pub(in crate::surface::proof) enum StatedForm<'a> {
    /// A written proposition: an `ensures` or `requires` clause, a `have` goal.
    Proposition(&'a ClickProposition),
    /// A written contract expression: a witness value, a theorem argument.
    Expression(&'a ContractExpression),
    /// A written C fragment: a segment bound, a resource quantity.
    CFragment(&'a CExpression),
}

impl StatedForm<'_> {
    fn describe(&self) -> String {
        match self {
            Self::Proposition(proposition) => {
                crate::surface::diagnostics::describe_click_proposition(proposition)
            }
            Self::Expression(expression) => {
                crate::surface::diagnostics::describe_contract_expression(expression)
            }
            Self::CFragment(expression) => {
                crate::surface::diagnostics::describe_c_expression(expression)
            }
        }
    }

    fn noun(&self) -> &'static str {
        match self {
            Self::Proposition(_) => "the proposition",
            Self::Expression(_) | Self::CFragment(_) => "the expression",
        }
    }
}

/// Where a lowering happened, in the terms a reader of the source has.
///
/// The naming tables are the lowering's own value environment, turned into the
/// parameter/argument shape surface reconstruction reads. That is the only way
/// a kernel variable becomes `hi` and a kernel pointer offset becomes `p` in a
/// message; without it the reader sees `v2` and an argument-memory expression.
pub(in crate::surface::proof) struct StatedSite<'a> {
    form: StatedForm<'a>,
    state: &'a CState,
    parameters: Vec<syntax::C0Parameter>,
    arguments: Vec<CExpression>,
}

impl<'a> StatedSite<'a> {
    /// The site of a lowering whose names come from a value environment.
    pub(in crate::surface::proof) fn new(
        form: StatedForm<'a>,
        state: &'a CState,
        values: &BTreeMap<String, CValue>,
    ) -> Self {
        let mut parameters = Vec::with_capacity(values.len());
        let mut arguments = Vec::with_capacity(values.len());
        for (name, value) in values {
            parameters.push(syntax::C0Parameter::new(
                crate::surface::generics::c0_type_from_kernel(value.c_type()),
                name.clone(),
                None,
            ));
            arguments.push(CExpression::Value(value.clone()));
        }
        Self {
            form,
            state,
            parameters,
            arguments,
        }
    }

    /// One kernel machine term in the user's spelling.
    fn spell_term(&self, term: &Bitvector32Term) -> Option<String> {
        synthesize_surface_machine_expression(term, &self.parameters, &self.arguments, self.state)
            .map(|expression| spelled_alone(&expression))
    }

    /// One kernel proposition as the user would write it, when reconstruction
    /// can name every value it mentions.
    fn spell_proposition(&self, proposition: &Proposition) -> Option<ClickProposition> {
        synthesize_surface_proposition(proposition, &self.parameters, &self.arguments, self.state)
    }
}

/// One evaluation condition, in the reader's vocabulary.
struct SpelledCondition {
    /// The condition as a sentence about the source.
    requirement: String,
    /// The written subterm whose evaluation raised it, when it names one.
    subterm: Option<String>,
    /// What a premise establishing it would look like, when one exists.
    repair: Option<String>,
}

/// Classify and spell one condition.
///
/// A loadability condition is reconstructed through the surface segment
/// machinery, which is what turns an argument-memory offset back into
/// `p[hi - 1..hi]`; the cell it names is that range's base and start. An
/// overflow guard names its own operation. Anything else falls back to the
/// bounded printer, which never dumps the snapshot a term is indexed by.
fn spell_condition(
    condition: &Proposition,
    site: &StatedSite<'_>,
    labels: &mut render::SnapshotLabels,
) -> SpelledCondition {
    let surface = site.spell_proposition(condition);
    let spelled = surface.as_ref().map_or_else(
        || render::render_proposition_labeled(condition, labels),
        crate::surface::diagnostics::describe_click_proposition,
    );
    if let Proposition::CMemoryLoadable { bytes, .. } = condition {
        let width = bytes
            .as_const()
            .map_or_else(|| "the".to_string(), |bytes| format!("the {bytes}"));
        return match loadable_cell(surface.as_ref()) {
            Some(Cell { base, index }) => SpelledCondition {
                requirement: format!("{width} bytes at `{base}[{index}]` must be loadable"),
                subterm: Some(format!("{base}[{index}]")),
                repair: Some(format!(
                    "state that cell's own loadability as a premise in this scope, written as the \
                     one-element range it is: `loadable({base}[{index}..{index} + 1])`"
                )),
            },
            None => SpelledCondition {
                requirement: format!("{width} bytes read here must be loadable: `{spelled}`"),
                subterm: None,
                repair: Some(
                    "state the loadability of exactly the cell this statement reads as a premise \
                     in this scope, as a one-element range"
                        .to_string(),
                ),
            },
        };
    }
    if let Proposition::ConditionIs(condition, false) = condition
        && let Some(operation) = overflowing_operation(condition)
        && let Some(operation) = site.spell_term(&operation)
    {
        return SpelledCondition {
            requirement: format!("`{operation}` must not overflow"),
            subterm: Some(operation.clone()),
            repair: Some(format!(
                "state its definedness as a premise in this scope: `defined({operation})`"
            )),
        };
    }
    if let Proposition::ConditionIs(condition, true) = condition
        && let Some((side, value, bound)) = conversion_bound(condition)
    {
        // A mathematical `Integer` has no source-name reconstruction, so its
        // term prints in the verifier's own value names. Saying which side of
        // which range is missing is the part the reader acts on.
        return SpelledCondition {
            requirement: format!(
                "the Integer converted back to a machine type must fit it: its {side} bound \
                 `{bound}` is not established for the converted value, written here in the \
                 verifier's own Integer value names as `{value}`"
            ),
            subterm: None,
            repair: Some(format!(
                "state that bound on the converted value as a premise in this scope, so that its \
                 {side} bound `{bound}` holds wherever this statement is read"
            )),
        };
    }
    if let Some(pointer) = load_definition_cell(condition) {
        // The equation names a read; the cell it reads is spelled by asking
        // the same reconstruction for the loadability of that cell, which is
        // where the array-index spelling lives.
        let cell = loadable_cell(
            site.spell_proposition(&Proposition::CMemoryLoadable {
                memory: site.state.memory().clone(),
                base: pointer.clone(),
                bytes: Bitvector32Term::Constant(4),
            })
            .as_ref(),
        );
        return SpelledCondition {
            requirement: match cell {
                Some(Cell { base, index }) => {
                    format!("the read at `{base}[{index}]` must denote the value this state holds")
                }
                None => format!("a read must denote the value this state holds: `{spelled}`"),
            },
            subterm: None,
            repair: None,
        };
    }
    SpelledCondition {
        requirement: format!("`{spelled}`"),
        subterm: None,
        repair: None,
    }
}

/// One written cell, kept as its two parts so a message can print both the
/// read `p[hi - 1]` and the one-element range `p[hi - 1..hi - 1 + 1]`.
struct Cell {
    base: String,
    index: String,
}

/// The cell a reconstructed single-element loadability segment names.
///
/// Reconstruction spells a one-cell region two ways. A recovered written range
/// gives `p[hi - 1..hi]` directly. A displaced pointer instead gives the
/// zero-based `(p + (hi - 1))[0..1]`, whose index has been folded into the
/// base; splitting that add back out is what turns the message's subterm into
/// the `p[hi - 1]` the reader wrote.
fn loadable_cell(surface: Option<&ClickProposition>) -> Option<Cell> {
    let ClickProposition::Loadable { segment } = surface? else {
        return None;
    };
    let (base, start, _) = segment.surface_range()?;
    if constant_index(start) == Some(0)
        && let ContractExpression::CFragment(CExpression::Add(pointer, index)) = base
    {
        return Some(Cell {
            base: spelled_alone(&ContractExpression::CFragment(pointer.as_ref().clone())),
            index: spelled_alone(&ContractExpression::CFragment(index.as_ref().clone())),
        });
    }
    Some(Cell {
        base: spelled_alone(base),
        index: spelled_alone(start),
    })
}

/// The constant an index expression is, when it is one.
fn constant_index(expression: &ContractExpression) -> Option<u32> {
    let ContractExpression::CFragment(CExpression::Value(CValue::Int32(term))) = expression else {
        return None;
    };
    term.as_const()
}

/// One expression spelling without the parentheses the expression printer adds
/// around every binary operation.
///
/// The printer parenthesizes because it composes; a subterm named on its own in
/// a sentence does not, and `hi - 1` is what the reader wrote.
fn spelled_alone(expression: &ContractExpression) -> String {
    let rendered = crate::surface::diagnostics::describe_contract_expression(expression);
    let Some(inner) = rendered
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return rendered;
    };
    // Only an outermost pair that closes at the end may be dropped: `(a) + (b)`
    // opens and closes before the end, and stripping it would produce `a) + (b`.
    let mut depth = 0usize;
    for character in inner.chars() {
        match character {
            '(' => depth += 1,
            ')' if depth == 0 => return rendered,
            ')' => depth -= 1,
            _ => {}
        }
    }
    inner.to_string()
}

/// The side, converted value, and limit of a machine-range bound on an
/// `Integer` conversion.
fn conversion_bound(condition: &ConditionTerm) -> Option<(&'static str, String, String)> {
    let (side, value, bound) = match condition {
        ConditionTerm::IntegerGreaterEqual(value, bound) => ("lower", value, bound),
        ConditionTerm::IntegerLessEqual(value, bound) => ("upper", value, bound),
        _ => return None,
    };
    Some((
        side,
        render::render_integer_term(value),
        render::render_integer_term(bound),
    ))
}

/// The machine operation a signed-overflow guard is about.
fn overflowing_operation(condition: &ConditionTerm) -> Option<Bitvector32Term> {
    match condition {
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            Some(Bitvector32Term::Add(left.clone(), right.clone()))
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            Some(Bitvector32Term::Subtract(left.clone(), right.clone()))
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            Some(Bitvector32Term::Multiply(left.clone(), right.clone()))
        }
        _ => None,
    }
}

/// The cell read by the equation naming one memory read, when this condition
/// is such an equation.
fn load_definition_cell(condition: &Proposition) -> Option<&Pointer> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = condition
    else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::Variable(_), Bitvector32Term::MemoryLoad(_, pointer))
        | (Bitvector32Term::MemoryLoad(_, pointer), Bitvector32Term::Variable(_)) => Some(pointer),
        _ => None,
    }
}

/// The premises the refusing lowering consulted, in source spelling.
///
/// The set is read through the context's own fact indexes and the rendering is
/// clipped to [`PREMISE_LIMIT`]; nothing here clones the fact set.
fn consulted_premises(
    assumptions: &PureFactContext,
    site: &StatedSite<'_>,
    labels: &mut render::SnapshotLabels,
) -> (Vec<String>, usize) {
    let mut total = 0;
    let mut shown = Vec::new();
    let conditions = assumptions
        .condition_fact_pairs()
        .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), value));
    for premise in conditions.chain(assumptions.proposition_facts().cloned()) {
        total += 1;
        if shown.len() < PREMISE_LIMIT {
            let spelled = site.spell_proposition(&premise).map_or_else(
                || render::render_proposition_labeled(&premise, labels),
                |surface| crate::surface::diagnostics::describe_click_proposition(&surface),
            );
            shown.push(format!("`{spelled}`"));
        }
    }
    (shown, total)
}

/// Why a loadability condition over one cell was not established, when a
/// premise in scope says something specific about the same object.
///
/// This reports the shape of the premises that are present. It does not rerun
/// the kernel's loadability check and does not claim to enumerate every route
/// that check has.
fn loadability_explanation(
    missing: &Proposition,
    assumptions: &PureFactContext,
    site: &StatedSite<'_>,
    labels: &mut render::SnapshotLabels,
) -> Option<String> {
    let Proposition::CMemoryLoadable { base, bytes, .. } = missing else {
        return None;
    };
    // A wider range over the same object is the interesting case: it is what
    // the reader believes covers the cell, and the one the kernel wants index
    // bounds for.
    let covering = assumptions
        .memory_loadable_fact_propositions()
        .find(|fact| match fact {
            Proposition::CMemoryLoadable {
                base: range_base,
                bytes: range_bytes,
                ..
            } => range_base.block == base.block && range_bytes != bytes,
            _ => false,
        })?;
    let spelled = site.spell_proposition(covering).map_or_else(
        || render::render_proposition_labeled(covering, labels),
        |surface| crate::surface::diagnostics::describe_click_proposition(&surface),
    );
    Some(format!(
        "`{spelled}` is a premise here and was consulted. A range premise establishes one cell \
         only where the cell's index bounds inside that range are themselves established order \
         facts in this scope; this check reads the premises as written and does not rearrange \
         them into those bounds"
    ))
}

/// Refuse the first mandatory evaluation condition the premises in scope do
/// not establish, saying which written subterm raised it, what it requires in
/// the user's names, what was consulted, why that was not enough, and what to
/// write instead.
pub(in crate::surface::proof) fn refuse_unproved_conversion_bounds(
    obligations: &[crate::kernel::ProofObligation],
    assumptions: &PureFactContext,
    site: &StatedSite<'_>,
) -> Result<(), String> {
    for obligation in obligations {
        if obligation.is_assumable() || assumptions.proves(obligation.proposition()) {
            continue;
        }
        return Err(describe_refusal(
            obligation.proposition(),
            assumptions,
            site,
        ));
    }
    Ok(())
}

fn describe_refusal(
    obligation: &Proposition,
    assumptions: &PureFactContext,
    site: &StatedSite<'_>,
) -> String {
    let mut labels = render::SnapshotLabels::default();
    let mut conjuncts = Vec::new();
    let mut pending = vec![obligation];
    while let Some(proposition) = pending.pop() {
        match proposition {
            Proposition::And(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            leaf => conjuncts.push(leaf),
        }
    }
    let unproved = conjuncts
        .iter()
        .find(|conjunct| !assumptions.proves(conjunct))
        .copied()
        .unwrap_or(obligation);
    let established = conjuncts
        .iter()
        .filter(|conjunct| assumptions.proves(conjunct))
        .copied()
        .collect::<Vec<_>>();
    let missing = spell_condition(unproved, site, &mut labels);

    let conditions = |evaluation: &str| match conjuncts.len() {
        1 => format!("1 condition of {evaluation} evaluation holds"),
        count => format!("{count} conditions of {evaluation} evaluation hold"),
    };
    let mut message = format!("{} `{}`: ", site.form.noun(), site.form.describe());
    match &missing.subterm {
        Some(subterm) => message.push_str(&format!(
            "its subterm `{subterm}` denotes a value only where {}",
            conditions("that")
        )),
        None => message.push_str(&format!(
            "it denotes a value only where {}",
            conditions("its")
        )),
    }
    message.push_str(&format!(
        ", and the premises in scope where it is stated establish {} of them, not this one.\
         \n  not established: {}",
        established.len(),
        missing.requirement
    ));

    if !established.is_empty() {
        let mut names = established
            .iter()
            .take(ESTABLISHED_LIMIT)
            .map(|condition| spell_condition(condition, site, &mut labels).requirement)
            .collect::<Vec<_>>();
        if established.len() > ESTABLISHED_LIMIT {
            names.push(format!(
                "… {} more omitted",
                established.len() - ESTABLISHED_LIMIT
            ));
        }
        message.push_str(&format!("\n  established: {}", names.join("; ")));
    }

    let (premises, premise_total) = consulted_premises(assumptions, site, &mut labels);
    if premise_total == 0 {
        message.push_str(
            "\n  premises consulted: none — the premise set this lowering was given is empty, so \
             a premise stated or proved elsewhere in this proof did not reach here",
        );
    } else {
        message.push_str(&format!(
            "\n  premises consulted ({premise_total}, a premise that is a conjunction counted as \
             its conjuncts): {}",
            premises.join(", ")
        ));
        if premise_total > premises.len() {
            message.push_str(&format!(
                ", … {} more omitted",
                premise_total - premises.len()
            ));
        }
    }

    if let Some(explanation) = loadability_explanation(unproved, assumptions, site, &mut labels) {
        message.push_str(&format!("\n  why that was not enough: {explanation}"));
    }

    message.push_str("\n  to repair: ");
    match &missing.repair {
        Some(repair) => message.push_str(repair),
        None => message.push_str(
            "state this condition itself as a premise in this scope, where it can be established",
        ),
    }
    if premise_total == 0 {
        // Advice about what to state is still the right advice; it only takes
        // effect once a premise stated in this scope reaches this lowering, and
        // nothing here can say whether one was written.
        message.push_str(
            ". Nothing can establish it until a premise reaches this lowering at all: the set it \
             consulted above is empty",
        );
    }
    // Item of record for the reader who wants the line: there is none to give.
    // No `.click` clause, proposition, or expression carries a source span in
    // the surface syntax tree — `import` is the only declaration that does — so
    // the claim named at the start of this message and the subterm named above
    // are the whole location.
    message.push_str(
        "\n  no line or column is available: a `.click` clause carries no source span in the \
         surface syntax tree, so this refusal is located by the claim named at the start of this \
         message and by the subterm above",
    );
    message
}
