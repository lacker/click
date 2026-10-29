use super::prelude::*;
use super::{ResourceDescription, ResourceFieldSchema};
use crate::kernel::CompareRelation;

thread_local! {
    static PRESERVE_INTEGER_COMPARISONS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Certificate operands retain their written machine observations. Ordinary
/// lowering still stores the equivalent native comparison as its single fact.
pub(crate) fn with_preserved_integer_comparisons<T>(operation: impl FnOnce() -> T) -> T {
    with_integer_comparisons_preserved(true, operation)
}

/// A condition inside a term, such as an `if` condition, is part of the
/// term's value rather than a certificate operand: it takes the one form
/// ordinary lowering gives it, so a term reads the same wherever it is cited.
fn with_integer_comparisons_preserved<T>(preserve: bool, operation: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            PRESERVE_INTEGER_COMPARISONS.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(PRESERVE_INTEGER_COMPARISONS.with(|flag| flag.replace(preserve)));
    operation()
}

mod existential;
mod quantifier_polarity;
pub(in crate::kernel) mod predicate_dependencies;
pub(in crate::kernel) mod walk;

type EvaluatedSpecResource = (CResource, ExecutionFacts, Vec<ProofObligation>);
type SpecResourceBuilder = Box<dyn Fn(Vec<CValue>) -> Option<CResource>>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SpecPropositionPath {
    pub(super) proposition: Proposition,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    /// The head chain of `proposition`, outermost first, recorded by the
    /// lowering step that built each node. A consumer that introduces the
    /// head of this proposition reads which nodes lowering inserted and
    /// which kernel variable each written universal was bound to, instead of
    /// guessing from the shape the written syntax happens to share.
    pub(super) introductions: LoweringIntroductions,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SpecExpressionPath {
    pub(super) value: CValue,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SpecIntegerPath {
    pub(super) value: IntegerTerm,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecSequencePath {
    value: SequenceTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecAlgebraicPath {
    value: AlgebraicTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

/// The interpretation of specification reads is lexical: ordinary expressions
/// denote logical values, while `defined(...)` explicitly asks for validity.
/// Both use the same expression walker and the same execution work budget.
/// Where a specification is read: the state, the loop-entry state that
/// `old` reads, and the bound algebraic names. Every evaluation step below
/// reads one scope; the assumptions it decides under change along paths and
/// are passed separately.
#[derive(Clone, Copy)]
struct SpecScope<'a> {
    state: &'a CState,
    loop_entry_state: Option<&'a CState>,
    algebraic_bindings: &'a BTreeMap<String, AlgebraicTerm>,
}

static NO_ALGEBRAIC_BINDINGS: BTreeMap<String, AlgebraicTerm> = BTreeMap::new();

impl<'a> SpecScope<'a> {
    fn new(
        state: &'a CState,
        loop_entry_state: Option<&'a CState>,
        algebraic_bindings: &'a BTreeMap<String, AlgebraicTerm>,
    ) -> Self {
        Self {
            state,
            loop_entry_state,
            algebraic_bindings,
        }
    }

    /// A scope with no bound algebraic names.
    fn unbound(state: &'a CState, loop_entry_state: Option<&'a CState>) -> Self {
        Self::new(state, loop_entry_state, &NO_ALGEBRAIC_BINDINGS)
    }
}

struct SpecEvaluation<'a> {
    budget: &'a mut ExecutionBudget,
    checked_reads: bool,
    /// Only the selected body of an already held resource, or an interface
    /// proposition checked where it is established, may introduce its
    /// well-formed logical calls' nominal argument requirements.
    recover_resource_call_types: bool,
    pointer_cast_operand: bool,
    integer_bindings: BTreeMap<Variable, IntegerTerm>,
}

impl<'a> SpecEvaluation<'a> {
    fn logical(budget: &'a mut ExecutionBudget) -> Self {
        Self {
            budget,
            checked_reads: false,
            recover_resource_call_types: false,
            pointer_cast_operand: false,
            integer_bindings: BTreeMap::new(),
        }
    }
    fn checked(budget: &'a mut ExecutionBudget) -> Self {
        Self {
            budget,
            checked_reads: true,
            recover_resource_call_types: false,
            pointer_cast_operand: false,
            integer_bindings: BTreeMap::new(),
        }
    }
    fn with_integer_bindings<T>(
        &mut self,
        variables: &[Option<Variable>],
        fields: &[AlgebraicValue],
        body: impl FnOnce(&mut Self) -> ExecutionResult<T>,
    ) -> ExecutionResult<T> {
        if variables.len() != fields.len()
            || variables.iter().zip(fields).any(|(variable, field)| {
                variable.is_some() && !matches!(field, AlgebraicValue::Integer(_))
            })
        {
            return Err(ExecutionLimit::Paths);
        }
        let mut saved = Vec::new();
        for (variable, field) in variables.iter().zip(fields) {
            if let Some(variable) = variable {
                let AlgebraicValue::Integer(field) = field else {
                    return Err(ExecutionLimit::Paths);
                };
                crate::instrumentation::record_deterministic_work(1);
                saved.push((
                    *variable,
                    self.integer_bindings.insert(*variable, field.clone()),
                ));
            }
        }
        let result = body(self);
        for (variable, previous) in saved.into_iter().rev() {
            match previous {
                Some(previous) => {
                    self.integer_bindings.insert(variable, previous);
                }
                None => {
                    self.integer_bindings.remove(&variable);
                }
            }
        }
        result
    }

    fn bound_integer_term(&self, term: &IntegerTerm) -> ExecutionResult<IntegerTerm> {
        if self.integer_bindings.is_empty() {
            return Ok(term.clone());
        }
        match term {
            IntegerTerm::Variable(variable) => {
                crate::instrumentation::record_deterministic_work(1);
                return Ok(self
                    .integer_bindings
                    .get(variable)
                    .cloned()
                    .unwrap_or_else(|| term.clone()));
            }
            IntegerTerm::Constant(_) => return Ok(term.clone()),
            _ => {}
        }
        // Select replacements from this payload only. Never scan the ambient
        // binder stack or rewrite entire descendant specification bodies.
        let mut variables = BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_integer_variables(
            term,
            &mut variables,
        );
        let replacements = variables
            .into_iter()
            .filter_map(|variable| {
                self.integer_bindings
                    .get(&variable)
                    .cloned()
                    .map(|value| (variable, value))
            })
            .collect::<BTreeMap<_, _>>();
        if replacements.is_empty() {
            return Ok(term.clone());
        }
        rewrite_integer_match_typed_body(
            term.clone(),
            &BTreeMap::new(),
            &replacements,
            &BTreeMap::new(),
        )
        .ok_or(ExecutionLimit::Paths)
    }
}

impl std::ops::Deref for SpecEvaluation<'_> {
    type Target = ExecutionBudget;
    fn deref(&self) -> &Self::Target {
        self.budget
    }
}
impl std::ops::DerefMut for SpecEvaluation<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.budget
    }
}

pub(super) fn lower_spec_proposition_at_state_with_loop_entry(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    lower_spec_proposition_at_state_with_loop_entry_in(
        state,
        proposition,
        loop_entry_state,
        assumptions,
        &mut SpecEvaluation::logical(budget),
    )
}

pub(in crate::kernel) fn lower_spec_proposition_at_state_without_range_guards(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    lower_spec_proposition_at_state_without_range_guards_in(
        state,
        proposition,
        loop_entry_state,
        assumptions,
        &mut SpecEvaluation::logical(budget),
    )
}

pub(in crate::kernel) fn lower_spec_proposition_at_state_with_algebraic_bindings(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    lower_spec_proposition_at_state_with_algebraic_bindings_in(
        SpecScope::new(state, loop_entry_state, algebraic_bindings),
        proposition,
        assumptions,
        &mut SpecEvaluation::logical(budget),
    )
}

/// Open the logical facts of an active, selected resource body. Holding the
/// resource justifies the nominal domains of the calls written in that body;
/// folding uses ordinary lowering and must establish those domains itself.
/// Receipts stay with each evaluation path, never with interned call arguments.
pub(in crate::kernel) fn lower_held_resource_body_clause(
    state: &CState,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut evaluation = SpecEvaluation::logical(budget);
    evaluation.recover_resource_call_types = true;
    lower_spec_proposition_at_state_with_algebraic_bindings_in(
        SpecScope::new(state, None, algebraic_bindings),
        proposition,
        assumptions,
        &mut evaluation,
    )
}

/// Lower a proposition that an interface assumes after checking it
/// elsewhere: a loop invariant at the loop head, or a `branch ensuring` fact
/// at the join. Entry and every back edge, or every arm, lower the same
/// proposition with ordinary lowering, which must establish the nominal
/// argument domains of its typed calls, and refuse it when it has no reading
/// there. Those domains are therefore part of what is assumed: this lowering
/// may introduce them for fresh values, as holding a resource does for its
/// selected body.
pub(in crate::kernel) fn lower_assumed_interface_proposition(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut evaluation = SpecEvaluation::logical(budget);
    evaluation.recover_resource_call_types = true;
    lower_spec_proposition_at_state_with_loop_entry_in(
        state,
        proposition,
        entry_state,
        assumptions,
        &mut evaluation,
    )
}

pub(in crate::kernel) fn evaluate_spec_expression_paths_with_bindings(
    state: &CState,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    evaluate_spec_expression_paths_with_bindings_in(
        state,
        expression,
        assumptions,
        algebraic_bindings,
        &mut SpecEvaluation::logical(budget),
    )
}

pub(in crate::kernel) fn evaluate_resource_child_argument_paths(
    state: &CState,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    integer_bindings: &BTreeMap<Variable, IntegerTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    if let SpecExpression::CExpression(expression) = expression {
        let _specification = crate::kernel::eval::SpecificationReadScope::enter();
        return evaluate_c_expression_paths(state, expression, assumptions, budget);
    }
    let rewritten;
    let expression = if integer_bindings.is_empty() {
        expression
    } else {
        let c_replacements = BTreeMap::new();
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite =
            crate::kernel::proof::term_rewrite::TermRewrite::for_checked_typed_variables(
                &c_replacements,
                integer_bindings,
                &algebraic_replacements,
            );
        rewritten = rewrite
            .spec_expression(expression)
            .map_err(|_| ExecutionLimit::ExpressionSteps)?;
        &rewritten
    };
    let paths = evaluate_spec_expression_paths_with_bindings_in(
        state,
        expression,
        assumptions,
        algebraic_bindings,
        &mut SpecEvaluation::checked(budget),
    )?;
    Ok(paths
        .into_iter()
        .map(|path| CExpressionPath {
            outcome: CExpressionOutcome::Value(path.value),
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect())
}

pub(super) fn evaluate_spec_integer_measure_paths(
    state: &CState,
    expression: &SpecIntegerExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    evaluate_spec_integer_measure_paths_in(
        state,
        expression,
        assumptions,
        &mut SpecEvaluation::logical(budget),
    )
}

pub(super) fn evaluate_spec_expression_paths_with_loop_entry(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    evaluate_spec_expression_paths_with_loop_entry_in(
        state,
        expression,
        loop_entry_state,
        assumptions,
        &mut SpecEvaluation::logical(budget),
    )
}

/// Resource-address evaluation requests validity explicitly; pure proposition
/// lowering uses the logical entry point above.
pub(super) fn evaluate_spec_expression_checked_paths_with_loop_entry(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    evaluate_spec_expression_paths_with_loop_entry_in(
        state,
        expression,
        loop_entry_state,
        assumptions,
        &mut SpecEvaluation::checked(budget),
    )
}

/// Capture a symbolic ADT value without admitting case assumptions or
/// unresolved arithmetic obligations into a resource initializer.
pub(crate) fn capture_spec_algebraic_value(
    state: &CState,
    expression: &SpecAlgebraicExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<AlgebraicTerm, String> {
    let paths = evaluate_spec_algebraic_at_state_with_bindings_in(
        SpecScope::unbound(state, entry_state),
        expression,
        assumptions,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
    )
    .map_err(|limit| {
        format!(
            "algebraic initializer evaluation stopped at {}",
            limit.describe()
        )
    })?;
    let [path] = paths.as_slice() else {
        return Err("algebraic initializer must denote one symbolic value".into());
    };
    if path.facts.has_path_conditions()
        || path
            .obligations
            .iter()
            .any(|o| !assumptions.proves_exact(o.proposition()))
    {
        return Err("algebraic initializer has unproved evaluation obligations".into());
    }
    Ok(path.value.clone())
}

/// Smart theorem selection asks only for the evaluation conditions of its
/// selected model argument. This query grants no value or proof authority:
/// the explicit application still checks the selected premises. Evaluate with
/// those premises, not ambient facts, so discharged ambient guards are retained.
pub(crate) fn algebraic_argument_evaluation_guards(
    state: &CState,
    expression: &SpecAlgebraicExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<Vec<Proposition>, String> {
    use walk::{SpecNode, Visit, spec_tree_all};

    let scope = SpecScope::unbound(state, entry_state);
    let mut execution_budget = ExecutionBudget::beside_live_state();
    let mut evaluation = SpecEvaluation::logical(&mut execution_budget);
    let mut guards = Vec::new();
    let mut refusal = None;
    spec_tree_all(SpecNode::Algebraic(expression), |node| {
        if let Err(limit) = evaluation.consume_expression_step() {
            refusal = Some(format!(
                "model argument evaluation stopped at {}",
                limit.describe()
            ));
            return Visit::Stop(());
        }
        // Constructors and ordinary opaque calls need their arguments' guards,
        // not their materialized model values. In particular a checked model
        // field cannot introduce evaluation guards from its stored contents.
        // Keep matches/conditionals and partial builtins with their evaluator:
        // its scoping decides which conditions are actually required.
        let paths = match node {
            SpecNode::Algebraic(algebraic) => match &algebraic.node {
                SpecAlgebraicExpressionNode::Variable(_)
                | SpecAlgebraicExpressionNode::Binding(_)
                | SpecAlgebraicExpressionNode::ResourceField(_) => return Visit::Skip,
                SpecAlgebraicExpressionNode::Constructor { .. } => return Visit::Descend,
                SpecAlgebraicExpressionNode::PureFunctionApplication { name, .. }
                    if name != "to_nat" =>
                {
                    return Visit::Descend;
                }
                _ => evaluate_spec_algebraic_at_state_with_bindings_in(
                    scope,
                    algebraic,
                    assumptions,
                    &mut evaluation,
                )
                .map(|paths| {
                    paths
                        .into_iter()
                        .map(|path| (path.facts, path.obligations))
                        .collect::<Vec<_>>()
                }),
            },
            SpecNode::AlgebraicValue(_) | SpecNode::Argument(_) => return Visit::Descend,
            SpecNode::Expression(expression) => {
                evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    scope,
                    expression,
                    assumptions,
                    &mut evaluation,
                )
                .map(|paths| {
                    paths
                        .into_iter()
                        .map(|path| (path.facts, path.obligations))
                        .collect()
                })
            }
            SpecNode::Integer(expression) => evaluate_spec_integer_expression_paths_in(
                scope,
                expression,
                assumptions,
                &mut evaluation,
            )
            .map(|paths| {
                paths
                    .into_iter()
                    .map(|path| (path.facts, path.obligations))
                    .collect()
            }),
            _ => {
                refusal = Some("unsupported model argument evaluation guard".into());
                return Visit::Stop(());
            }
        };
        let mut paths = match paths {
            Ok(paths) => paths,
            Err(limit) => {
                refusal = Some(format!(
                    "model argument evaluation stopped at {}",
                    limit.describe()
                ));
                return Visit::Stop(());
            }
        };
        if paths.len() != 1 {
            refusal = Some("model argument needs explicit evaluation evidence: evaluation does not select one symbolic value".into());
            return Visit::Stop(());
        }
        let (facts, obligations) = paths.pop().unwrap();
        if crate::instrumentation::deadline_exceeded_with_work(
            facts.len().saturating_add(obligations.len()),
        ) {
            refusal = Some("model argument guard retention exceeded its work limit".into());
            return Visit::Stop(());
        }
        guards.extend(
            facts
                .iter()
                .filter(|fact| !fact.is_certified())
                .map(|fact| fact.proposition().clone()),
        );
        guards.extend(
            obligations
                .into_iter()
                .map(|obligation| obligation.proposition().clone()),
        );
        Visit::Skip
    });
    match refusal {
        Some(message) => Err(message),
        None => Ok(guards),
    }
}

/// The written subterm of a captured Integer expression that an evaluation
/// condition came from. A capture refusal names it so the reader is pointed
/// at the part of the source that has to change, rather than at whichever
/// node the capture entry point happens to be called for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpecCaptureSubterm {
    RangeEndpoint,
    FoldInitializer,
    FoldBody,
    Expression,
}

impl SpecCaptureSubterm {
    pub fn describe(self) -> &'static str {
        match self {
            SpecCaptureSubterm::RangeEndpoint => "the fold's range endpoint",
            SpecCaptureSubterm::FoldInitializer => "the fold's initializer",
            SpecCaptureSubterm::FoldBody => "the fold's body",
            SpecCaptureSubterm::Expression => "this Integer expression",
        }
    }
}

/// Why capturing an Integer expression as one symbolic term was refused.
#[derive(Clone, Debug)]
pub enum SpecCaptureRefusal {
    Message(String),
    /// Evaluating `subterm` is only valid where `proposition` holds, and the
    /// proof context does not state it.
    Undischarged {
        subterm: SpecCaptureSubterm,
        proposition: Proposition,
    },
}

impl From<String> for SpecCaptureRefusal {
    fn from(message: String) -> Self {
        SpecCaptureRefusal::Message(message)
    }
}

/// Capture a symbolic Integer value without admitting case assumptions or
/// unresolved arithmetic obligations into a resource initializer.
pub(crate) fn capture_spec_integer_value(
    state: &CState,
    expression: &SpecIntegerExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<IntegerTerm, SpecCaptureRefusal> {
    capture_spec_integer_value_with_guards(state, expression, entry_state, assumptions)
        .map(|(value, _)| value)
}

/// Retain non-certified guards and obligations carried by the captured path.
/// Conditions already discharged during evaluation may no longer occur here;
/// consumers must recheck argument capture with the selected explicit evidence.
pub(crate) fn capture_spec_integer_value_with_guards(
    state: &CState,
    expression: &SpecIntegerExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(IntegerTerm, Vec<Proposition>), SpecCaptureRefusal> {
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(state, entry_state),
        expression,
        assumptions,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
    )
    .map_err(|limit| {
        SpecCaptureRefusal::Message(format!(
            "Integer expression evaluation stopped at {}",
            limit.describe()
        ))
    })?;
    let [path] = paths.as_slice() else {
        return Err(SpecCaptureRefusal::Message(format!(
            "this Integer expression does not denote one symbolic value here: \
             evaluating it produced {} paths rather than one, so a partial \
             operation or a condition inside it is not decided here",
            paths.len()
        )));
    };
    // A path fact guards the evaluation path this value was read off: an
    // int32 endpoint `hi - 1` is this value only where the subtraction does
    // not overflow. Where the ambient context already states that guard, the
    // guarded path is the only live one, so admitting the fact changes
    // nothing about what the captured term asserts. Discharge it by the same
    // exact routes an obligation uses -- no search -- and keep refusing a
    // fact that is genuinely unavailable, which is the case below.
    // Kernel-certified consequences (such as the observation of a guarded
    // native result) are definitions, not extra assumptions the caller must
    // restate. Their path guards and proof obligations still need discharge.
    let undischarged = path
        .facts
        .iter()
        .filter(|fact| !fact.is_certified())
        .map(|fact| fact.proposition())
        .chain(path.obligations.iter().map(|o| o.proposition()))
        .find(|proposition| !required_obligation_is_exactly_discharged(assumptions, proposition));
    if let Some(proposition) = undischarged {
        let subterm = locate_spec_integer_capture_condition(
            state,
            expression,
            entry_state,
            assumptions,
            proposition,
        );
        return Err(SpecCaptureRefusal::Undischarged {
            subterm,
            proposition: proposition.clone(),
        });
    }
    if crate::instrumentation::deadline_exceeded_with_work(
        path.facts.len().saturating_add(path.obligations.len()),
    ) {
        return Err(SpecCaptureRefusal::Message(
            "Integer capture guard retention exceeded its work limit".into(),
        ));
    }
    let guards = path
        .facts
        .iter()
        .filter(|fact| !fact.is_certified())
        .map(|fact| fact.proposition().clone())
        .chain(path.obligations.iter().map(|o| o.proposition().clone()))
        .collect();
    Ok((path.value.clone(), guards))
}

/// Which written subterm contributed `proposition` to a capture path.
///
/// This runs only on the refusal path, where naming the offending subterm is
/// worth re-evaluating the two small header subterms of a fold; a successful
/// capture never reaches it.
fn locate_spec_integer_capture_condition(
    state: &CState,
    expression: &SpecIntegerExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> SpecCaptureSubterm {
    let SpecIntegerExpression::RangeFold { index, initial, .. } = expression else {
        return SpecCaptureSubterm::Expression;
    };
    let contributed = |facts: &ExecutionFacts, obligations: &[ProofObligation]| {
        facts.iter().any(|fact| fact.proposition() == proposition)
            || obligations.iter().any(|o| o.proposition() == proposition)
    };
    if let Ok(index_paths) = evaluate_spec_integer_range_fold_indices_in(
        SpecScope::unbound(state, entry_state),
        index,
        assumptions,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
    ) && index_paths
        .iter()
        .any(|(_, facts, obligations)| contributed(facts, obligations))
    {
        return SpecCaptureSubterm::RangeEndpoint;
    }
    if let Ok(initial_paths) = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(state, entry_state),
        initial,
        assumptions,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
    ) && initial_paths
        .iter()
        .any(|path| contributed(&path.facts, &path.obligations))
    {
        return SpecCaptureSubterm::FoldInitializer;
    }
    SpecCaptureSubterm::FoldBody
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecAlgebraicCasePath {
    variant: String,
    fields: Vec<AlgebraicValue>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecAlgebraicValuePath {
    value: AlgebraicValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecPureFunctionArgumentPath {
    value: PureFunctionArgument,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

fn lower_spec_proposition_at_state_with_loop_entry_in(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    lower_spec_proposition_at_state_with_algebraic_bindings_in(
        SpecScope::unbound(state, loop_entry_state),
        proposition,
        assumptions,
        budget,
    )
}

fn lower_spec_proposition_at_state_without_range_guards_in(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    // Composite-resource population setup treats loadability as an opaque
    // symbolic summary; the contained ranges supply its validity conditions.
    // Separation retains its range-validity conjuncts even in a resource
    // definition: folding establishes them and observing may expose them.
    let SpecProposition::MemoryLoadable {
        memory,
        base,
        start,
        end,
        element_width,
    } = proposition
    else {
        return lower_spec_proposition_at_state_with_algebraic_bindings_in(
            SpecScope::unbound(state, loop_entry_state),
            proposition,
            assumptions,
            budget,
        );
    };
    lower_spec_memory_loadable_at_state_in(
        SpecScope::unbound(state, loop_entry_state),
        memory,
        base,
        start,
        end,
        *element_width,
        assumptions,
        budget,
        false,
    )
}

fn lower_spec_proposition_at_state_with_algebraic_bindings_in(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    if let Some(paths) = quantifier_polarity::lower_prefix(scope, proposition, assumptions, budget)? {
        return Ok(paths);
    }
    if let Some(paths) = lower_spec_negation_chain_in(scope, proposition, assumptions, budget)? {
        return Ok(paths);
    }
    if let Some(paths) =
        lower_spec_conjunction_left_spine_in(scope, proposition, assumptions, budget)?
    {
        return Ok(paths);
    }
    if let Some(paths) = lower_spec_universal_chain_in(scope, proposition, assumptions, budget)? {
        return Ok(paths);
    }
    if let Some(paths) =
        lower_simple_spec_implication_chain_in(scope, proposition, assumptions, budget)?
    {
        return Ok(paths);
    }
    lower_spec_proposition_at_state_with_algebraic_bindings_one_in(
        scope,
        proposition,
        assumptions,
        budget,
    )
}

fn lower_spec_negation_chain_in(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<Vec<SpecPropositionPath>>> {
    let mut count = 0;
    let mut body = proposition;
    while let SpecProposition::Not(inner) = body {
        count += 1;
        body = inner;
    }
    if count == 0 {
        return Ok(None);
    }

    let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        body,
        assumptions,
        budget,
    )?;
    for _ in 0..count {
        paths = paths.into_iter().map(wrap_spec_negation_path).collect();
    }
    Ok(Some(paths))
}

fn wrap_spec_negation_path(path: SpecPropositionPath) -> SpecPropositionPath {
    // A negated condition is the condition with the other value, as an
    // execution spells the branch it did not take. Only the remaining shape
    // keeps a `Not` node an introduction can reach.
    let (proposition, introductions) = match path.proposition {
        Proposition::ConditionIs(condition, value) => (
            Proposition::ConditionIs(condition, !value),
            LoweringIntroductions::new(),
        ),
        proposition => (
            Proposition::Not(Box::new(proposition)),
            vec![LoweringIntroduction::WrittenNegation],
        ),
    };
    SpecPropositionPath {
        proposition,
        facts: path.facts,
        obligations: path.obligations,
        introductions,
    }
}

/// Lowers the parser's left-associated `and` chain iteratively. Each right
/// operand still sees the accumulated path context from the complete prefix,
/// exactly as it does in the recursive binary case.
fn lower_spec_conjunction_left_spine_in(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<Vec<SpecPropositionPath>>> {
    let mut right_operands = Vec::new();
    let mut leftmost = proposition;
    while let SpecProposition::And(left, right) = leftmost {
        right_operands.push(right.as_ref());
        leftmost = left;
    }
    if right_operands.is_empty() {
        return Ok(None);
    }

    let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        leftmost,
        assumptions,
        budget,
    )?;
    for right in right_operands.into_iter().rev() {
        let mut combined = Vec::new();
        for left_path in paths {
            let right_assumptions = assumptions_with_path_context(
                assumptions,
                &left_path.facts,
                &left_path.obligations,
            );
            for right_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                right,
                &right_assumptions,
                budget,
            )? {
                if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &left_path.facts,
                    &left_path.obligations,
                    &right_path.facts,
                    &right_path.obligations,
                    assumptions,
                    &right_assumptions,
                ) {
                    combined.push(SpecPropositionPath {
                        introductions: Vec::new(),
                        proposition: Proposition::And(
                            Box::new(left_path.proposition.clone()),
                            Box::new(right_path.proposition),
                        ),
                        facts,
                        obligations,
                    });
                }
            }
        }
        paths = combined;
    }
    Ok(Some(paths))
}

#[derive(Clone)]
struct SpecUniversalBinder {
    name: String,
    variable: Variable,
    sort: Sort,
    pointer: bool,
    integer: bool,
}

/// Lowers a run of written universal quantifiers without putting one Rust
/// stack frame around each binder. Surface syntax deliberately supports deep
/// propositions, and the state extensions for C-valued binders can be
/// accumulated before lowering the innermost body.
fn lower_spec_universal_chain_in(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<Vec<SpecPropositionPath>>> {
    let mut binders = Vec::new();
    let mut body = proposition;
    // A binder is bound by its `Variable` alone, here and in the quantifier
    // arms of `lower_spec_proposition_at_state_with_algebraic_bindings_one_in`.
    // The Surface resolves every bound occurrence to that variable before the
    // kernel sees the body, so the body is lowered at `state` unchanged.
    // Binding the source spelling as a local would shadow a C local of that
    // spelling, such as a predicate argument substituted under a same-named
    // binder, and read it as the bound variable (regression:
    // `mdtests/an_unfolded_quantifier_does_not_capture_a_same_named_argument.md`).
    let mut quantified_assumptions = assumptions.clone();

    loop {
        let quantifier = body;
        let (binder, next_body) = match body {
            SpecProposition::ForAllInteger {
                name,
                variable,
                body,
            } => (
                SpecUniversalBinder {
                    name: name.clone(),
                    variable: *variable,
                    sort: Sort::Integer,
                    pointer: false,
                    integer: true,
                },
                body.as_ref(),
            ),
            SpecProposition::ForAllAlgebraic {
                name,
                variable,
                algebraic_type,
                body,
            } => (
                SpecUniversalBinder {
                    name: name.clone(),
                    variable: *variable,
                    sort: Sort::Algebraic(algebraic_type.clone()),
                    pointer: false,
                    integer: false,
                },
                body.as_ref(),
            ),
            SpecProposition::ForAllMachineInteger {
                name,
                variable,
                body,
                ..
            }
            | SpecProposition::ForAllInt32 {
                name,
                variable,
                body,
            } => {
                let integer_type = match quantifier {
                    SpecProposition::ForAllMachineInteger { integer_type, .. } => *integer_type,
                    _ => MachineIntegerType::Int32,
                };
                (
                    SpecUniversalBinder {
                        name: name.clone(),
                        variable: *variable,
                        sort: Sort::machine_integer(integer_type),
                        pointer: false,
                        integer: false,
                    },
                    body.as_ref(),
                )
            }
            SpecProposition::ForAllPointer {
                name,
                variable,
                c_type,
                body,
            } => (
                SpecUniversalBinder {
                    name: name.clone(),
                    variable: *variable,
                    sort: Sort::CPointer(*c_type),
                    pointer: true,
                    integer: false,
                },
                body.as_ref(),
            ),
            _ => break,
        };
        for fact in machine_quantifier_range_facts(&binder.sort, binder.variable) {
            quantified_assumptions =
                quantified_assumptions.assume_proposition(fact.proposition().clone());
        }
        binders.push(binder);
        body = next_body;
    }

    if binders.is_empty() {
        return Ok(None);
    }

    let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        body,
        &quantified_assumptions,
        budget,
    )?;
    for binder in binders.into_iter().rev() {
        paths = paths
            .into_iter()
            .map(|path| wrap_spec_universal_path(path, &binder))
            .collect();
    }
    Ok(Some(paths))
}

fn machine_quantifier_range_facts(sort: &Sort, variable: Variable) -> ExecutionFacts {
    sort.machine_integer_type()
        .and_then(|ty| super::api::c_narrow_integer_range_facts(&ty.symbolic_value(variable)))
        .unwrap_or_default()
        .into_iter()
        .map(ExecutionPureFact::certified)
        .collect()
}

fn wrap_spec_universal_path(
    mut path: SpecPropositionPath,
    binder: &SpecUniversalBinder,
) -> SpecPropositionPath {
    let mut range_facts = machine_quantifier_range_facts(&binder.sort, binder.variable);
    range_facts.append(&mut path.facts);
    path.facts = range_facts;
    let (body, guards) = wrap_path_context_with_introductions(path.proposition, &path.facts, &[]);
    let mut introductions = vec![LoweringIntroduction::WrittenUniversal {
        name: binder.name.clone(),
        variable: binder.variable,
        pointer: binder.pointer,
        integer: binder.integer,
    }];
    introductions.extend(guards);
    introductions.extend(path.introductions);
    SpecPropositionPath {
        proposition: Proposition::ForAll {
            var: binder.variable,
            sort: binder.sort.clone(),
            body: Box::new(body),
            name: BinderName::written(&binder.name),
        },
        facts: Vec::new().into(),
        obligations: path
            .obligations
            .into_iter()
            .map(|obligation| {
                obligation.map_proposition(|proposition| Proposition::ForAll {
                    var: binder.variable,
                    sort: binder.sort.clone(),
                    name: BinderName::written(&binder.name),
                    body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                })
            })
            .collect(),
        introductions,
    }
}

/// Lowers the common right-associated implication shape iteratively. The
/// ordinary recursive lowering remains the fallback for propositions whose
/// antecedents need path routing, facts, or obligations.
fn lower_simple_spec_implication_chain_in(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<Vec<SpecPropositionPath>>> {
    let mut antecedents = Vec::new();
    let mut consequent = proposition;
    while let SpecProposition::Implies(left, right) = consequent {
        antecedents.push(left.as_ref());
        consequent = right;
    }
    if antecedents.is_empty() {
        return Ok(None);
    }

    let mut chain_assumptions = assumptions.clone();
    let mut lowered_antecedents = Vec::with_capacity(antecedents.len());
    let antecedent_count = antecedents.len();
    for antecedent in &antecedents {
        let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_one_in(
            scope,
            antecedent,
            &chain_assumptions,
            budget,
        )?;
        if paths.len() != 1 {
            return Ok(None);
        }
        let path = paths.pop().expect("the path count was checked");
        if path.facts.has_path_conditions() || !path.obligations.is_empty() {
            return Ok(None);
        }
        chain_assumptions = chain_assumptions.assume_proposition(path.proposition.clone());
        lowered_antecedents.push(path.proposition);
    }

    let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_one_in(
        scope,
        consequent,
        &chain_assumptions,
        budget,
    )?;
    if paths.len() != 1 {
        return Ok(None);
    }
    let mut path = paths.pop().expect("the path count was checked");
    if path.facts.has_path_conditions() || !path.obligations.is_empty() {
        return Ok(None);
    }

    let mut lowered = path.proposition;
    for antecedent in lowered_antecedents.into_iter().rev() {
        lowered = Proposition::Implies(Box::new(antecedent), Box::new(lowered));
    }
    Ok(Some(vec![SpecPropositionPath {
        proposition: lowered,
        facts: Vec::new().into(),
        obligations: Vec::new(),
        introductions: {
            let mut introductions = Vec::new();
            introductions.resize(
                // Each written implication contributes one introduction; the
                // consequent's introductions retain their original order.
                antecedent_count,
                LoweringIntroduction::WrittenImplication,
            );
            introductions.append(&mut path.introductions);
            introductions
        },
    }]))
}

fn lower_spec_proposition_at_state_with_algebraic_bindings_one_in(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    match proposition {
        SpecProposition::IntegerComparison {
            left,
            operator,
            right,
        } => {
            let left_paths =
                evaluate_spec_integer_expression_paths_in(scope, left, assumptions, budget)?;
            let mut result = Vec::new();
            for left_path in left_paths {
                let path_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in evaluate_spec_integer_expression_paths_in(
                    scope,
                    right,
                    &path_assumptions,
                    budget,
                )? {
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &left_path.facts,
                            &left_path.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                            &path_assumptions,
                        )
                    else {
                        continue;
                    };
                    let condition = match operator {
                        IntegerComparisonOperator::Equal => ConditionTerm::integer_equal(
                            left_path.value.clone(),
                            right_path.value.clone(),
                        ),
                        IntegerComparisonOperator::NotEqual => ConditionTerm::integer_not_equal(
                            left_path.value.clone(),
                            right_path.value.clone(),
                        ),
                        IntegerComparisonOperator::LessThan => ConditionTerm::integer_less_than(
                            left_path.value.clone(),
                            right_path.value.clone(),
                        ),
                        IntegerComparisonOperator::LessEqual => ConditionTerm::integer_less_equal(
                            left_path.value.clone(),
                            right_path.value.clone(),
                        ),
                        IntegerComparisonOperator::GreaterThan => {
                            ConditionTerm::integer_greater_than(
                                left_path.value.clone(),
                                right_path.value.clone(),
                            )
                        }
                        IntegerComparisonOperator::GreaterEqual => {
                            ConditionTerm::integer_greater_equal(
                                left_path.value.clone(),
                                right_path.value.clone(),
                            )
                        }
                    };
                    // One fact, one form: an Integer comparison of exact
                    // observations of one machine type holds exactly when
                    // the native comparison of their carriers does, so it is
                    // that native comparison. A type-range bound such as
                    // `to_integer(x) <= 4294967295` is trivially true of the
                    // carrier but is what Integer reasoning cites, so it
                    // keeps its Integer form.
                    let (condition, truth) = if PRESERVE_INTEGER_COMPARISONS.with(|flag| flag.get())
                    {
                        (condition, true)
                    } else {
                        match crate::kernel::machine_integer::comparison::native_comparison_of_integer_observation(
                            &condition, true,
                        ) {
                            Some((ConditionTerm::Constant(_), _)) | None => (condition, true),
                            Some(native) => native,
                        }
                    };
                    result.push(SpecPropositionPath {
                        introductions: Vec::new(),
                        proposition: Proposition::ConditionIs(condition, truth),
                        facts,
                        obligations,
                    });
                }
            }
            Ok(result)
        }
        SpecProposition::AlgebraicComparison { left, equal, right } => {
            lower_spec_algebraic_comparison_at_state_in(
                scope,
                left,
                *equal,
                right,
                assumptions,
                budget,
            )
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            lower_spec_sequence_membership_at_state_in(
                scope,
                element,
                sequence,
                assumptions,
                budget,
            )
        }
        SpecProposition::SequenceComparison { left, equal, right } => {
            lower_spec_sequence_comparison_at_state_in(
                scope,
                left,
                *equal,
                right,
                assumptions,
                budget,
            )
        }
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => lower_spec_comparison_proposition_at_state_in(
            scope,
            left,
            *operator,
            right,
            assumptions,
            budget,
        ),
        SpecProposition::FloatClassification {
            expression,
            classification,
        } => lower_spec_float_classification_proposition_at_state_in(
            scope,
            expression,
            *classification,
            assumptions,
            budget,
        ),
        SpecProposition::And(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                left,
                assumptions,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
                    scope,
                    right,
                    &right_assumptions,
                    budget,
                )? {
                    if let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &left_path.facts,
                            &left_path.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                            &right_assumptions,
                        )
                    {
                        paths.push(SpecPropositionPath {
                            introductions: Vec::new(),
                            proposition: Proposition::And(
                                Box::new(left_path.proposition.clone()),
                                Box::new(right_path.proposition),
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
            }
            Ok(paths)
        }
        SpecProposition::Or(left, right) => {
            lower_spec_disjunction_at_state_in(scope, left, right, assumptions, budget)
        }
        SpecProposition::Not(body) => {
            Ok(lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                body,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| {
                // A negated condition is the condition with the other value,
                // as an execution spells the branch it did not take. Only the
                // remaining shape keeps a `Not` node an introduction can reach.
                let (proposition, introductions) = match path.proposition {
                    Proposition::ConditionIs(condition, value) => (
                        Proposition::ConditionIs(condition, !value),
                        LoweringIntroductions::new(),
                    ),
                    proposition => (
                        Proposition::Not(Box::new(proposition)),
                        vec![LoweringIntroduction::WrittenNegation],
                    ),
                };
                SpecPropositionPath {
                    proposition,
                    facts: path.facts,
                    obligations: path.obligations,
                    introductions,
                }
            })
            .collect())
        }
        SpecProposition::Implies(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                left,
                assumptions,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                )
                .assume_proposition(left_path.proposition.clone());
                for right_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
                    scope,
                    right,
                    &right_assumptions,
                    budget,
                )? {
                    let guarded_right_obligations = right_path
                        .obligations
                        .iter()
                        .cloned()
                        .map(|obligation| {
                            let antecedent = left_path.proposition.clone();
                            obligation.map_proposition(|proposition| {
                                Proposition::Implies(Box::new(antecedent), Box::new(proposition))
                            })
                        })
                        .collect::<Vec<_>>();
                    if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &left_path.facts,
                        &left_path.obligations,
                        &right_path.facts,
                        &guarded_right_obligations,
                        assumptions,
                    ) {
                        let mut introductions = vec![LoweringIntroduction::WrittenImplication];
                        introductions.extend(right_path.introductions);
                        paths.push(SpecPropositionPath {
                            proposition: Proposition::Implies(
                                Box::new(left_path.proposition.clone()),
                                Box::new(right_path.proposition),
                            ),
                            facts,
                            obligations,
                            introductions,
                        });
                    }
                }
            }
            Ok(paths)
        }
        SpecProposition::ForAllInteger {
            name,
            variable,
            body,
        } => Ok(lower_spec_proposition_at_state_with_algebraic_bindings_in(
            scope,
            body,
            assumptions,
            budget,
        )?
        .into_iter()
        .map(|path| {
            let (body, guards) =
                wrap_path_context_with_introductions(path.proposition, &path.facts, &[]);
            let mut introductions = vec![LoweringIntroduction::WrittenUniversal {
                name: name.clone(),
                variable: *variable,
                pointer: false,
                integer: true,
            }];
            introductions.extend(guards);
            introductions.extend(path.introductions);
            SpecPropositionPath {
                proposition: Proposition::ForAll {
                    var: *variable,
                    name: BinderName::written(name),
                    sort: Sort::Integer,
                    body: Box::new(body),
                },
                facts: Vec::new().into(),
                obligations: path
                    .obligations
                    .into_iter()
                    .map(|obligation| {
                        obligation.map_proposition(|proposition| Proposition::ForAll {
                            var: *variable,
                            name: BinderName::written(name),
                            sort: Sort::Integer,
                            body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                        })
                    })
                    .collect(),
                introductions,
            }
        })
        .collect()),
        SpecProposition::ForAllAlgebraic {
            name,
            variable,
            algebraic_type,
            body,
        } => Ok(lower_spec_proposition_at_state_with_algebraic_bindings_in(
            scope,
            body,
            assumptions,
            budget,
        )?
        .into_iter()
        .map(|path| {
            let (body, guards) =
                wrap_path_context_with_introductions(path.proposition, &path.facts, &[]);
            let mut introductions = vec![LoweringIntroduction::WrittenUniversal {
                name: name.clone(),
                variable: *variable,
                pointer: false,
                integer: false,
            }];
            introductions.extend(guards);
            introductions.extend(path.introductions);
            SpecPropositionPath {
                proposition: Proposition::ForAll {
                    var: *variable,
                    name: BinderName::written(name),
                    sort: Sort::Algebraic(algebraic_type.clone()),
                    body: Box::new(body),
                },
                facts: Vec::new().into(),
                obligations: path
                    .obligations
                    .into_iter()
                    .map(|obligation| {
                        obligation.map_proposition(|proposition| Proposition::ForAll {
                            var: *variable,
                            name: BinderName::written(name),
                            sort: Sort::Algebraic(algebraic_type.clone()),
                            body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                        })
                    })
                    .collect(),
                introductions,
            }
        })
        .collect()),
        SpecProposition::ForAllMachineInteger {
            name,
            variable,
            body,
            ..
        }
        | SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } => {
            let integer_type = match proposition {
                SpecProposition::ForAllMachineInteger { integer_type, .. } => *integer_type,
                _ => MachineIntegerType::Int32,
            };
            let range_facts =
                machine_quantifier_range_facts(&Sort::machine_integer(integer_type), *variable);
            let mut quantified_assumptions = assumptions.clone();
            for fact in &range_facts {
                quantified_assumptions =
                    quantified_assumptions.assume_proposition(fact.proposition().clone());
            }
            Ok(lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                body,
                &quantified_assumptions,
                budget,
            )?
            .into_iter()
            .map(|mut path| {
                let mut facts = range_facts.clone();
                facts.append(&mut path.facts);
                path.facts = facts;
                let (body, guards) =
                    wrap_path_context_with_introductions(path.proposition, &path.facts, &[]);
                let mut introductions = vec![LoweringIntroduction::WrittenUniversal {
                    name: name.clone(),
                    variable: *variable,
                    pointer: false,
                    integer: false,
                }];
                introductions.extend(guards);
                introductions.extend(path.introductions);
                SpecPropositionPath {
                    proposition: Proposition::ForAll {
                        var: *variable,
                        name: BinderName::written(name),
                        sort: Sort::machine_integer(integer_type),
                        body: Box::new(body),
                    },
                    // Path facts may mention the bound variable. They are
                    // guards on this quantified path, not facts in the
                    // surrounding context.
                    facts: Vec::new().into(),
                    obligations: path
                        .obligations
                        .into_iter()
                        .map(|obligation| {
                            obligation.map_proposition(|proposition| Proposition::ForAll {
                                var: *variable,
                                name: BinderName::written(name),
                                sort: Sort::machine_integer(integer_type),
                                body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                            })
                        })
                        .collect(),
                    introductions,
                }
            })
            .collect())
        }
        SpecProposition::ForAllPointer {
            name,
            variable,
            c_type,
            body,
        } => Ok(lower_spec_proposition_at_state_with_algebraic_bindings_in(
            scope,
            body,
            assumptions,
            budget,
        )?
        .into_iter()
        .map(|path| {
            let (body, guards) =
                wrap_path_context_with_introductions(path.proposition, &path.facts, &[]);
            let mut introductions = vec![LoweringIntroduction::WrittenUniversal {
                name: name.clone(),
                variable: *variable,
                pointer: true,
                integer: false,
            }];
            introductions.extend(guards);
            introductions.extend(path.introductions);
            SpecPropositionPath {
                proposition: Proposition::ForAll {
                    var: *variable,
                    name: BinderName::written(name),
                    sort: Sort::CPointer(*c_type),
                    body: Box::new(body),
                },
                facts: Vec::new().into(),
                obligations: path
                    .obligations
                    .into_iter()
                    .map(|obligation| {
                        obligation.map_proposition(|proposition| Proposition::ForAll {
                            var: *variable,
                            name: BinderName::written(name),
                            sort: Sort::CPointer(*c_type),
                            body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                        })
                    })
                    .collect(),
                introductions,
            }
        })
        .collect()),
        SpecProposition::ExistsInteger {
            name,
            variable,
            body,
        } => {
            let body_paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                body,
                assumptions,
                budget,
            )?;

            Ok(vec![
                existential::ScopedExistential::new(
                    name.clone(),
                    *variable,
                    Sort::Integer,
                    body_paths,
                )
                .into_checked_path(),
            ])
        }
        SpecProposition::ExistsAlgebraic {
            name,
            variable,
            algebraic_type,
            body,
        } => {
            let body_paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                body,
                assumptions,
                budget,
            )?;
            Ok(vec![
                existential::ScopedExistential::new(
                    name.clone(),
                    *variable,
                    Sort::Algebraic(algebraic_type.clone()),
                    body_paths,
                )
                .into_checked_path(),
            ])
        }
        SpecProposition::ExistsMachineInteger {
            name,
            variable,
            body,
            ..
        }
        | SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } => {
            let integer_type = match proposition {
                SpecProposition::ExistsMachineInteger { integer_type, .. } => *integer_type,
                _ => MachineIntegerType::Int32,
            };
            let range_facts =
                machine_quantifier_range_facts(&Sort::machine_integer(integer_type), *variable);
            let mut quantified_assumptions = assumptions.clone();
            for fact in &range_facts {
                quantified_assumptions =
                    quantified_assumptions.assume_proposition(fact.proposition().clone());
            }
            let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                body,
                &quantified_assumptions,
                budget,
            )?;
            for path in &mut paths {
                let mut facts = range_facts.clone();
                facts.append(&mut path.facts);
                path.facts = facts;
            }
            Ok(vec![
                existential::ScopedExistential::new(
                    name.clone(),
                    *variable,
                    Sort::machine_integer(integer_type),
                    paths,
                )
                .into_checked_path(),
            ])
        }
        SpecProposition::ExistsPointer {
            name,
            variable,
            c_type,
            body,
        } => {
            let paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                scope,
                body,
                assumptions,
                budget,
            )?;
            Ok(vec![
                existential::ScopedExistential::new(
                    name.clone(),
                    *variable,
                    Sort::CPointer(*c_type),
                    paths,
                )
                .into_checked_path(),
            ])
        }
        SpecProposition::Predicate {
            name,
            arguments,
            resource_state_dependent,
        } => lower_spec_predicate_proposition_at_state_in(
            scope,
            name,
            arguments,
            *resource_state_dependent,
            assumptions,
            budget,
        ),
        SpecProposition::ResourceSeparate { left, right } => {
            lower_spec_resource_relation_at_state_in(
                scope,
                left,
                right,
                assumptions,
                budget,
                |left, right| Proposition::CResourceSeparate {
                    left: Box::new(left),
                    right: Box::new(right),
                },
            )
        }
        SpecProposition::ResourceContains { parent, child } => {
            lower_spec_resource_relation_at_state_in(
                scope,
                parent,
                child,
                assumptions,
                budget,
                |parent, child| Proposition::CResourceContains {
                    parent: Box::new(parent),
                    child: Box::new(child),
                },
            )
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            element_width,
        } => lower_spec_memory_loadable_at_state_in(
            scope,
            memory,
            base,
            start,
            end,
            *element_width,
            assumptions,
            budget,
            true,
        ),
        SpecProposition::Defined(expression) => {
            let mut checked = SpecEvaluation::checked(budget);
            // Definedness is decided from no facts, except that a contract
            // entry's own requirement keeps assuming what its caller checked
            // about opaque pointer extents.
            let context = if assumptions.should_assume_entry_clause_extents() {
                PureFactContext::new().assume_entry_clause_extents()
            } else {
                PureFactContext::new()
            };
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                expression,
                &context,
                &mut checked,
            )?;
            let mut normal_paths = paths.into_iter().map(|path| {
                proposition_and_all(
                    path.facts
                        .into_iter()
                        // A cached read equation follows from the selected
                        // value; it is not a condition for the read to exist.
                        .filter(|fact| !fact.is_logical_read_equation())
                        .filter_map(|fact| {
                            drop_verified_load_definition_conjuncts(fact.proposition().clone())
                        })
                        .chain(path.obligations.into_iter().filter_map(|obligation| {
                            drop_verified_load_definition_conjuncts(
                                obligation.proposition().clone(),
                            )
                        }))
                        .collect(),
                )
            });
            let proposition = normal_paths.next().map_or_else(
                || Proposition::ConditionIs(ConditionTerm::Constant(false), true),
                |first| {
                    normal_paths.fold(first, |left, right| {
                        Proposition::Or(Box::new(left), Box::new(right))
                    })
                },
            );
            Ok(vec![SpecPropositionPath {
                introductions: Vec::new(),
                proposition,
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }])
        }
    }
}

/// Combines alternative evaluation paths without moving an existential across
/// the disjunction. Each branch may carry a different definedness guard, but
/// all branches still describe the same witness.
fn proposition_or_all(mut propositions: Vec<Proposition>) -> Proposition {
    if propositions.is_empty() {
        return Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    }
    while propositions.len() > 1 {
        let mut next = Vec::with_capacity(propositions.len().div_ceil(2));
        let mut pairs = propositions.into_iter();
        while let Some(left) = pairs.next() {
            next.push(match pairs.next() {
                Some(right) => Proposition::Or(Box::new(left), Box::new(right)),
                None => left,
            });
        }
        propositions = next;
    }
    propositions.pop().expect("nonempty disjunction level")
}

fn retain_required_integer_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
) {
    if assumptions.proves_exact(&proposition) {
        return;
    }
    // Keep the original evaluation obligations and their diagnostic context.
    // Appending the mandatory condition avoids scanning unrelated path history.
    obligations.push(ProofObligation::verification_condition(proposition));
}

fn evaluate_spec_integer_expression_paths_in(
    scope: SpecScope<'_>,
    expression: &SpecIntegerExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    budget.consume_expression_step()?;
    match expression {
        SpecIntegerExpression::ResourceField(projection) => {
            let snapshot = if projection.at_entry {
                loop_entry_state.ok_or(ExecutionLimit::Paths)?
            } else {
                state
            };
            let Some(AlgebraicValue::Integer(value)) = snapshot
                .resource_instance_at_path(projection.identity, &projection.children)
                .and_then(|instance| instance.fields().get(projection.field_index))
            else {
                return Err(ExecutionLimit::ResourceFieldInstanceUnavailable);
            };
            Ok(vec![SpecIntegerPath {
                value: value.clone(),
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }])
        }
        SpecIntegerExpression::Term(term) => {
            let term = budget.bound_integer_term(term)?;
            if crate::instrumentation::numeric_operation_work_exceeded(integer_term_bits(&term)) {
                return Err(ExecutionLimit::Deadline);
            }
            Ok(vec![SpecIntegerPath {
                value: term,
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }])
        }
        SpecIntegerExpression::PureFunctionApplication { name, arguments } => {
            evaluate_spec_integer_pure_function_application_paths_in(
                scope,
                name,
                arguments,
                assumptions,
                budget,
            )
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            evaluate_spec_integer_algebraic_match_paths_in(
                scope,
                scrutinee,
                arms,
                assumptions,
                budget,
            )
        }
        SpecIntegerExpression::If {
            condition,
            then_branch,
            else_branch,
        } => evaluate_spec_integer_if_paths_in(
            scope,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        ),
        SpecIntegerExpression::FromMachine(machine) => {
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                machine,
                assumptions,
                budget,
            )?;
            // Preserve the complete domain of the C expression, including the
            // normal-path guards whose complementary paths had undefined behavior.
            // This is a mandatory condition, not an assumption supplied by the
            // conversion's own successful evaluation path.
            let domain = paths
                .iter()
                .map(|path| {
                    proposition_and_all(
                        path.facts
                            .iter()
                            // Certified consequences describe the result;
                            // only unproved path guards restrict its domain.
                            .filter(|fact| !fact.is_certified())
                            .map(|fact| fact.proposition().clone())
                            .chain(
                                path.obligations
                                    .iter()
                                    .map(|obligation| obligation.proposition().clone()),
                            )
                            .collect(),
                    )
                })
                .reduce(|left, right| Proposition::Or(Box::new(left), Box::new(right)))
                .unwrap_or(Proposition::ConditionIs(
                    ConditionTerm::Constant(false),
                    true,
                ));
            paths
                .into_iter()
                .map(|path| {
                    let ty = MachineIntegerType::from_c_type(path.value.c_type())
                        .ok_or(ExecutionLimit::Paths)?;
                    let bits = c_value_bitvector_term(&path.value).ok_or(ExecutionLimit::Paths)?;
                    let value = IntegerTerm::from_machine(ty, bits).ok_or(ExecutionLimit::Paths)?;
                    let mut obligations = path.obligations;
                    retain_required_integer_obligation(
                        &mut obligations,
                        assumptions,
                        domain.clone(),
                    );
                    Ok(SpecIntegerPath {
                        value,
                        facts: path.facts,
                        obligations,
                    })
                })
                .collect()
        }
        SpecIntegerExpression::Negate(inner) => {
            evaluate_spec_integer_expression_paths_in(scope, inner, assumptions, budget).and_then(
                |paths| {
                    let mut result = Vec::new();
                    for mut path in paths {
                        if crate::instrumentation::numeric_operation_work_exceeded(
                            integer_term_bits(&path.value),
                        ) {
                            return Err(ExecutionLimit::Deadline);
                        }
                        path.value = IntegerTerm::negate(path.value);
                        result.push(path);
                    }
                    Ok(result)
                },
            )
        }
        SpecIntegerExpression::Add(left, right) => evaluate_integer_binary_paths_in(
            scope,
            left,
            right,
            assumptions,
            budget,
            IntegerBinaryOperation::Add,
        ),
        SpecIntegerExpression::Subtract(left, right) => evaluate_integer_binary_paths_in(
            scope,
            left,
            right,
            assumptions,
            budget,
            IntegerBinaryOperation::Subtract,
        ),
        SpecIntegerExpression::Multiply(left, right) => evaluate_integer_binary_paths_in(
            scope,
            left,
            right,
            assumptions,
            budget,
            IntegerBinaryOperation::Multiply,
        ),
        SpecIntegerExpression::TruncatingQuotient(left, right) => evaluate_integer_binary_paths_in(
            scope,
            left,
            right,
            assumptions,
            budget,
            IntegerBinaryOperation::TruncatingQuotient,
        ),
        SpecIntegerExpression::TruncatingRemainder(left, right) => {
            evaluate_integer_binary_paths_in(
                scope,
                left,
                right,
                assumptions,
                budget,
                IntegerBinaryOperation::TruncatingRemainder,
            )
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let index_paths =
                evaluate_spec_integer_range_fold_indices_in(scope, index, assumptions, budget)?;
            let mut result = Vec::new();
            for (index, index_facts, index_obligations) in index_paths {
                let index_assumptions =
                    assumptions_with_path_context(assumptions, &index_facts, &index_obligations);
                for initial_path in evaluate_spec_integer_expression_paths_in(
                    scope,
                    initial,
                    &index_assumptions,
                    budget,
                )? {
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &index_facts,
                            &index_obligations,
                            &initial_path.facts,
                            &initial_path.obligations,
                            assumptions,
                            &index_assumptions,
                        )
                    else {
                        continue;
                    };
                    let body_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    let (_, body_guard) = integer_range_fold_item_domain(&index, *item);
                    if integer_range_fold_index_is_empty(&index) {
                        // Keep one symbolic body value for fold capture and
                        // theorem shape, but do not let a concrete empty
                        // range make an unavailable load a live obligation.
                        // Symbolic-load mode preserves the load term while
                        // the half-open guard makes every body obligation
                        // vacuous.
                        let empty_body_assumptions =
                            body_assumptions.assume_proposition(body_guard.clone());
                        let body_paths = budget.with_integer_bindings(
                            &[
                                Some(*accumulator),
                                matches!(index, IntegerRangeFoldIndex::Integer { .. })
                                    .then_some(*item),
                            ],
                            &[
                                AlgebraicValue::Integer(IntegerTerm::var(*accumulator)),
                                AlgebraicValue::Integer(IntegerTerm::var(*item)),
                            ],
                            |budget| {
                                evaluate_spec_integer_expression_paths_in(
                                    scope,
                                    body,
                                    &empty_body_assumptions,
                                    budget,
                                )
                            },
                        )?;
                        // The fold of an empty range is its initial value
                        // whatever the body is, so the body's facts never
                        // decide the spelling.
                        let body_value = match body_paths.as_slice() {
                            [body_path] => Some(body_path.value.clone()),
                            _ => None,
                        };
                        if let Some(body_value) = body_value {
                            result.push(SpecIntegerPath {
                                value: IntegerTerm::range_fold(
                                    index.clone(),
                                    initial_path.value.clone(),
                                    *accumulator,
                                    *item,
                                    body_value,
                                ),
                                facts,
                                obligations,
                            });
                        } else {
                            result.push(SpecIntegerPath {
                                value: initial_path.value.clone(),
                                facts,
                                obligations,
                            });
                        }
                        continue;
                    }
                    let body_assumptions = body_assumptions.assume_proposition(body_guard);
                    let body_paths = budget.with_integer_bindings(
                        &[
                            Some(*accumulator),
                            matches!(index, IntegerRangeFoldIndex::Integer { .. }).then_some(*item),
                        ],
                        &[
                            AlgebraicValue::Integer(IntegerTerm::var(*accumulator)),
                            AlgebraicValue::Integer(IntegerTerm::var(*item)),
                        ],
                        |budget| {
                            evaluate_spec_integer_expression_paths_in(
                                scope,
                                body,
                                &body_assumptions,
                                budget,
                            )
                        },
                    )?;
                    // A fold body is one symbolic iteration under its two
                    // binders.  Case splits are not universally valid for
                    // every item, so retain only a single non-branching path;
                    // unresolved alternatives are rejected rather than
                    // exporting one branch's assumptions to the fold.
                    let [body_path] = body_paths.as_slice() else {
                        budget.record_dropped_fold_body(body_paths.len(), None, *item);
                        continue;
                    };
                    {
                        // The fold body is under its accumulator/item binders.
                        // Its branch facts and definedness obligations therefore
                        // cannot be exported as ambient facts for the fold
                        // result.  Load-defining facts are represented by the
                        // registered snapshot load itself and may be dropped;
                        // derived read equations also stay local; all other body facts
                        // must already be ambient.
                        if let Some(unavailable) = body_path.facts.iter().find(|fact| {
                            !fact.is_logical_read_equation()
                                && !assumptions.proves_exact(fact.proposition())
                                && !is_verified_load_variable_defining_fact(fact.proposition())
                        }) {
                            budget.record_dropped_fold_body(
                                1,
                                Some(unavailable.proposition().clone()),
                                *item,
                            );
                            continue;
                        }
                        let body_obligations = body_path
                            .obligations
                            .iter()
                            .filter_map(|obligation| {
                                let proposition = drop_verified_load_definition_conjuncts(
                                    obligation.proposition().clone(),
                                )?;
                                let scoped = integer_range_fold_body_obligation(
                                    proposition,
                                    &index,
                                    *accumulator,
                                    *item,
                                );
                                Some(obligation.clone().map_proposition(|_| scoped))
                            })
                            .collect::<Vec<_>>();
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &facts,
                            &obligations,
                            &[],
                            &body_obligations,
                            assumptions,
                        ) else {
                            continue;
                        };
                        result.push(SpecIntegerPath {
                            value: IntegerTerm::range_fold(
                                index.clone(),
                                initial_path.value.clone(),
                                *accumulator,
                                *item,
                                body_path.value.clone(),
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
            }
            Ok(result)
        }
    }
}

/// A load definition is trusted only when its descriptor is the exact
/// registered snapshot and pointer for the reserved variable. Comparing
/// interned snapshots uses their O(1) identity equality; arbitrary memory
/// contents are never traversed here.
pub(crate) fn is_verified_load_variable_defining_fact(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = proposition
    else {
        return false;
    };
    let (Bitvector32Term::Variable(variable), load @ Bitvector32Term::MemoryLoad(_, _, _)) =
        (left.as_ref(), right.as_ref())
    else {
        return false;
    };
    if !crate::kernel::is_load_variable(variable) {
        return false;
    }
    // The descriptor is the registered load exactly, kind included: a
    // definition that names another kind of read at the address is not one.
    crate::kernel::eval::registered_load_term_for_variable(variable).as_ref() == Some(load)
}

/// Removes only kernel-certified load definitions from a conjunction. The
/// defining equation is metadata for a registered load; its exact descriptor
/// has already been checked against the registry above. Other equalities,
/// including a tampered load definition, remain obligations.
fn drop_verified_load_definition_conjuncts(proposition: Proposition) -> Option<Proposition> {
    if is_verified_load_variable_defining_fact(&proposition) {
        return None;
    }
    match proposition {
        Proposition::And(left, right) => {
            let left = drop_verified_load_definition_conjuncts(*left);
            let right = drop_verified_load_definition_conjuncts(*right);
            match (left, right) {
                (Some(left), Some(right)) => {
                    Some(Proposition::And(Box::new(left), Box::new(right)))
                }
                (Some(proposition), None) | (None, Some(proposition)) => Some(proposition),
                (None, None) => None,
            }
        }
        proposition => Some(proposition),
    }
}

fn verified_load_obligation_without_definition(
    obligation: &ProofObligation,
) -> Option<ProofObligation> {
    let proposition = drop_verified_load_definition_conjuncts(obligation.proposition().clone())?;
    Some(obligation.clone().map_proposition(|_| proposition))
}

/// Build one existential branch while removing only exact registered
/// load definitions. The path facts and obligations can both contain the
/// same certified equation; loadability, range guards, and all user written
/// conditions remain in the conjunction.
#[cfg(test)]
pub(super) fn existential_body_branch(path: &SpecPropositionPath) -> Proposition {
    existential::ScopedExistentialBranch::from_path(path.clone()).into_checked_body()
}

/// Turn one non-branching body requirement into a requirement for every
/// iteration in the fold's half-open range.  The accumulator is quantified
/// only when the requirement actually contains a mathematical Integer with
/// that identity; the item is always quantified so an empty or reversed
/// range makes the body requirement vacuous.
fn integer_range_fold_body_obligation(
    proposition: Proposition,
    index: &IntegerRangeFoldIndex,
    accumulator: Variable,
    item: Variable,
) -> Proposition {
    let (item_sort, guard) = integer_range_fold_item_domain(index, item);
    let body = Proposition::Implies(Box::new(guard), Box::new(proposition.clone()));
    let body = Proposition::ForAll {
        name: Default::default(),
        var: item,
        sort: item_sort,
        body: Box::new(body),
    };
    if proposition_mentions_integer_variable(&proposition, accumulator) {
        Proposition::ForAll {
            name: Default::default(),
            var: accumulator,
            sort: Sort::Integer,
            body: Box::new(body),
        }
    } else {
        body
    }
}

fn integer_range_fold_item_domain(
    index: &IntegerRangeFoldIndex,
    item: Variable,
) -> (Sort, Proposition) {
    let (item_sort, guard) = match index {
        IntegerRangeFoldIndex::Int32 { start, end } => {
            let item_term = Bitvector32Term::Variable(item);
            let guard = Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(item_term.clone(), start.value().clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(item_term, end.value().clone()),
                    true,
                )),
            );
            (Sort::CInt32, guard)
        }
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            let item_term = Bitvector32Term::Variable(item);
            let guard = Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::uint64_less_equal(start.value().clone(), item_term.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::uint64_less_than(item_term, end.value().clone()),
                    true,
                )),
            );
            (Sort::CMachineInteger(MachineIntegerType::UInt64), guard)
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            let item_term = IntegerTerm::Variable(item);
            let guard = Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_greater_equal(item_term.clone(), start.as_ref().clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_less_than(item_term, end.as_ref().clone()),
                    true,
                )),
            );
            (Sort::Integer, guard)
        }
    };

    (item_sort, guard)
}

fn integer_range_fold_index_is_empty(index: &IntegerRangeFoldIndex) -> bool {
    match index {
        IntegerRangeFoldIndex::Int32 { start, end } => {
            let Some(start) = start.value().as_const().map(|value| value as i32) else {
                return false;
            };
            let Some(end) = end.value().as_const().map(|value| value as i32) else {
                return false;
            };
            start >= end
        }
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            match (
                start.value().uint64_as_const(),
                end.value().uint64_as_const(),
            ) {
                (Some(start), Some(end)) => start >= end,
                _ => false,
            }
        }
        IntegerRangeFoldIndex::Integer { start, end } => match (start.as_const(), end.as_const()) {
            (Some(start), Some(end)) => start >= end,
            _ => false,
        },
    }
}

fn integer_carrier_in_pointer(pointer: &Pointer, variable: Variable) -> bool {
    // Like an opaque algebraic application, a pointer call can carry the
    // accumulator through its arguments, and a loaded pointer through its
    // defining read's address. Retain the scope without expanding a shared
    // application or registry DAG once for every fold obligation.
    matches!(
        pointer.block,
        PointerBlock::PureFunctionApplication(_) | PointerBlock::LoadedPointer(_)
    ) || integer_carrier_in_pointer_offset(&pointer.offset, variable)
}

fn integer_carrier_in_pointer_offset(offset: &PointerOffsetTerm, variable: Variable) -> bool {
    match offset {
        PointerOffsetTerm::Constant(_) => false,
        PointerOffsetTerm::Variable(load) => {
            integer_carrier_in_bitvector(&Bitvector32Term::Variable(*load), variable)
        }
        PointerOffsetTerm::Add(left, right) => {
            integer_carrier_in_pointer_offset(left, variable)
                || integer_carrier_in_pointer_offset(right, variable)
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            integer_carrier_in_bitvector(value, variable)
        }
    }
}

/// A registered load may use another registered load directly as an offset.
/// `scaled_values` intentionally reports only scaled bitvector payloads, so
/// it cannot see `Add(..., Variable(load))` or a direct `Variable(load)` leaf.
/// Keep this query conservative for those selected pointer leaves: retaining
/// the accumulator quantifier is sound, while expanding the registry here
/// would duplicate the checked carrier collector and reopen its DAG.
fn pointer_offset_contains_registered_load(offset: &PointerOffsetTerm) -> bool {
    match offset {
        PointerOffsetTerm::Constant(_) => false,
        PointerOffsetTerm::Variable(variable) => crate::kernel::is_load_variable(variable),
        PointerOffsetTerm::Add(left, right) => {
            pointer_offset_contains_registered_load(left)
                || pointer_offset_contains_registered_load(right)
        }
        PointerOffsetTerm::Int32Scaled { .. } | PointerOffsetTerm::Int64Scaled { .. } => false,
    }
}

/// Use the checked carrier collector for ordinary machine payloads, then
/// inspect only a registered load's selected pointer.  The memory snapshot is
/// deliberately never traversed.  Unknown registry entries are treated as a
/// dependency so a missing pointer cannot drop an accumulator quantifier.
fn integer_carrier_in_bitvector(term: &Bitvector32Term, variable: Variable) -> bool {
    let mut variables = BTreeSet::new();
    collect_bitvector_integer_variables(term, &mut variables);
    if variables.contains(&variable) {
        return true;
    }
    let Bitvector32Term::Variable(load) = term else {
        // The shared collector covers known Integer-to-machine payloads.  A
        // composite machine expression can still hide a registered load
        // whose pointer carries an Integer, so retain the scope rather than
        // returning an unsound negative for that opaque case.
        return !matches!(
            term,
            Bitvector32Term::Constant(_)
                | Bitvector32Term::UInt32Constant(_)
                | Bitvector32Term::Int64Constant(_)
                | Bitvector32Term::UInt64Constant(_)
                | Bitvector32Term::MachineIntegerConstant(_)
        );
    };
    if !crate::kernel::is_load_variable(load) {
        return false;
    }
    let Some((memory, pointer)) = crate::kernel::eval::registered_load_for_variable(load) else {
        return true;
    };
    if pointer_offset_contains_registered_load(&pointer.offset) {
        return true;
    }
    if pointer
        .offset
        .scaled_values()
        .iter()
        .any(|value| match value {
            Bitvector32Term::Variable(variable) => crate::kernel::is_load_variable(variable),
            Bitvector32Term::Constant(_)
            | Bitvector32Term::UInt32Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::MachineIntegerConstant(_) => false,
            _ => true,
        })
    {
        // A nested registered load is an opaque pointer payload here.  Its
        // own selected address may carry the accumulator, so keep the scope
        // conservatively without expanding the registry DAG.
        return true;
    }
    let Some(kind) = crate::kernel::eval::registered_load_kind_for_variable(load) else {
        return true;
    };
    let selected_load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer), kind);
    let mut pointer_variables = BTreeSet::new();
    collect_bitvector_integer_variables(&selected_load, &mut pointer_variables);
    if pointer_variables.contains(&variable) {
        true
    } else {
        // The shared collector intentionally does not expand registered
        // variables nested below an arbitrary machine expression.  Keep
        // those opaque payloads sound by retaining the accumulator scope;
        // direct registered roots above still get the precise pointer query.
        false
    }
}

fn integer_carrier_in_c_value(value: &CValue, variable: Variable) -> bool {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Pointer(pointer) => integer_carrier_in_pointer(pointer, variable),
        CValue::Parameter(term) => integer_carrier_in_algebraic(term, variable),
        CValue::Void => false,
        CValue::Int8(term) => integer_carrier_in_bitvector(term, variable),
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Int128(term)
        | CValue::UInt128(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => integer_carrier_in_bitvector(term, variable),
    }
}

fn integer_carrier_in_integer(term: &IntegerTerm, variable: Variable) -> bool {
    let mut variables = BTreeSet::new();
    collect_integer_carrier_variables(term, &mut variables);
    if variables.contains(&variable) {
        return true;
    }
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => false,
        IntegerTerm::Machine(machine) => integer_carrier_in_bitvector(machine.value(), variable),
        // A composite Integer payload may contain a registered machine load
        // hidden below the shared carrier collector.  Preserve soundness
        // conservatively rather than recursively duplicating the full term
        // language here.
        IntegerTerm::Negate(_)
        | crate::kernel::binary_integer_term!(_, _)
        | IntegerTerm::PureFunctionApplication(_)
        | IntegerTerm::AlgebraicMatch { .. }
        | IntegerTerm::If { .. }
        | IntegerTerm::RangeFold { .. } => true,
    }
}

fn integer_carrier_in_algebraic(value: &AlgebraicTerm, _variable: Variable) -> bool {
    match &value.node {
        AlgebraicTermNode::Variable(_) => false,
        // Algebraic values are immutable DAG payloads and may contain
        // registered loads through constructor fields, match bindings, or
        // pure-function arguments.  A full recursive scan here would repeat
        // shared branches for every fold obligation.  Keep the dependency
        // sound with one conservative answer for every non-atomic payload.
        AlgebraicTermNode::Constructor { .. }
        | AlgebraicTermNode::Match { .. }
        | AlgebraicTermNode::If { .. }
        | AlgebraicTermNode::MemoryLoad { .. }
        | AlgebraicTermNode::PureFunctionApplication { .. } => true,
    }
}

fn sequence_contains_integer_variable(sequence: &SequenceTerm, variable: Variable) -> bool {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => values
            .iter()
            .any(|value| integer_carrier_in_c_value(value, variable)),
        // Sequence concatenations are shared DAGs.  Their elements can carry
        // a registered pointer load, so preserving the accumulator scope for
        // the opaque composite is the bounded, sound choice.
        SequenceTermNode::Concat(_, _) => true,
    }
}

/// The fold evaluator only needs this typed query for the accumulator.  The
/// general proposition collector deliberately combines carriers for source
/// freshness, which would confuse an Integer accumulator with an Int32 item
/// carrying the same numeric identity.  Keep the query narrow and
/// conservative for unsupported proposition payloads: an uncertain payload
/// causes the extra Integer quantifier, never an under-quantified obligation.
fn proposition_mentions_integer_variable(proposition: &Proposition, variable: Variable) -> bool {
    fn term_contains(term: &Term, variable: Variable) -> bool {
        match term {
            Term::Integer(term) => integer_carrier_in_integer(term, variable),
            Term::Bitvector32(term) => integer_carrier_in_bitvector(term, variable),
            Term::Condition(condition) => condition_contains(condition, variable),
            Term::CValue(value) => integer_carrier_in_c_value(value, variable),
            Term::Sequence(sequence) => sequence_contains_integer_variable(sequence, variable),
            Term::PointerOffset(offset) => integer_carrier_in_pointer_offset(offset, variable),
            Term::Algebraic(value) => integer_carrier_in_algebraic(value, variable),
            Term::CExpressionOutcome(CExpressionOutcome::Value(value)) => {
                integer_carrier_in_c_value(value, variable)
            }
            // A state or an execution outcome may carry a mathematical
            // machine conversion in a nested local.  Keep this conservative
            // rather than silently dropping the accumulator scope; memory
            // snapshots themselves remain opaque below.
            Term::CStatementOutcome(_) | Term::CFunctionOutcome(_) | Term::CState(_) => true,
            Term::CExpressionOutcome(_) | Term::CMemory(_) => false,
        }
    }

    fn condition_contains(condition: &ConditionTerm, variable: Variable) -> bool {
        match condition {
            ConditionTerm::PointerValueEqual(left, right) => left
                .pointers()
                .chain(right.pointers())
                .any(|p| integer_carrier_in_pointer(p, variable)),

            crate::kernel::integer_comparison_condition!(left, right) => {
                integer_carrier_in_integer(left.as_ref(), variable)
                    || integer_carrier_in_integer(right.as_ref(), variable)
            }
            crate::kernel::binary_bitvector_condition!(left, right) => {
                integer_carrier_in_bitvector(left, variable)
                    || integer_carrier_in_bitvector(right, variable)
            }
            ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
            ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
                let mut found = false;
                float_condition.for_each_bitvector_term(|term| {
                    found |= integer_carrier_in_bitvector(term, variable);
                });
                found
            }
            ConditionTerm::AlgebraicEqual(left, right) => {
                integer_carrier_in_algebraic(left, variable)
                    || integer_carrier_in_algebraic(right, variable)
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                integer_carrier_in_pointer_offset(left, variable)
                    || integer_carrier_in_pointer_offset(right, variable)
            }
            ConditionTerm::PointerEqual(left, right) => {
                integer_carrier_in_pointer(left, variable)
                    || integer_carrier_in_pointer(right, variable)
            }
            // An application's arguments or a read's address may carry
            // one; keep the scope, as for an opaque payload.
            ConditionTerm::BoolApplication(_) | ConditionTerm::BoolLoad(..) => true,
            ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => condition
                .bool_children()
                .any(|child| condition_contains(child, variable)),
        }
    }

    match proposition {
        Proposition::Equal(left, right) => {
            term_contains(left, variable) || term_contains(right, variable)
        }
        Proposition::ConditionIs(condition, _) => condition_contains(condition, variable),
        Proposition::Predicate { arguments, .. } => {
            arguments.iter().any(|term| term_contains(term, variable))
        }
        Proposition::CMemoryLoads {
            pointer, outcome, ..
        } => {
            integer_carrier_in_pointer(pointer, variable)
                || matches!(outcome, CExpressionOutcome::Value(value) if integer_carrier_in_c_value(value, variable))
        }
        Proposition::CMemoryCanStore { pointer, .. } => {
            integer_carrier_in_pointer(pointer, variable)
        }
        Proposition::CMemoryReadDefined { pointer, .. } => {
            integer_carrier_in_pointer(pointer, variable)
        }
        Proposition::CMemoryLoadable { base, bytes, .. } => {
            integer_carrier_in_bitvector(bytes, variable)
                || integer_carrier_in_pointer(base, variable)
        }
        Proposition::CMemoryMutatesOnly { writes, .. } => writes
            .iter()
            .any(|(pointer, _)| integer_carrier_in_pointer(pointer, variable)),
        Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
            mutable_ranges.iter().any(|range| {
                integer_carrier_in_bitvector(range.bound_terms().0, variable)
                    || integer_carrier_in_bitvector(range.bound_terms().1, variable)
                    || integer_carrier_in_pointer(&range.base, variable)
            })
        }
        Proposition::CHeapAllocationFreed {
            allocation_base,
            bytes,
            ..
        } => {
            integer_carrier_in_bitvector(bytes, variable)
                || integer_carrier_in_pointer(allocation_base, variable)
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_mentions_integer_variable(left, variable)
                || proposition_mentions_integer_variable(right, variable)
        }
        Proposition::Not(body) => proposition_mentions_integer_variable(body, variable),
        Proposition::ForAll {
            var, sort, body, ..
        }
        | Proposition::Exists {
            var, sort, body, ..
        } => {
            (*var != variable || *sort != Sort::Integer)
                && proposition_mentions_integer_variable(body, variable)
        }
        // These proposition forms can contain machine payloads in their C
        // state/outcome terms.  A conservative answer prevents dropping a
        // needed accumulator scope, while CMemory remains intentionally
        // opaque in the explicit forms above.
        _ => true,
    }
}

fn evaluate_spec_integer_range_fold_indices_in(
    scope: SpecScope<'_>,
    index: &SpecIntegerRangeFoldIndex,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<(IntegerRangeFoldIndex, ExecutionFacts, Vec<ProofObligation>)>> {
    match index {
        SpecIntegerRangeFoldIndex::Int32 { start, end }
        | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
            let unsigned64 = matches!(index, SpecIntegerRangeFoldIndex::UInt64 { .. });
            let mut result = Vec::new();
            for start_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                start,
                assumptions,
                budget,
            )? {
                let start_assumptions = assumptions_with_path_context(
                    assumptions,
                    &start_path.facts,
                    &start_path.obligations,
                );
                for end_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    scope,
                    end,
                    &start_assumptions,
                    budget,
                )? {
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &start_path.facts,
                            &start_path.obligations,
                            &end_path.facts,
                            &end_path.obligations,
                            assumptions,
                            &start_assumptions,
                        )
                    else {
                        continue;
                    };
                    // Each kind takes endpoints of its own type only.
                    let index = match (start_path.value.clone(), end_path.value, unsigned64) {
                        (CValue::Int32(start), CValue::Int32(end), false) => {
                            IntegerRangeFoldIndex::Int32 {
                                start: SharedIntegerRangeEndpoint::intern(start),
                                end: SharedIntegerRangeEndpoint::intern(end),
                            }
                        }
                        (CValue::UInt64(start), CValue::UInt64(end), true) => {
                            IntegerRangeFoldIndex::UInt64 {
                                start: SharedIntegerRangeEndpoint::intern(start),
                                end: SharedIntegerRangeEndpoint::intern(end),
                            }
                        }
                        _ => continue,
                    };
                    result.push((index, facts, obligations));
                }
            }
            Ok(result)
        }
        SpecIntegerRangeFoldIndex::Integer { start, end } => {
            let mut result = Vec::new();
            for start_path in
                evaluate_spec_integer_expression_paths_in(scope, start, assumptions, budget)?
            {
                let start_assumptions = assumptions_with_path_context(
                    assumptions,
                    &start_path.facts,
                    &start_path.obligations,
                );
                for end_path in evaluate_spec_integer_expression_paths_in(
                    scope,
                    end,
                    &start_assumptions,
                    budget,
                )? {
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &start_path.facts,
                            &start_path.obligations,
                            &end_path.facts,
                            &end_path.obligations,
                            assumptions,
                            &start_assumptions,
                        )
                    else {
                        continue;
                    };
                    result.push((
                        IntegerRangeFoldIndex::Integer {
                            start: start_path.value.clone().into(),
                            end: end_path.value.into(),
                        },
                        facts,
                        obligations,
                    ));
                }
            }
            Ok(result)
        }
    }
}

fn evaluate_spec_integer_algebraic_match_paths_in(
    scope: SpecScope<'_>,
    scrutinee: &SpecAlgebraicExpression,
    arms: &[SpecIntegerMatchArm],
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    let state = scope.state;
    let algebraic_bindings = scope.algebraic_bindings;
    let scrutinee_paths =
        evaluate_spec_algebraic_at_state_with_bindings_in(scope, scrutinee, assumptions, budget)?;
    let mut result = Vec::new();
    for scrutinee_path in scrutinee_paths {
        let mut facts = scrutinee_path.facts;
        let mut obligations = scrutinee_path.obligations;
        if arms.len() != scrutinee_path.value.algebraic_type.variants.len()
            || scrutinee_path
                .value
                .algebraic_type
                .variants
                .iter()
                .any(|schema| arms.iter().filter(|arm| arm.variant == schema.name).count() != 1)
            || arms.iter().any(|arm| {
                scrutinee_path
                    .value
                    .algebraic_type
                    .variants
                    .iter()
                    .find(|schema| schema.name == arm.variant)
                    .is_none_or(|schema| !spec_integer_match_arm_is_well_formed(schema, arm))
            })
        {
            return Err(ExecutionLimit::Paths);
        }
        let mut lowered_arms = Vec::with_capacity(arms.len());
        for arm in arms {
            let schema = scrutinee_path
                .value
                .algebraic_type
                .variants
                .iter()
                .find(|schema| schema.name == arm.variant)
                .ok_or(ExecutionLimit::Paths)?;
            let bindings = symbolic_algebraic_match_binders_in(
                &scrutinee_path.value.algebraic_type,
                schema,
                budget,
            )?;
            let mut body_state = state.clone();
            let mut body_algebraic_bindings = algebraic_bindings.clone();
            for (binding, value) in arm.bindings.iter().zip(bindings.clone()) {
                match value {
                    AlgebraicValue::C(value) => body_state.locals.set(binding.clone(), value),
                    AlgebraicValue::Algebraic(value) => {
                        body_algebraic_bindings.insert(binding.clone(), value);
                    }
                    AlgebraicValue::Integer(_) => {}
                }
            }
            let body_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            let mut body_paths =
                budget.with_integer_bindings(&arm.binding_variables, &bindings, |budget| {
                    evaluate_spec_integer_expression_paths_in(
                        SpecScope {
                            state: &body_state,
                            algebraic_bindings: &body_algebraic_bindings,
                            ..scope
                        },
                        &arm.body,
                        &body_assumptions,
                        budget,
                    )
                })?;
            let Some(body_path) = body_paths.pop() else {
                return Err(ExecutionLimit::Paths);
            };
            if !body_paths.is_empty()
                || body_path.facts.has_path_conditions()
                || !body_path.obligations.is_empty()
            {
                return Err(ExecutionLimit::Paths);
            }
            let mut integer_replacements = BTreeMap::new();
            for ((surface, binding_type), symbolic) in arm
                .binding_variables
                .iter()
                .zip(&arm.binding_types)
                .zip(&bindings)
            {
                if binding_type != &AlgebraicValueType::Integer {
                    continue;
                }
                let Some(surface) = surface else {
                    return Err(ExecutionLimit::Paths);
                };
                let AlgebraicValue::Integer(IntegerTerm::Variable(symbolic)) = symbolic else {
                    return Err(ExecutionLimit::Paths);
                };
                if integer_replacements
                    .insert(*surface, IntegerTerm::var(*symbolic))
                    .is_some()
                {
                    return Err(ExecutionLimit::Paths);
                }
            }
            let body = rewrite_integer_match_typed_body(
                body_path.value,
                &BTreeMap::new(),
                &integer_replacements,
                &BTreeMap::new(),
            )
            .ok_or(ExecutionLimit::Paths)?;
            lowered_arms.push(AlgebraicIntegerMatchArm {
                binding_names: crate::kernel::BindingNames::written(&arm.bindings),
                variant: arm.variant.clone(),
                bindings: bindings.clone(),
                body: body.into(),
            });
        }
        let value = match &scrutinee_path.value.node {
            AlgebraicTermNode::Constructor { variant, fields } => lowered_arms
                .iter()
                .find(|arm| arm.variant == *variant)
                .and_then(|arm| {
                    if arm.bindings.len() != fields.len() {
                        return None;
                    }
                    let body = rewrite_integer_match_typed_fields(
                        arm.body.as_ref().clone(),
                        &arm.bindings,
                        fields,
                    )?;
                    Some(body)
                })
                .ok_or(ExecutionLimit::Paths)?,
            _ => IntegerTerm::AlgebraicMatch {
                scrutinee: Box::new(scrutinee_path.value),
                arms: lowered_arms,
            },
        };
        result.push(SpecIntegerPath {
            value,
            facts: std::mem::take(&mut facts),
            obligations: std::mem::take(&mut obligations),
        });
    }
    Ok(result)
}

fn spec_integer_match_arm_is_well_formed(
    schema: &AlgebraicVariantType,
    arm: &SpecIntegerMatchArm,
) -> bool {
    if schema.fields != arm.binding_types
        || schema.fields.len() != arm.bindings.len()
        || arm.binding_variables.len() != arm.bindings.len()
    {
        return false;
    }
    let mut names = BTreeSet::new();
    let mut integer_variables = BTreeSet::new();
    arm.bindings.iter().all(|name| names.insert(name))
        && arm
            .binding_variables
            .iter()
            .zip(&arm.binding_types)
            .all(|(variable, binding_type)| {
                if binding_type == &AlgebraicValueType::Integer {
                    variable.is_some_and(|variable| integer_variables.insert(variable))
                } else {
                    variable.is_none()
                }
            })
}

#[cfg(test)]
mod integer_match_metadata_tests;

fn rewrite_integer_match_typed_body(
    body: IntegerTerm,
    c_replacements: &BTreeMap<Variable, crate::kernel::proof::term_rewrite::TypedCReplacement>,
    integer_replacements: &BTreeMap<Variable, IntegerTerm>,
    algebraic_replacements: &BTreeMap<Variable, AlgebraicTerm>,
) -> Option<IntegerTerm> {
    let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::for_typed_variables(
        c_replacements,
        integer_replacements,
        algebraic_replacements,
    );
    let rewritten = rewrite.term(&Term::Integer(body));
    if rewrite.refusal().is_some() {
        return None;
    }
    let Term::Integer(value) = rewritten else {
        return None;
    };
    Some(value)
}

/// Eliminates an arm's binders by substituting the selected constructor's
/// fields into the arm body.
///
/// The body is the arm body alone, lifted out of the `Match` that bound it,
/// so nothing in the term itself distinguishes a bound occurrence of a binder
/// from a free variable that happens to carry the same identity. The check
/// that makes the substitution capture-correct is therefore on the binders:
/// every one has to be a match-binder identity
/// ([`ExecutionBudget::is_match_binder_variable`]), a range no execution,
/// quantifier, fold, load or pointer producer mints from. Given that, an
/// occurrence of a binder's identity in the arm body is a bound occurrence of
/// that binder -- or of a nested match's binder that shadows it, which the
/// rewrite walker stops at. A binder from any other range is a live free
/// identity and substituting it would be a capture, so the rewrite refuses
/// instead of performing it.
fn rewrite_integer_match_typed_fields(
    body: IntegerTerm,
    bindings: &[AlgebraicValue],
    fields: &[AlgebraicValue],
) -> Option<IntegerTerm> {
    if bindings.len() != fields.len() {
        return None;
    }
    let mut c_replacements = BTreeMap::new();
    let mut integer_replacements = BTreeMap::new();
    let mut algebraic_replacements = BTreeMap::new();
    for (binding, field) in bindings.iter().zip(fields) {
        match (binding, field) {
            (AlgebraicValue::Integer(IntegerTerm::Variable(from)), AlgebraicValue::Integer(to)) => {
                if !ExecutionBudget::is_match_binder_variable(*from) {
                    return None;
                }
                if integer_replacements.insert(*from, to.clone()).is_some() {
                    return None;
                }
            }
            (AlgebraicValue::C(from), AlgebraicValue::C(to)) => match (from, to) {
                (CValue::Void, CValue::Void) => {}
                (from, to) if c_value_bitvector_term(from).is_some() => {
                    let from = c_value_bitvector_term(from)?;
                    let Bitvector32Term::Variable(from) = from else {
                        return None;
                    };
                    if !ExecutionBudget::is_match_binder_variable(from) {
                        return None;
                    }
                    let to = c_value_bitvector_term(to)?;
                    if c_replacements
                        .insert(
                            from,
                            crate::kernel::proof::term_rewrite::TypedCReplacement::Bitvector(to),
                        )
                        .is_some()
                    {
                        return None;
                    }
                }
                (CValue::Pointer(from), CValue::Pointer(to)) => {
                    let (PointerBlock::Symbolic(from) | PointerBlock::FunctionSymbolic(from)) =
                        &from.block
                    else {
                        return None;
                    };
                    if !ExecutionBudget::is_match_binder_variable(*from) {
                        return None;
                    }
                    if c_replacements
                        .insert(
                            *from,
                            crate::kernel::proof::term_rewrite::TypedCReplacement::Pointer(
                                to.clone(),
                            ),
                        )
                        .is_some()
                    {
                        return None;
                    }
                }
                // A value of an abstract type is an algebraic term; its
                // binder is replaced as an algebraic binder is.
                (CValue::Parameter(from), CValue::Parameter(to)) => {
                    let AlgebraicTermNode::Variable(from) = &from.node else {
                        return None;
                    };
                    if !ExecutionBudget::is_match_binder_variable(*from) {
                        return None;
                    }
                    if algebraic_replacements
                        .insert(*from, to.as_ref().clone())
                        .is_some()
                    {
                        return None;
                    }
                }
                _ => return None,
            },
            (AlgebraicValue::Algebraic(from), AlgebraicValue::Algebraic(to)) => {
                let AlgebraicTermNode::Variable(from) = &from.node else {
                    return None;
                };
                if !ExecutionBudget::is_match_binder_variable(*from) {
                    return None;
                }
                if algebraic_replacements.insert(*from, to.clone()).is_some() {
                    return None;
                }
            }
            _ => return None,
        }
    }
    rewrite_integer_match_typed_body(
        body,
        &c_replacements,
        &integer_replacements,
        &algebraic_replacements,
    )
}

fn evaluate_integer_binary_paths_in(
    scope: SpecScope<'_>,
    left: &SpecIntegerExpression,
    right: &SpecIntegerExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
    operation: IntegerBinaryOperation,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    let left_paths = evaluate_spec_integer_expression_paths_in(scope, left, assumptions, budget)?;
    let mut result = Vec::new();
    for left_path in left_paths {
        let path_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in
            evaluate_spec_integer_expression_paths_in(scope, right, &path_assumptions, budget)?
        {
            let Some((facts, mut obligations)) = merge_execution_pure_facts_and_obligations_under(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
                &path_assumptions,
            ) else {
                continue;
            };
            let left_bits = integer_term_bits(&left_path.value);
            let right_bits = integer_term_bits(&right_path.value);
            let work = match operation {
                IntegerBinaryOperation::Multiply
                | IntegerBinaryOperation::TruncatingQuotient
                | IntegerBinaryOperation::TruncatingRemainder => {
                    left_bits.saturating_mul(right_bits)
                }
                IntegerBinaryOperation::Add | IntegerBinaryOperation::Subtract => {
                    left_bits.saturating_add(right_bits)
                }
            };
            if crate::instrumentation::numeric_operation_work_exceeded(work) {
                return Err(ExecutionLimit::Deadline);
            }
            if matches!(
                operation,
                IntegerBinaryOperation::TruncatingQuotient
                    | IntegerBinaryOperation::TruncatingRemainder
            ) {
                let nonzero = ConditionTerm::integer_not_equal(
                    right_path.value.clone(),
                    IntegerTerm::constant_i64(0),
                );
                retain_required_integer_obligation(
                    &mut obligations,
                    &path_assumptions,
                    Proposition::ConditionIs(nonzero, true),
                );
            }
            let value = match operation {
                IntegerBinaryOperation::Add => {
                    IntegerTerm::add(left_path.value.clone(), right_path.value)
                }
                IntegerBinaryOperation::Subtract => {
                    IntegerTerm::subtract(left_path.value.clone(), right_path.value)
                }
                IntegerBinaryOperation::Multiply => {
                    IntegerTerm::multiply(left_path.value.clone(), right_path.value)
                }
                IntegerBinaryOperation::TruncatingQuotient => {
                    IntegerTerm::truncating_quotient(left_path.value.clone(), right_path.value)
                }
                IntegerBinaryOperation::TruncatingRemainder => {
                    IntegerTerm::truncating_remainder(left_path.value.clone(), right_path.value)
                }
            };
            result.push(SpecIntegerPath {
                value,
                facts,
                obligations,
            });
        }
    }
    Ok(result)
}

#[derive(Clone, Copy)]
enum IntegerBinaryOperation {
    Add,
    Subtract,
    Multiply,
    TruncatingQuotient,
    TruncatingRemainder,
}

fn integer_term_bits(term: &IntegerTerm) -> usize {
    term.as_const()
        .and_then(|value| usize::try_from(value.bits()).ok())
        .unwrap_or(1)
        .saturating_add(1)
}

fn lower_spec_algebraic_comparison_at_state_in(
    scope: SpecScope<'_>,
    left: &SpecAlgebraicExpression,
    equal: bool,
    right: &SpecAlgebraicExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    if super::functions::spec_algebraic_expression_is_obligation_free(left)
        && super::functions::spec_algebraic_expression_is_obligation_free(right)
        && super::functions::spec_algebraic_expression_is_state_independent(left)
        && super::functions::spec_algebraic_expression_is_state_independent(right)
        && (left == right
            || algebraic_match_reconstructs(left, right)
            || algebraic_match_reconstructs(right, left))
    {
        return Ok(vec![SpecPropositionPath {
            introductions: Vec::new(),
            proposition: Proposition::ConditionIs(ConditionTerm::Constant(equal), true),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }]);
    }
    let mut paths = Vec::new();
    for left_path in
        evaluate_spec_algebraic_at_state_with_bindings_in(scope, left, assumptions, budget)?
    {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_algebraic_at_state_with_bindings_in(
            scope,
            right,
            &right_assumptions,
            budget,
        )? {
            if left_path.value.algebraic_type != right_path.value.algebraic_type {
                continue;
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
                &right_assumptions,
            ) else {
                continue;
            };
            // State-dependent projections must be resolved (and their ownership
            // checked) before reflexivity can close a symbolic application.
            let equality = if left_path.value == right_path.value {
                Proposition::ConditionIs(ConditionTerm::Constant(true), true)
            } else {
                Proposition::Equal(
                    Term::Algebraic(left_path.value.clone()),
                    Term::Algebraic(right_path.value),
                )
            };
            paths.push(SpecPropositionPath {
                introductions: if equal {
                    Vec::new()
                } else {
                    vec![LoweringIntroduction::ComparisonNegation]
                },
                proposition: if equal {
                    equality
                } else {
                    Proposition::Not(Box::new(equality))
                },
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

fn algebraic_match_reconstructs(
    expression: &SpecAlgebraicExpression,
    scrutinee: &SpecAlgebraicExpression,
) -> bool {
    let SpecAlgebraicExpressionNode::Match {
        scrutinee: matched,
        arms,
    } = &expression.node
    else {
        return false;
    };
    if matched.as_ref() != scrutinee || expression.algebraic_type != scrutinee.algebraic_type {
        return false;
    }
    let arm_variants = arms
        .iter()
        .map(|arm| arm.variant.as_str())
        .collect::<BTreeSet<_>>();
    !scrutinee.algebraic_type.rigid
        && arms.len() == scrutinee.algebraic_type.variants.len()
        && arm_variants.len() == arms.len()
        && arms.iter().all(|arm| {
            let Some(schema) = scrutinee
                .algebraic_type
                .variants
                .iter()
                .find(|variant| variant.name == arm.variant)
            else {
                return false;
            };
            let SpecAlgebraicExpressionNode::Constructor { variant, fields } = &arm.body.node
            else {
                return false;
            };
            arm.body.algebraic_type == scrutinee.algebraic_type
                && variant == &arm.variant
                && arm.binding_types == schema.fields
                && fields.len() == arm.bindings.len()
                && fields.iter().zip(&schema.fields).zip(&arm.bindings).all(
                    |((field, field_type), binding)| match (field, field_type) {
                        (
                            SpecAlgebraicValue::C(SpecExpression::CExpression(
                                CExpression::Variable(name),
                            )),
                            AlgebraicValueType::C(_) | AlgebraicValueType::ObjectPointer(_, _),
                        ) => name == binding,
                        (
                            SpecAlgebraicValue::Algebraic(SpecAlgebraicExpression {
                                node: SpecAlgebraicExpressionNode::Binding(name),
                                ..
                            }),
                            AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_),
                        ) => name == binding,
                        _ => false,
                    },
                )
        })
}

#[cfg(test)]
fn evaluate_spec_algebraic_at_state_in(
    state: &CState,
    expression: &SpecAlgebraicExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecAlgebraicPath>> {
    evaluate_spec_algebraic_at_state_with_bindings_in(
        SpecScope::unbound(state, loop_entry_state),
        expression,
        assumptions,
        budget,
    )
}

fn evaluate_spec_algebraic_at_state_with_bindings_in(
    scope: SpecScope<'_>,
    expression: &SpecAlgebraicExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecAlgebraicPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    let algebraic_bindings = scope.algebraic_bindings;
    budget.consume_expression_step()?;
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(projection) => {
            let snapshot = if projection.at_entry {
                loop_entry_state.ok_or(ExecutionLimit::Paths)?
            } else {
                state
            };
            let Some(AlgebraicValue::Algebraic(value)) = snapshot
                .resource_instance_at_path(projection.identity, &projection.children)
                .and_then(|instance| instance.fields().get(projection.field_index))
            else {
                return Err(ExecutionLimit::ResourceFieldInstanceUnavailable);
            };
            if value.algebraic_type != expression.algebraic_type {
                return Err(ExecutionLimit::Paths);
            }
            Ok(vec![SpecAlgebraicPath {
                value: value.clone(),
                facts: vec![].into(),
                obligations: vec![],
            }])
        }
        SpecAlgebraicExpressionNode::Variable(variable) => Ok(vec![SpecAlgebraicPath {
            value: AlgebraicTerm {
                algebraic_type: expression.algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(*variable),
            },
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }]),
        SpecAlgebraicExpressionNode::CValue(value) => {
            let mut paths = Vec::new();
            for path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                value,
                assumptions,
                budget,
            )? {
                let CValue::Parameter(term) = path.value else {
                    return Err(ExecutionLimit::Paths);
                };
                if term.algebraic_type != expression.algebraic_type {
                    return Err(ExecutionLimit::Paths);
                }
                paths.push(SpecAlgebraicPath {
                    value: *term,
                    facts: path.facts,
                    obligations: path.obligations,
                });
            }
            Ok(paths)
        }
        SpecAlgebraicExpressionNode::Binding(name) => {
            let Some(value) = algebraic_bindings.get(name) else {
                return Err(ExecutionLimit::Paths);
            };
            if value.algebraic_type != expression.algebraic_type {
                return Err(ExecutionLimit::Paths);
            }
            Ok(vec![SpecAlgebraicPath {
                value: value.clone(),
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }])
        }
        SpecAlgebraicExpressionNode::If {
            condition,
            then_branch,
            else_branch,
        } => evaluate_spec_algebraic_if_paths_in(
            scope,
            &expression.algebraic_type,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        ),
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            if !spec_algebraic_result_match_arms_are_well_formed(&scrutinee.algebraic_type, arms) {
                return Err(ExecutionLimit::Paths);
            }
            let mut result = Vec::new();
            for scrutinee_path in evaluate_spec_algebraic_at_state_with_bindings_in(
                scope,
                scrutinee,
                assumptions,
                budget,
            )? {
                if !matches!(
                    scrutinee_path.value.node,
                    AlgebraicTermNode::Constructor { .. }
                ) {
                    let mut lowered_arms = Vec::with_capacity(arms.len());
                    let facts = scrutinee_path.facts.clone();
                    let obligations = scrutinee_path.obligations.clone();
                    for arm in arms {
                        let Some(schema) = scrutinee_path
                            .value
                            .algebraic_type
                            .variants
                            .iter()
                            .find(|variant| variant.name == arm.variant)
                        else {
                            return Err(ExecutionLimit::Paths);
                        };
                        let bindings = symbolic_algebraic_match_binders_in(
                            &scrutinee_path.value.algebraic_type,
                            schema,
                            budget,
                        )?;
                        let mut body_state = state.clone();
                        let mut body_algebraic_bindings = algebraic_bindings.clone();
                        for (binding, value) in arm.bindings.iter().zip(&bindings) {
                            match value {
                                AlgebraicValue::C(value) => {
                                    body_state.locals.set(binding.clone(), value.clone());
                                }
                                AlgebraicValue::Integer(_) => {}
                                AlgebraicValue::Algebraic(value) => {
                                    body_algebraic_bindings.insert(binding.clone(), value.clone());
                                }
                            }
                        }
                        let body_assumptions =
                            assumptions_with_path_context(assumptions, &facts, &obligations);
                        let mut body_paths = budget.with_integer_bindings(
                            &arm.binding_variables,
                            &bindings,
                            |budget| {
                                evaluate_spec_algebraic_at_state_with_bindings_in(
                                    SpecScope {
                                        state: &body_state,
                                        algebraic_bindings: &body_algebraic_bindings,
                                        ..scope
                                    },
                                    &arm.body,
                                    &body_assumptions,
                                    budget,
                                )
                            },
                        )?;
                        let Some(body_path) = body_paths.pop() else {
                            return Err(ExecutionLimit::Paths);
                        };
                        if !body_paths.is_empty() {
                            return Err(ExecutionLimit::Paths);
                        }
                        // Arm-local facts and obligations are valid only when this
                        // constructor is selected. A symbolic match must not leak
                        // them into its unconditional enclosing path.
                        if body_path.facts.has_path_conditions()
                            || !body_path.obligations.is_empty()
                        {
                            return Err(ExecutionLimit::Paths);
                        }
                        // The only remaining body facts are derived read equations.
                        // They belong to this arm, not to the enclosing match.
                        lowered_arms.push(AlgebraicResultMatchArm {
                            binding_names: crate::kernel::BindingNames::written(&arm.bindings),
                            variant: arm.variant.clone(),
                            bindings,
                            body: body_path.value,
                        });
                    }
                    result.push(SpecAlgebraicPath {
                        value: AlgebraicTerm {
                            algebraic_type: expression.algebraic_type.clone(),
                            node: AlgebraicTermNode::Match {
                                scrutinee: Box::new(scrutinee_path.value),
                                arms: lowered_arms,
                            },
                        },
                        facts,
                        obligations,
                    });
                    continue;
                }
                for case in algebraic_case_paths_in(&scrutinee_path.value, budget)? {
                    let Some(arm) = arms.iter().find(|arm| arm.variant == case.variant) else {
                        return Err(ExecutionLimit::Paths);
                    };
                    // Arms were checked against the scrutinee schema above;
                    // case construction supplies fields of those exact types.
                    // Re-inferring their carrier erases nominal pointer types.
                    if arm.bindings.len() != case.fields.len() {
                        return Err(ExecutionLimit::Paths);
                    }
                    let mut body_state = state.clone();
                    let mut body_algebraic_bindings = algebraic_bindings.clone();
                    for (binding, field) in arm.bindings.iter().zip(&case.fields) {
                        match field {
                            AlgebraicValue::C(field) => {
                                body_state.locals.set(binding.clone(), field.clone());
                            }
                            AlgebraicValue::Integer(_) => {}
                            AlgebraicValue::Algebraic(field) => {
                                body_algebraic_bindings.insert(binding.clone(), field.clone());
                            }
                        }
                    }
                    let Some((case_facts, case_obligations)) =
                        merge_execution_pure_facts_and_obligations(
                            &scrutinee_path.facts,
                            &scrutinee_path.obligations,
                            &case.facts,
                            &case.obligations,
                            assumptions,
                        )
                    else {
                        continue;
                    };
                    let body_assumptions =
                        assumptions_with_path_context(assumptions, &case_facts, &case_obligations);
                    for body_path in budget.with_integer_bindings(
                        &arm.binding_variables,
                        &case.fields,
                        |budget| {
                            evaluate_spec_algebraic_at_state_with_bindings_in(
                                SpecScope {
                                    state: &body_state,
                                    algebraic_bindings: &body_algebraic_bindings,
                                    ..scope
                                },
                                &arm.body,
                                &body_assumptions,
                                budget,
                            )
                        },
                    )? {
                        if let Some((facts, obligations)) =
                            merge_execution_pure_facts_and_obligations_under(
                                &case_facts,
                                &case_obligations,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                &body_assumptions,
                            )
                        {
                            result.push(SpecAlgebraicPath {
                                value: body_path.value,
                                facts,
                                obligations,
                            });
                        }
                    }
                }
            }
            budget.check_path_width(result.len())?;
            Ok(result)
        }
        SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
            let Some(schema) = expression
                .algebraic_type
                .variants
                .iter()
                .find(|schema| schema.name == *variant)
            else {
                return Err(ExecutionLimit::Paths);
            };
            if schema.fields.len() != fields.len() {
                return Err(ExecutionLimit::Paths);
            }
            let mut paths = vec![(Vec::new(), ExecutionFacts::new(), Vec::new())];
            for (field, expected) in fields.iter().zip(&schema.fields) {
                let mut next = Vec::new();
                for (values, facts, obligations) in paths {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for mut field_path in evaluate_spec_algebraic_value_at_state_in(
                        scope,
                        field,
                        &path_assumptions,
                        budget,
                    )? {
                        if !field_path.value.has_type(expected) {
                            // The same original-class check governs model
                            // fields and calls. It also handles known null
                            // aliases and a declared object's block class.
                            let (
                                AlgebraicValueType::ObjectPointer(ty, class),
                                AlgebraicValue::C(value),
                            ) = (expected, &mut field_path.value)
                            else {
                                continue;
                            };
                            if value.c_type() != *ty {
                                continue;
                            }
                            let context = assumptions_with_path_context(
                                &path_assumptions,
                                &field_path.facts,
                                &field_path.obligations,
                            );
                            if !refine_object_pointer_argument(
                                value,
                                class,
                                scope.state.memory(),
                                &context,
                            ) {
                                continue;
                            }
                        }
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations_under(
                                &facts,
                                &obligations,
                                &field_path.facts,
                                &field_path.obligations,
                                assumptions,
                                &path_assumptions,
                            )
                        else {
                            continue;
                        };
                        let mut next_values = values.clone();
                        next_values.push(field_path.value);
                        next.push((next_values, merged_facts, merged_obligations));
                    }
                }
                paths = next;
            }
            let paths = paths
                .into_iter()
                .map(|(fields, facts, obligations)| SpecAlgebraicPath {
                    value: AlgebraicTerm {
                        algebraic_type: expression.algebraic_type.clone(),
                        node: AlgebraicTermNode::Constructor {
                            variant: variant.clone(),
                            fields,
                        },
                    },
                    facts,
                    obligations,
                })
                .collect::<Vec<_>>();
            budget.check_path_width(paths.len())?;
            Ok(paths)
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            let mut paths = vec![(Vec::new(), ExecutionFacts::new(), Vec::new())];
            for argument in arguments {
                let mut next = Vec::new();
                for (values, facts, obligations) in paths {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for argument_path in evaluate_spec_pure_function_argument_paths_in(
                        scope,
                        argument,
                        &path_assumptions,
                        budget,
                    )? {
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations_under(
                                &facts,
                                &obligations,
                                &argument_path.facts,
                                &argument_path.obligations,
                                assumptions,
                                &path_assumptions,
                            )
                        else {
                            continue;
                        };
                        let mut values = values.clone();
                        values.push(argument_path.value);
                        next.push((values, merged_facts, merged_obligations));
                    }
                }
                paths = next;
            }
            Ok(paths
                .into_iter()
                .map(|(arguments, facts, mut obligations)| {
                    if name == "to_nat"
                        && let Some(PureFunctionArgument::Integer(value)) = arguments.first()
                    {
                        let nonnegative = ConditionTerm::integer_greater_equal(
                            value.as_ref().clone(),
                            crate::kernel::IntegerTerm::Constant(0.into()),
                        );
                        let required = Proposition::ConditionIs(nonnegative, true);
                        if super::check_nat_integer_law(
                            "click::nat::to_integer_nonnegative",
                            &required,
                        )
                        .is_none()
                        {
                            retain_required_integer_obligation(
                                &mut obligations,
                                assumptions,
                                required,
                            );
                        }
                    }
                    SpecAlgebraicPath {
                        value: AlgebraicTerm {
                            algebraic_type: expression.algebraic_type.clone(),
                            node: AlgebraicTermNode::PureFunctionApplication {
                                name: name.clone(),
                                arguments,
                            },
                        },
                        facts,
                        obligations,
                    }
                })
                .collect())
        }
    }
}

/// One symbolic value per field of `variant`, to bind a match arm's patterns
/// to.
///
/// The identities come from the budget's match-binder range, not from the
/// execution counter: they are *bound* variables of the match term being
/// lowered, and a bound variable that happens to equal a live execution's
/// free identity is what let the binder-elimination rewrite substitute a
/// loop-havocked local along with the binder it was named after.
fn symbolic_algebraic_match_binders_in(
    algebraic_type: &AlgebraicType,
    variant: &AlgebraicVariantType,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<AlgebraicValue>> {
    symbolic_algebraic_fields(algebraic_type, variant, || {
        budget.allocate_match_binder_variable()
    })
}

/// One symbolic value per field of `variant`, as the arbitrary witness of a
/// case split on a scrutinee whose constructor is not known.
///
/// These are *free* variables of the constructor equation this case
/// publishes, so they must be fresh for the execution the state belongs to
/// and come from its counter. A budget that cannot invent execution
/// identities refuses here, which is the point: a case witness minted beside
/// a live state from a restarted counter would name something that state
/// already holds.
fn symbolic_algebraic_case_witnesses_in(
    algebraic_type: &AlgebraicType,
    variant: &AlgebraicVariantType,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<AlgebraicValue>> {
    symbolic_algebraic_fields(algebraic_type, variant, || {
        budget.allocate_kernel_variable()
    })
}

fn symbolic_algebraic_fields(
    algebraic_type: &AlgebraicType,
    variant: &AlgebraicVariantType,
    mut allocate: impl FnMut() -> ExecutionResult<Variable>,
) -> ExecutionResult<Vec<AlgebraicValue>> {
    variant
        .fields
        .iter()
        .enumerate()
        .map(|(index, value_type)| {
            let variable = allocate()?;
            match value_type {
                AlgebraicValueType::C(c_type) | AlgebraicValueType::ObjectPointer(c_type, _) => {
                    Ok(AlgebraicValue::C(
                        algebraic_type
                            .symbolic_c_field_value(&variant.name, index, *c_type, variable)
                            .with_pointer_object_class(value_type.object_class()),
                    ))
                }
                AlgebraicValueType::Integer => {
                    Ok(AlgebraicValue::Integer(IntegerTerm::var(variable)))
                }
                AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_) => {
                    algebraic_type
                        .resolve_nested_type(value_type)
                        .map(|nested_type| {
                            AlgebraicValue::Algebraic(AlgebraicTerm {
                                algebraic_type: nested_type,
                                node: AlgebraicTermNode::Variable(variable),
                            })
                        })
                        .ok_or(ExecutionLimit::Paths)
                }
            }
        })
        .collect()
}

fn evaluate_spec_algebraic_value_at_state_in(
    scope: SpecScope<'_>,
    value: &SpecAlgebraicValue,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecAlgebraicValuePath>> {
    match value {
        SpecAlgebraicValue::Integer(expression) => {
            Ok(
                evaluate_spec_integer_expression_paths_in(scope, expression, assumptions, budget)?
                    .into_iter()
                    .map(|path| SpecAlgebraicValuePath {
                        value: AlgebraicValue::Integer(path.value),
                        facts: path.facts,
                        obligations: path.obligations,
                    })
                    .collect(),
            )
        }
        SpecAlgebraicValue::C(expression) => {
            Ok(evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                expression,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| SpecAlgebraicValuePath {
                value: AlgebraicValue::C(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
        SpecAlgebraicValue::Algebraic(expression) => {
            Ok(evaluate_spec_algebraic_at_state_with_bindings_in(
                scope,
                expression,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| SpecAlgebraicValuePath {
                value: AlgebraicValue::Algebraic(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
    }
}

fn spec_algebraic_result_match_arms_are_well_formed(
    algebraic_type: &AlgebraicType,
    arms: &[SpecAlgebraicResultMatchArm],
) -> bool {
    !algebraic_type.rigid
        && arms.len() == algebraic_type.variants.len()
        && algebraic_type.variants.iter().all(|variant| {
            arms.iter()
                .filter(|arm| arm.variant == variant.name)
                .count()
                == 1
                && arms
                    .iter()
                    .find(|arm| arm.variant == variant.name)
                    .is_some_and(|arm| {
                        arm.binding_types == variant.fields && arm.bindings_are_well_formed()
                    })
        })
}

fn spec_scalar_match_arms_are_well_formed(
    algebraic_type: &AlgebraicType,
    arms: &[SpecAlgebraicMatchArm],
) -> bool {
    !algebraic_type.rigid
        && arms.len() == algebraic_type.variants.len()
        && algebraic_type.variants.iter().all(|variant| {
            arms.iter()
                .filter(|arm| arm.variant == variant.name)
                .count()
                == 1
                && arms
                    .iter()
                    .find(|arm| arm.variant == variant.name)
                    .is_some_and(|arm| {
                        arm.bindings.len() == variant.fields.len()
                            && arm.binding_types == variant.fields
                    })
        })
}

fn algebraic_case_paths_in(
    term: &AlgebraicTerm,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecAlgebraicCasePath>> {
    match &term.node {
        AlgebraicTermNode::Constructor { variant, fields } => Ok(vec![SpecAlgebraicCasePath {
            variant: variant.clone(),
            fields: fields.clone(),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }]),
        AlgebraicTermNode::Variable(_)
        | AlgebraicTermNode::Match { .. }
        | AlgebraicTermNode::If { .. }
        | AlgebraicTermNode::MemoryLoad { .. }
        | AlgebraicTermNode::PureFunctionApplication { .. } => {
            let mut paths = Vec::with_capacity(term.algebraic_type.variants.len());
            for variant in term.algebraic_type.variants.iter() {
                let fields =
                    symbolic_algebraic_case_witnesses_in(&term.algebraic_type, variant, budget)?;
                let constructor = AlgebraicTerm {
                    algebraic_type: term.algebraic_type.clone(),
                    node: AlgebraicTermNode::Constructor {
                        variant: variant.name.clone(),
                        fields: fields.clone(),
                    },
                };
                paths.push(SpecAlgebraicCasePath {
                    variant: variant.name.clone(),
                    fields,
                    facts: vec![ExecutionPureFact::new(Proposition::Equal(
                        Term::Algebraic(term.clone()),
                        Term::Algebraic(constructor),
                    ))]
                    .into(),
                    obligations: Vec::new(),
                });
            }
            budget.check_path_width(paths.len())?;
            Ok(paths)
        }
    }
}

fn lower_spec_sequence_membership_at_state_in(
    scope: SpecScope<'_>,
    element: &SpecExpression,
    sequence: &SpecSequenceExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for element_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        element,
        assumptions,
        budget,
    )? {
        let sequence_assumptions = assumptions_with_path_context(
            assumptions,
            &element_path.facts,
            &element_path.obligations,
        );
        for sequence_path in
            evaluate_spec_sequence_at_state_in(scope, sequence, &sequence_assumptions, budget)?
        {
            if sequence_path
                .value
                .element_type
                .is_some_and(|element_type| element_type != element_path.value.c_type())
            {
                continue;
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &element_path.facts,
                &element_path.obligations,
                &sequence_path.facts,
                &sequence_path.obligations,
                assumptions,
                &sequence_assumptions,
            ) else {
                continue;
            };
            let comparisons = sequence_elements(&sequence_path.value)
                .filter_map(|member| {
                    c_value_comparison_proposition(
                        &element_path.value,
                        CComparisonOperator::Equal,
                        member,
                    )
                })
                .collect::<Vec<_>>();
            let proposition = comparisons
                .into_iter()
                .reduce(|left, right| Proposition::Or(Box::new(left), Box::new(right)))
                .unwrap_or(Proposition::ConditionIs(
                    ConditionTerm::Constant(false),
                    true,
                ));
            paths.push(SpecPropositionPath {
                introductions: Vec::new(),
                proposition,
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

pub(super) fn sequence_elements(sequence: &SequenceTerm) -> SequenceElements<'_> {
    SequenceElements {
        pending: vec![sequence],
        current: None,
    }
}

pub(super) struct SequenceElements<'a> {
    pending: Vec<&'a SequenceTerm>,
    current: Option<std::slice::Iter<'a, CValue>>,
}

impl<'a> Iterator for SequenceElements<'a> {
    type Item = &'a CValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(values) = &mut self.current {
                if let Some(value) = values.next() {
                    return Some(value);
                }
                self.current = None;
            }
            match self.pending.pop()?.node.as_ref() {
                SequenceTermNode::Literal(values) => self.current = Some(values.iter()),
                SequenceTermNode::Concat(left, right) => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
    }
}

fn lower_spec_sequence_comparison_at_state_in(
    scope: SpecScope<'_>,
    left: &SpecSequenceExpression,
    equal: bool,
    right: &SpecSequenceExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_spec_sequence_at_state_in(scope, left, assumptions, budget)? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in
            evaluate_spec_sequence_at_state_in(scope, right, &right_assumptions, budget)?
        {
            if !sequence_element_types_compatible(
                left_path.value.element_type,
                right_path.value.element_type,
            ) {
                continue;
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
                &right_assumptions,
            ) else {
                continue;
            };
            let equality = finite_sequence_equality(&left_path.value, &right_path.value);
            paths.push(SpecPropositionPath {
                introductions: if equal {
                    Vec::new()
                } else {
                    vec![LoweringIntroduction::ComparisonNegation]
                },
                proposition: if equal {
                    equality
                } else {
                    Proposition::Not(Box::new(equality))
                },
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

/// Finite integer sequences have ordinary elementwise equality. Expose that
/// logical structure once during elaboration, so every proof context can use
/// the same introduction, extraction, and equality rules. Other element types
/// retain logical sequence equality (not C floating or address comparison).
fn finite_sequence_equality(left: &SequenceTerm, right: &SequenceTerm) -> Proposition {
    let fallback =
        || Proposition::Equal(Term::Sequence(left.clone()), Term::Sequence(right.clone()));
    let mut left = sequence_elements(left);
    let mut right = sequence_elements(right);
    let mut equalities = Vec::new();
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) => {
                let Some(equality) = integer_sequence_element_equality(left, right) else {
                    return fallback();
                };
                equalities.push(equality);
            }
            (None, None) => break,
            _ => return Proposition::ConditionIs(ConditionTerm::Constant(false), true),
        }
    }
    if equalities.is_empty() {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    }
    while equalities.len() > 1 {
        let mut next = Vec::with_capacity(equalities.len().div_ceil(2));
        let mut values = equalities.into_iter();
        while let Some(left) = values.next() {
            next.push(match values.next() {
                Some(right) => Proposition::And(Box::new(left), Box::new(right)),
                None => left,
            });
        }
        equalities = next;
    }
    equalities.pop().expect("nonempty equality tree")
}

pub(super) fn integer_sequence_element_equality(
    left: &CValue,
    right: &CValue,
) -> Option<Proposition> {
    if left.c_type() != right.c_type() || !matches!(left, crate::kernel::integer64_c_value!(_)) {
        return None;
    }
    c_value_comparison_proposition(left, CComparisonOperator::Equal, right)
}

fn evaluate_spec_sequence_at_state_in(
    scope: SpecScope<'_>,
    expression: &SpecSequenceExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecSequencePath>> {
    budget.consume_expression_step()?;
    match expression {
        SpecSequenceExpression::Literal(elements) => {
            let mut paths = vec![(Vec::new(), ExecutionFacts::new(), Vec::new())];
            for element in elements {
                let mut next = Vec::new();
                for (values, facts, obligations) in paths {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for element_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                        scope,
                        element,
                        &path_assumptions,
                        budget,
                    )? {
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations_under(
                                &facts,
                                &obligations,
                                &element_path.facts,
                                &element_path.obligations,
                                assumptions,
                                &path_assumptions,
                            )
                        else {
                            continue;
                        };
                        let mut next_values = values.clone();
                        next_values.push(element_path.value);
                        next.push((next_values, merged_facts, merged_obligations));
                    }
                }
                paths = next;
            }
            Ok(paths
                .into_iter()
                .filter_map(|(values, facts, obligations)| {
                    let element_type = values.first().map(CValue::c_type);
                    values
                        .iter()
                        .all(|value| Some(value.c_type()) == element_type)
                        .then(|| SpecSequencePath {
                            value: SequenceTerm {
                                element_type,
                                node: std::sync::Arc::new(SequenceTermNode::Literal(values.into())),
                            },
                            facts,
                            obligations,
                        })
                })
                .collect())
        }
        SpecSequenceExpression::Concat(left, right) => {
            let mut paths = Vec::new();
            for left_path in evaluate_spec_sequence_at_state_in(scope, left, assumptions, budget)? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in
                    evaluate_spec_sequence_at_state_in(scope, right, &right_assumptions, budget)?
                {
                    if !sequence_element_types_compatible(
                        left_path.value.element_type,
                        right_path.value.element_type,
                    ) {
                        continue;
                    }
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &left_path.facts,
                            &left_path.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                            &right_assumptions,
                        )
                    else {
                        continue;
                    };
                    paths.push(SpecSequencePath {
                        value: concatenate_sequence_terms(
                            left_path.value.clone(),
                            right_path.value,
                        ),
                        facts,
                        obligations,
                    });
                }
            }
            Ok(paths)
        }
    }
}

fn sequence_element_types_compatible(left: Option<CType>, right: Option<CType>) -> bool {
    left.is_none() || right.is_none() || left == right
}

fn concatenate_sequence_terms(left: SequenceTerm, right: SequenceTerm) -> SequenceTerm {
    if matches!(left.node.as_ref(), SequenceTermNode::Literal(values) if values.is_empty()) {
        return right;
    }
    if matches!(right.node.as_ref(), SequenceTermNode::Literal(values) if values.is_empty()) {
        return left;
    }
    SequenceTerm {
        element_type: left.element_type.or(right.element_type),
        node: std::sync::Arc::new(SequenceTermNode::Concat(left, right)),
    }
}

#[cfg(test)]
mod sequence_term_tests;

#[cfg(test)]
mod algebraic_term_tests;

fn lower_spec_float_classification_proposition_at_state_in(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    classification: CFloatClassification,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    Ok(evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        expression,
        assumptions,
        budget,
    )?
    .into_iter()
    .filter_map(|path| {
        let condition = match path.value {
            CValue::Float32(value) => ConditionTerm::float32_classification(value, classification),
            CValue::Float64(value) => ConditionTerm::float64_classification(value, classification),
            _ => return None,
        };
        Some(SpecPropositionPath {
            introductions: Vec::new(),
            proposition: Proposition::ConditionIs(condition, true),
            facts: path.facts,
            obligations: path.obligations,
        })
    })
    .collect())
}

#[derive(Clone)]
struct SpecValuesPath {
    values: Vec<CValue>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

fn evaluate_spec_values_at_state_in(
    scope: SpecScope<'_>,
    expressions: &[SpecExpression],
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecValuesPath>> {
    let mut paths = vec![SpecValuesPath {
        values: Vec::new(),
        facts: Vec::new().into(),
        obligations: Vec::new(),
    }];
    for expression in expressions {
        let mut next_paths = Vec::new();
        for prefix in paths {
            let path_assumptions =
                assumptions_with_path_context(assumptions, &prefix.facts, &prefix.obligations);
            for value_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                expression,
                &path_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &prefix.facts,
                    &prefix.obligations,
                    &value_path.facts,
                    &value_path.obligations,
                    assumptions,
                    &path_assumptions,
                ) else {
                    continue;
                };
                let mut values = prefix.values.clone();
                values.push(value_path.value);
                next_paths.push(SpecValuesPath {
                    values,
                    facts,
                    obligations,
                });
            }
        }
        paths = next_paths;
    }
    Ok(paths)
}

fn evaluate_spec_resource_at_state_in(
    scope: SpecScope<'_>,
    resource: &SpecResource,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<EvaluatedSpecResource>> {
    let (expressions, build): (Vec<SpecExpression>, SpecResourceBuilder) = match resource {
        SpecResource::Memory {
            base,
            start,
            end,
            element_width,
        } => {
            let element_width = *element_width;
            (
                vec![base.clone(), start.clone(), end.clone()],
                Box::new(move |values| match values.as_slice() {
                    // A range with an unsigned 64-bit bound is wide, here as
                    // in a contract clause, so a `separate(...)` or
                    // containment names the range the clause holds.
                    [CValue::Pointer(base), start, end]
                        if crate::kernel::wide_range_bounds(start, end).is_some() =>
                    {
                        let (start, end) = crate::kernel::wide_range_bounds(start, end)?;
                        Some(CResource::Memory(CMemoryRange::from_pointer_value_wide(
                            base,
                            start,
                            end,
                            element_width,
                        )))
                    }
                    [
                        CValue::Pointer(base),
                        CValue::Int32(start),
                        CValue::Int32(end),
                    ] => Some(CResource::Memory(CMemoryRange::from_pointer_value(
                        base,
                        start.clone(),
                        end.clone(),
                        element_width,
                    ))),
                    // A constant unsigned 64-bit end over a 32-bit start is the
                    // same number as a 32-bit bound, as a clause's segment
                    // reads it.
                    [
                        CValue::Pointer(base),
                        CValue::Int32(start),
                        CValue::UInt64(end),
                    ] => {
                        let end = i32::try_from(end.uint64_as_const()?).ok()?;
                        Some(CResource::Memory(CMemoryRange::from_pointer_value(
                            base,
                            start.clone(),
                            Bitvector32Term::Constant(end as u32),
                            element_width,
                        )))
                    }
                    _ => None,
                }),
            )
        }
        SpecResource::Composite { name, arguments } => {
            let name = name.clone();
            (
                arguments.clone(),
                Box::new(move |arguments| {
                    Some(CResource::Composite {
                        name: name.clone(),
                        arguments: arguments.into_iter().map(AlgebraicValue::C).collect(),
                    })
                }),
            )
        }
        SpecResource::Token { name, arguments } => {
            let name = name.clone();
            (
                arguments.clone(),
                Box::new(move |arguments| {
                    Some(CResource::Token {
                        name: name.clone(),
                        arguments: arguments.into_iter().map(AlgebraicValue::C).collect(),
                    })
                }),
            )
        }
    };
    Ok(
        evaluate_spec_values_at_state_in(scope, &expressions, assumptions, budget)?
            .into_iter()
            .filter_map(|path| {
                build(path.values).map(|resource| (resource, path.facts, path.obligations))
            })
            .collect(),
    )
}

/// Whether a stated relation names a memory range whose byte extent this
/// context has already decided cannot be valid.
///
/// The separation counterpart of `reject_impossible_range_guards`, which does
/// this for a stated `owns`/`views` range. A range that runs backwards denotes
/// no bytes, so relating it to anything states nothing, and accepting it let
/// `separate(memory(a[s..t]), …)` be written with `s == i32::MAX` and
/// `t == -i32::MAX` — endpoints whose wrapping difference is a tidy `2`.
///
/// Reject a range already known invalid with the focused extent diagnostic.
/// Undecided guards remain conjuncts of the lowered separation proposition.
fn separation_extent_is_impossible(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    crate::kernel::stated_separation_extent_guards(proposition)
        .iter()
        .any(|guard| match guard {
            Proposition::ConditionIs(ConditionTerm::Constant(false), true) => true,
            Proposition::ConditionIs(condition, true) => {
                assumptions.decide(condition) == Some(false)
            }
            _ => false,
        })
}

/// Lowers a relation between two spec resources.
///
/// A separation names valid memory extents in every context. Relations over
/// opaque resources, and containment relations, contribute no range bounds.
fn lower_spec_resource_relation_at_state_in(
    scope: SpecScope<'_>,
    left: &SpecResource,
    right: &SpecResource,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
    relation: impl Fn(CResource, CResource) -> Proposition,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for (left, left_facts, left_obligations) in
        evaluate_spec_resource_at_state_in(scope, left, assumptions, budget)?
    {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for (right, right_facts, right_obligations) in
            evaluate_spec_resource_at_state_in(scope, right, &right_assumptions, budget)?
        {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &left_facts,
                &left_obligations,
                &right_facts,
                &right_obligations,
                assumptions,
                &right_assumptions,
            ) else {
                continue;
            };
            let mut proposition = relation(left.clone(), right);
            if separation_extent_is_impossible(&proposition, assumptions) {
                budget.record_dropped_relation_range_extent();
                continue;
            }
            // An assumption provides every conjunct; a goal establishes all
            // of them. The same lowering serves contracts and theorem proofs.
            for guard in crate::kernel::stated_separation_extent_bounds(&proposition) {
                proposition = Proposition::And(Box::new(proposition), Box::new(guard));
            }
            paths.push(SpecPropositionPath {
                introductions: Vec::new(),
                proposition,
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

#[allow(clippy::too_many_arguments)]
fn lower_spec_memory_loadable_at_state_in(
    scope: SpecScope<'_>,
    memory: &SpecMemory,
    base: &SpecExpression,
    start: &SpecExpression,
    end: &SpecExpression,
    element_width: u32,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
    enforce_range_guards: bool,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    let memory = match memory {
        SpecMemory::Current => state.memory(),
        SpecMemory::FunctionEntry | SpecMemory::LoopEntry => match loop_entry_state {
            Some(entry) => entry.memory(),
            None => return Ok(Vec::new()),
        },
        SpecMemory::Fixed(memory) => memory,
    };
    Ok(evaluate_spec_values_at_state_in(
        scope,
        &[base.clone(), start.clone(), end.clone()],
        assumptions,
        budget,
    )?
    .into_iter()
    .filter_map(|path| match path.values.as_slice() {
        // The proposition describes the same native range as a resource
        // clause, including its extent guards, and states the wide liveness
        // fact a contract holding it is given. Neither endpoint is a signed
        // observation of the source count.
        [CValue::Pointer(base), start, end]
            if crate::kernel::wide_range_bounds(start, end).is_some() =>
        {
            let (start, end) = crate::kernel::wide_range_bounds(start, end)?;
            let range = CMemoryRange::new_wide(
                Pointer {
                    block: base.block.clone(),
                    offset: crate::kernel::eval::canonical_offset_term(&base.offset),
                },
                crate::kernel::eval::canonical_term(&start),
                crate::kernel::eval::canonical_term(&end),
                element_width,
            );
            let mut obligations = path.obligations;
            if enforce_range_guards {
                for guard in crate::kernel::memory_range_extent_guards(&range) {
                    add_proof_obligation(&mut obligations, assumptions, guard)?;
                }
            }
            Some(SpecPropositionPath {
                introductions: Vec::new(),
                proposition: range.loadable_fact(memory),
                facts: path.facts,
                obligations,
            })
        }
        // A range from constant zero to a constant unsigned 64-bit bound is
        // wide here too, so the proposition is the one a symbolic bound
        // lowers to once that bound is substituted by the constant.
        [
            CValue::Pointer(base),
            CValue::Int32(Bitvector32Term::Constant(0)),
            CValue::UInt64(end),
        ] => {
            let range = CMemoryRange::new_wide(
                Pointer {
                    block: base.block.clone(),
                    offset: crate::kernel::eval::canonical_offset_term(&base.offset),
                },
                Bitvector32Term::UInt64Constant(0),
                crate::kernel::eval::canonical_term(end),
                element_width,
            );
            let mut obligations = path.obligations;
            if enforce_range_guards {
                for guard in crate::kernel::memory_range_extent_guards(&range) {
                    add_proof_obligation(&mut obligations, assumptions, guard)?;
                }
            }
            Some(SpecPropositionPath {
                introductions: Vec::new(),
                proposition: range.loadable_fact(memory),
                facts: path.facts,
                obligations,
            })
        }
        [
            CValue::Pointer(base),
            CValue::Int32(start),
            CValue::Int32(end),
        ] => {
            // Terms are canonical at creation: the same segment lowered
            // anywhere is one proposition.
            let range_start = start.clone();
            let range_end = end.clone();
            let mut discarded_facts = ExecutionFacts::new();
            let start =
                crate::kernel::canonicalized_offset_index_term(start.clone(), &mut discarded_facts);
            let base = Pointer {
                block: base.block.clone(),
                offset: canonical_offset_sum(
                    base.offset.clone(),
                    canonical_scaled_offset(start, i64::from(element_width)),
                ),
            };
            let mut obligations = path.obligations;
            if enforce_range_guards {
                match crate::kernel::memory_range_byte_count_extent(
                    range_start.clone(),
                    range_end.clone(),
                    element_width,
                ) {
                    crate::kernel::MemoryRangeExtent::ConstantValid => {}
                    // A constant range that is reversed or wider than a `u32`
                    // byte extent prunes this path. Record why: the surviving
                    // path count alone said only "no path".
                    crate::kernel::MemoryRangeExtent::ConstantInvalid {
                        element_count,
                        byte_limit,
                    } => {
                        budget.record_dropped_range_extent(
                            element_count,
                            element_width,
                            byte_limit,
                        );
                        return None;
                    }
                    // The extent half of the stated range. It is owed here
                    // like any other side condition of the lowering, and a
                    // site assuming the lowered proposition as a hypothesis
                    // proved elsewhere assumes it with the rest.
                    crate::kernel::MemoryRangeExtent::Guards(guards) => {
                        // Past one-byte elements the unsigned `fits` half is
                        // the signed count bound, which is the spelling a
                        // proof can write and a refusal can print.
                        let guards = if element_width > 1 {
                            crate::kernel::memory_range_extent_guards(
                                &CMemoryRange::new_with_element_width(
                                    base.clone(),
                                    range_start.clone(),
                                    range_end.clone(),
                                    element_width,
                                ),
                            )
                        } else {
                            guards
                        };
                        let ordered = Proposition::ConditionIs(
                            ConditionTerm::signed_less_equal(
                                range_start.clone(),
                                range_end.clone(),
                            ),
                            true,
                        );
                        for guard in guards {
                            // A guard this context refutes prunes the path;
                            // record which, as the constant case does.
                            let reversed = guard == ordered;
                            if add_proof_obligation(&mut obligations, assumptions, guard).is_none()
                            {
                                budget.record_dropped_refuted_range_extent(reversed);
                                return None;
                            }
                        }
                    }
                }
            }
            Some(SpecPropositionPath {
                introductions: Vec::new(),
                proposition: Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base,
                    bytes: crate::kernel::memory_range_byte_count(
                        range_start,
                        range_end,
                        element_width,
                    ),
                    wide: false,
                },
                facts: path.facts,
                obligations,
            })
        }
        _ => None,
    })
    .collect())
}

fn evaluate_spec_integer_pure_function_application_paths_in(
    scope: SpecScope<'_>,
    name: &str,
    arguments: &[SpecPureFunctionArgument],
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    let mut paths = vec![(Vec::new(), ExecutionFacts::new(), Vec::new())];
    for argument in arguments {
        let mut next = Vec::new();
        for (values, facts, obligations) in paths {
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            let argument_paths = evaluate_spec_pure_function_argument_paths_in(
                scope,
                argument,
                &path_assumptions,
                budget,
            )?;
            let domain = argument_paths
                .iter()
                .map(|path| {
                    proposition_and_all(
                        path.facts
                            .iter()
                            .map(|fact| fact.proposition().clone())
                            .chain(
                                path.obligations
                                    .iter()
                                    .map(|obligation| obligation.proposition().clone()),
                            )
                            .collect(),
                    )
                })
                .reduce(|left, right| Proposition::Or(Box::new(left), Box::new(right)));
            let argument_paths = argument_paths
                .into_iter()
                .map(|mut path| {
                    if let Some(domain) = domain.clone() {
                        retain_required_integer_obligation(
                            &mut path.obligations,
                            assumptions,
                            domain,
                        );
                    }
                    path
                })
                .collect::<Vec<_>>();
            let single_path = argument_paths.len() == 1;
            let mut prefix = Some(values);
            for (index, argument_path) in argument_paths.into_iter().enumerate() {
                if let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &argument_path.facts,
                        &argument_path.obligations,
                        assumptions,
                    )
                {
                    let mut merged_values = if single_path && index == 0 {
                        prefix.take().expect("single argument path owns its prefix")
                    } else {
                        prefix
                            .as_ref()
                            .expect("branched argument paths retain prefix")
                            .clone()
                    };
                    merged_values.push(argument_path.value);
                    next.push((merged_values, merged_facts, merged_obligations));
                }
            }
        }
        paths = next;
    }
    Ok(paths
        .into_iter()
        .map(|(arguments, facts, obligations)| SpecIntegerPath {
            value: IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                name.to_string(),
                arguments,
            )),
            facts,
            obligations,
        })
        .collect())
}

/// An element index scaled to bytes, folded when the index is a constant.
fn canonical_scaled_offset(value: Bitvector32Term, byte_width: i64) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}

/// `left + right` on offsets with constants folded and zero addends dropped.
fn canonical_offset_sum(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

fn lower_spec_disjunction_at_state_in(
    scope: SpecScope<'_>,
    left: &SpecProposition,
    right: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        left,
        assumptions,
        budget,
    )? {
        // The right side matters only where the left fails, as with
        // `implies`: it is lowered assuming the left's negation and its
        // obligations are owed only there. A guard such as
        // `b == 0 or a <= MAX / b` then lowers as written whatever the facts.
        let negated_left = match &left_path.proposition {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations)
                .assume_proposition(negated_left);
        let right_paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
            scope,
            right,
            &right_assumptions,
            budget,
        )?;
        // A literally true left side leaves no case for the right, which then
        // need not denote anything (`0u32 == 0u32 or a <= MAX / 0u32`).
        if right_paths.is_empty()
            && matches!(
                &left_path.proposition,
                Proposition::ConditionIs(ConditionTerm::Constant(value), expected)
                    if value == expected
            )
        {
            paths.push(left_path);
            continue;
        }
        if right_paths.is_empty() {
            return Err(ExecutionLimit::DisjunctionRightUndefined);
        }
        for right_path in right_paths {
            let guarded_right_obligations = right_path
                .obligations
                .iter()
                .cloned()
                .map(|obligation| {
                    let left = left_path.proposition.clone();
                    obligation.map_proposition(|proposition| {
                        Proposition::Or(Box::new(left), Box::new(proposition))
                    })
                })
                .collect::<Vec<_>>();
            if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &guarded_right_obligations,
                assumptions,
            ) {
                paths.push(SpecPropositionPath {
                    introductions: Vec::new(),
                    proposition: Proposition::Or(
                        Box::new(left_path.proposition.clone()),
                        Box::new(right_path.proposition),
                    ),
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

fn lower_spec_comparison_proposition_at_state_in(
    scope: SpecScope<'_>,
    left: &SpecExpression,
    operator: CComparisonOperator,
    right: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    if matches!(left, SpecExpression::AlgebraicMatch { .. })
        && left == right
        && matches!(
            operator,
            CComparisonOperator::Equal | CComparisonOperator::NotEqual
        )
    {
        return Ok(vec![SpecPropositionPath {
            introductions: Vec::new(),
            proposition: Proposition::ConditionIs(
                ConditionTerm::Constant(operator == CComparisonOperator::Equal),
                true,
            ),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }]);
    }
    let mut paths = Vec::new();
    let left_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        left,
        assumptions,
        budget,
    )?;
    let left_path_count = left_paths.len();
    let mut right_path_count = 0usize;
    let mut merge_failure_count = 0usize;
    let mut rejected_comparison = None;
    for left_path in left_paths {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        let right_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            right,
            &right_assumptions,
            budget,
        )?;
        right_path_count = right_path_count.saturating_add(right_paths.len());
        for right_path in right_paths {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
                &right_assumptions,
            ) else {
                merge_failure_count = merge_failure_count.saturating_add(1);
                continue;
            };
            let bool_comparison =
                bool_comparison_proposition(&left_path.value, operator, &right_path.value)
                    .transpose()?;
            if let Some(proposition) = bool_comparison.or_else(|| {
                c_value_comparison_proposition(&left_path.value, operator, &right_path.value)
            }) {
                paths.push(SpecPropositionPath {
                    introductions: Vec::new(),
                    proposition,
                    facts,
                    obligations,
                });
            } else {
                rejected_comparison.get_or_insert((
                    left_path.value.c_type(),
                    operator,
                    right_path.value.c_type(),
                ));
            }
        }
    }
    if paths.is_empty()
        && let Some(comparison) = rejected_comparison
    {
        budget.dropped_comparison.get_or_insert(comparison);
    }
    if paths.is_empty() && crate::instrumentation::enabled() {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
            format!(
                "spec comparison produced no paths: {left_path_count} left paths, {right_path_count} right paths, {merge_failure_count} inconsistent merges"
            ),
        ));
    }
    Ok(paths)
}

fn lower_spec_predicate_proposition_at_state_in(
    scope: SpecScope<'_>,
    name: &str,
    arguments: &[SpecPredicateArgument],
    resource_state_dependent: bool,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    if name == MUTEX_HELD_PREDICATE_NAME {
        let [SpecPredicateArgument::Value(mutex)] = arguments else {
            return Ok(vec![invalid_mutex_held_path(
                Vec::new().into(),
                Vec::new(),
                "held expects one mutex pointer",
            )]);
        };
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            mutex,
            assumptions,
            budget,
        )?;
        return Ok(paths
            .into_iter()
            .map(|path| {
                let CValue::Pointer(mutex) = path.value else {
                    return invalid_mutex_held_path(
                        path.facts,
                        path.obligations,
                        "held expects one mutex pointer",
                    );
                };
                if state.preserves_mutex_protocols
                    && (state.mutex_ledger.is_none() || state.opaque_mutex_acquisitions.is_some())
                {
                    let guard = super::mutexes::guard_resource(state, mutex.pointer(), true)
                        .expect("abstract guard description");
                    // The guard is matched as written: the facts never make
                    // an aliased mutex held.
                    if state
                        .resources
                        .satisfies_fact(&guard, &PureFactContext::new())
                    {
                        return SpecPropositionPath {
                            introductions: Vec::new(),
                            proposition: Proposition::ConditionIs(
                                ConditionTerm::Constant(true),
                                true,
                            ),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    }
                    return invalid_mutex_held_path(
                        path.facts,
                        path.obligations,
                        "held cannot inspect an opaque contract protocol",
                    );
                }
                let held = state
                    .mutex_ledger
                    .as_ref()
                    .map_or(ConditionTerm::Constant(false), |ledger| {
                        ledger.held_condition(mutex.pointer())
                    });
                SpecPropositionPath {
                    introductions: Vec::new(),
                    proposition: Proposition::ConditionIs(held, true),
                    facts: path.facts,
                    obligations: path.obligations,
                }
            })
            .collect());
    }
    // A function-contract fact describes the behavior of its pointer value;
    // it is independent of the caller's current resource-population snapshot.
    // Keeping the uniform predicate state argument canonical lets a closed
    // pure theorem establish the same fact at every later application site.
    let predicate_state = if !resource_state_dependent
        || CFunctionContract::surface_name_from_predicate(name).is_some()
    {
        CState::new()
    } else {
        state.resource_state_snapshot()
    };
    let mut paths = vec![SpecPropositionPath {
        introductions: Vec::new(),
        proposition: Proposition::Predicate {
            name: name.to_string(),
            arguments: vec![Term::CState(Box::new(predicate_state))],
        },
        facts: Vec::new().into(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let (expression, memory) = match argument {
            SpecPredicateArgument::Value(expression) => (expression, None),
            SpecPredicateArgument::ArrayRef { memory, pointer } => (pointer, Some(memory)),
        };
        let argument_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            expression,
            assumptions,
            budget,
        )?;
        let mut next_paths = Vec::new();
        for prefix_path in paths {
            let path_assumptions = assumptions_with_path_context(
                assumptions,
                &prefix_path.facts,
                &prefix_path.obligations,
            );
            for argument_path in &argument_paths {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &prefix_path.facts,
                    &prefix_path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    &path_assumptions,
                ) else {
                    continue;
                };
                let Proposition::Predicate {
                    name,
                    mut arguments,
                } = prefix_path.proposition.clone()
                else {
                    unreachable!("predicate lowering should carry predicate propositions")
                };
                if let Some(memory) = memory {
                    let memory = match memory {
                        SpecMemory::Current => state.memory(),
                        SpecMemory::FunctionEntry | SpecMemory::LoopEntry => {
                            let Some(entry_state) = loop_entry_state else {
                                continue;
                            };
                            entry_state.memory()
                        }
                        SpecMemory::Fixed(memory) => memory,
                    };
                    arguments.push(Term::CMemory(memory.clone()));
                }
                arguments.push(Term::CValue(argument_path.value.clone()));
                next_paths.push(SpecPropositionPath {
                    introductions: Vec::new(),
                    proposition: Proposition::Predicate { name, arguments },
                    facts,
                    obligations,
                });
            }
        }
        paths = next_paths;
    }

    if name == SAME_OBJECT_PREDICATE_NAME {
        for path in &mut paths {
            let Proposition::Predicate { arguments, .. } = &path.proposition else {
                unreachable!("predicate lowering retains its proposition carrier")
            };
            let [
                Term::CState(_),
                Term::CValue(CValue::Pointer(left)),
                Term::CValue(CValue::Pointer(right)),
            ] = arguments.as_slice()
            else {
                return Ok(Vec::new());
            };
            if !left.c_type().is_object_pointer() || !right.c_type().is_object_pointer() {
                return Ok(Vec::new());
            }
            path.proposition = pointer_same_object_proposition(left.pointer(), right.pointer());
        }
    }
    Ok(paths)
}

fn invalid_mutex_held_path(
    facts: ExecutionFacts,
    mut obligations: Vec<ProofObligation>,
    context: &str,
) -> SpecPropositionPath {
    let refusal = super::loops::false_equals_true_proposition();
    obligations
        .push(ProofObligation::verification_condition(refusal.clone()).with_context(context));
    SpecPropositionPath {
        introductions: Vec::new(),
        proposition: refusal,
        facts,
        obligations,
    }
}

/// Evaluates one specification expression with explicit algebraic bindings
/// and no loop-entry snapshot. This is the shape a declared pure function
/// body is evaluated in: its parameters are the bindings and its locals.
fn evaluate_spec_expression_paths_with_bindings_in(
    state: &CState,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::new(state, None, algebraic_bindings),
        expression,
        assumptions,
        budget,
    )
}

/// One lowered Integer specification expression's values at `state`.
///
/// A `decreases` component names no state of its own, so there is no
/// loop-entry snapshot and no algebraic binding to supply: the kernel picks
/// the state and this reads the one declared expression there.
fn evaluate_spec_integer_measure_paths_in(
    state: &CState,
    expression: &SpecIntegerExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(state, None),
        expression,
        assumptions,
        budget,
    )
}

fn evaluate_spec_expression_paths_with_loop_entry_in(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(state, loop_entry_state),
        expression,
        assumptions,
        budget,
    )
}

fn evaluate_spec_expression_paths_with_algebraic_bindings_in(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut right_operands = Vec::new();
    let mut current = expression;
    while let SpecExpression::Add(left, right) = current {
        if !matches!(right.as_ref(), SpecExpression::Value(_)) {
            break;
        }
        right_operands.push(right.as_ref());
        current = left;
    }
    if right_operands.len() > 128 && matches!(current, SpecExpression::Value(_)) {
        return evaluate_spec_add_chain_paths_in(
            scope,
            current,
            &right_operands,
            assumptions,
            budget,
        );
    }
    // Only the explicit cast operand reads a complete C representation.
    // Pure functions, model fields and mathematical lets remain numeric.
    let saved = budget.pointer_cast_operand;
    budget.pointer_cast_operand &= matches!(
        expression,
        SpecExpression::CExpression(_)
            | SpecExpression::MemoryLoad { .. }
            | SpecExpression::AggregateFieldValue { .. }
            | SpecExpression::Value(_)
            | SpecExpression::LoopEntrySnapshot(_)
            | SpecExpression::Cast(_, _)
            | SpecExpression::Add(_, _)
            | SpecExpression::BitwiseAnd(_, _)
            | SpecExpression::BitwiseOr(_, _)
            | SpecExpression::BitwiseNot(_)
    );
    let keep_representation = budget.pointer_cast_operand;
    let _word_representation =
        keep_representation.then(|| crate::kernel::eval::WordRepresentationScope::enter(true));
    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_one_in(
        scope,
        expression,
        assumptions,
        budget,
    );
    budget.pointer_cast_operand = saved;
    let paths = paths?;
    if keep_representation {
        return Ok(paths);
    }
    // Integer specifications observe mathematical values, not the hidden
    // representation of a complete C word. Model congruence cannot copy it.
    Ok(paths
        .into_iter()
        .map(|mut path| {
            path.value = path.value.numeric_value().clone();
            path
        })
        .collect())
}

fn evaluate_spec_add_chain_paths_in(
    scope: SpecScope<'_>,
    base: &SpecExpression,
    right_operands: &[&SpecExpression],
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let state = scope.state;
    let mut paths = evaluate_spec_expression_paths_with_algebraic_bindings_one_in(
        scope,
        base,
        assumptions,
        budget,
    )?;
    for right in right_operands.iter().rev() {
        budget.consume_expression_step()?;
        let mut next = Vec::new();
        for left_path in paths {
            let right_assumptions = assumptions_with_path_context(
                assumptions,
                &left_path.facts,
                &left_path.obligations,
            );
            for right_path in evaluate_spec_expression_paths_with_algebraic_bindings_one_in(
                scope,
                right,
                &right_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &left_path.facts,
                    &left_path.obligations,
                    &right_path.facts,
                    &right_path.obligations,
                    assumptions,
                    &right_assumptions,
                ) else {
                    continue;
                };
                next.extend(spec_value_paths_in(
                    apply_spec_arithmetic(
                        left_path.value.clone(),
                        right_path.value,
                        facts,
                        obligations,
                        assumptions,
                        |left, right, facts, obligations, context| {
                            apply_c_add(state, left, right, None, None, facts, obligations, context)
                        },
                    ),
                    budget,
                ));
            }
        }
        paths = next;
    }
    Ok(paths)
}

/// Rebase only the syntactic object projection. A loaded/aliased C pointer
/// cannot use this operation to gain access to a retained logical value.
fn aggregate_projection_pointer(
    expression: &SpecExpression,
    parameter: &str,
    slot: &Pointer,
) -> Option<SpecExpression> {
    match expression {
        SpecExpression::CExpression(CExpression::Variable(name)) if name == parameter => {
            Some(SpecExpression::Value(CValue::pointer(slot.clone())))
        }
        SpecExpression::Subobject { pointer, width } => Some(SpecExpression::Subobject {
            pointer: Box::new(aggregate_projection_pointer(pointer, parameter, slot)?),
            width: *width,
        }),
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => Some(SpecExpression::PointerOffset {
            pointer: Box::new(aggregate_projection_pointer(pointer, parameter, slot)?),
            elements: elements.clone(),
            byte_width: *byte_width,
        }),
        _ => None,
    }
}

#[cfg(test)]
mod aggregate_value_tests;

/// Keep the optional Count-state selection off the recursive expression
/// evaluator's stack. Ordinary expressions do not need an owned CState.
fn evaluate_resource_count_paths(
    scope: SpecScope<'_>,
    name: &str,
    arguments: &[Option<SpecExpression>],
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    let algebraic_bindings = scope.algebraic_bindings;
    // A predicate records immutable observations, not execution custody. Restore
    // its captured read witness only inside this evaluator; no resource step
    // sees this context, and the numeric model remains the captured ledger.
    let predicate_state = state
        .population_effects
        .predicate_count_permissions
        .as_ref()
        .map(|permissions| {
            let mut observed = state.clone();
            observed.resources = permissions.0.as_ref().clone();
            std::sync::Arc::make_mut(&mut observed.population_effects)
                .predicate_count_permissions = None;
            observed
        });
    let state = predicate_state.as_ref().unwrap_or(state);
    let mut argument_paths = vec![(
        Vec::<Option<AlgebraicValue>>::new(),
        ExecutionFacts::new(),
        Vec::new(),
    )];
    for argument in arguments {
        let mut next = Vec::new();
        for (values, facts, obligations) in argument_paths {
            let Some(argument) = argument else {
                let mut next_values = values;
                next_values.push(None);
                next.push((next_values, facts, obligations));
                continue;
            };
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            for argument_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                argument,
                &path_assumptions,
                budget,
            )? {
                let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations_under(
                        &facts,
                        &obligations,
                        &argument_path.facts,
                        &argument_path.obligations,
                        assumptions,
                        &path_assumptions,
                    )
                else {
                    continue;
                };
                let mut next_values = values.clone();
                next_values.push(Some(AlgebraicValue::C(argument_path.value)));
                next.push((next_values, merged_facts, merged_obligations));
            }
        }
        argument_paths = next;
    }
    argument_paths
        .into_iter()
        .map(|(arguments, mut facts, mut obligations)| {
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            {
                let Some(Some(AlgebraicValue::C(CValue::Pointer(_)))) = arguments.first() else {
                    return Err(ExecutionLimit::AuthorityCountNeedsExactPointer);
                };
                let exact = arguments.len() > 1 && arguments.iter().all(Option::is_some);
                if !exact && arguments.iter().skip(1).any(Option::is_some) {
                    return Err(ExecutionLimit::AuthorityCountNeedsExactPointer);
                }
                let member = exact.then(|| {
                    ResourceDescription::new(
                        name.to_owned(),
                        arguments
                            .iter()
                            .map(|value| value.clone().expect("exact argument"))
                            .collect::<Vec<_>>()
                            .into(),
                        ResourceFieldSchema::new(vec![]).expect("empty resource schema"),
                    )
                });
                let description = ResourceDescription::new(
                    name.to_owned(),
                    vec![arguments[0].clone().expect("checked anchor")].into(),
                    ResourceFieldSchema::new(vec![]).expect("empty resource schema"),
                );
                let description = if arguments.len() > 1 {
                    description
                        .with_population_arity(arguments.len())
                        .map_err(|_| ExecutionLimit::AuthorityCountNeedsExactPointer)?
                } else {
                    description
                };
                let creation = state
                    .population_effects
                    .creation
                    .as_ref()
                    .ok_or(ExecutionLimit::AuthorityCountNeedsOwnership)?;
                // Count observes an already owned authority; pointer equality
                // never creates or transfers one. The anchor is used as
                // written, authenticating the held description in the live
                // ledger before using its count.
                let owned_description = |candidate: &ResourceDescription| {
                    let candidate = creation.population_type_description(candidate);
                    let required =
                        CResourceFact::own(CResource::PopulationAuthority(candidate.clone()));
                    state
                        .resources()
                        .directly_supporting_fact(&required, &path_assumptions)
                        .and_then(|fact| fact.owned_resource())
                        .and_then(|resource| match resource {
                            CResource::PopulationAuthority(owned)
                                if creation.owns_population_authority(owned) =>
                            {
                                Some(owned.clone())
                            }
                            _ => None,
                        })
                };
                let canonical = owned_description(&description);
                let description =
                    canonical.unwrap_or_else(|| creation.population_type_description(&description));
                let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
                    return Err(ExecutionLimit::AuthorityCountNeedsExactPointer);
                };
                let anchor = pointer.pointer();
                // Consuming an authority after its population is proved empty
                // preserves that exact zero as an immutable observation. It
                // does not restore ownership or permission to change members.
                if creation.checked_empty_population(&description) {
                    return Ok(SpecExpressionPath {
                        value: CValue::Int32(Bitvector32Term::Constant(0)),
                        facts,
                        obligations,
                    });
                }
                // An outstanding locked worker changes this population at an
                // unknown time before its join, so no total is current.
                if state
                    .thread_ledger
                    .as_ref()
                    .is_some_and(|ledger| ledger.defers_population_change(&description))
                {
                    return Err(ExecutionLimit::AuthorityCountPendingLockedWorker);
                }
                let authority =
                    CResourceFact::own(CResource::PopulationAuthority(description.clone()));
                if !state
                    .resources
                    .satisfies_fact(&authority, &path_assumptions)
                    && !creation.checked_control_count_permission(
                        state,
                        &description,
                        &path_assumptions,
                    )
                {
                    return Err(
                        if state
                            .thread_ledger
                            .as_ref()
                            .is_some_and(|ledger| ledger.lends_population_authority(&description))
                        {
                            ExecutionLimit::AuthorityCountLentToWorker
                        } else {
                            ExecutionLimit::AuthorityCountNeedsOwnership
                        },
                    );
                }
                let symbolic = if let Some(member) = member {
                    let mut arguments = member.arguments().to_vec();
                    arguments[0] = description.arguments()[0].clone();
                    let member = ResourceDescription::new(
                        name.to_owned(),
                        arguments.into(),
                        description.schema().clone(),
                    );
                    Some(
                        creation
                            .observe_exact_member(&member)
                            .map_err(|_| ExecutionLimit::AuthorityCountNeedsResolvedMember)?,
                    )
                } else {
                    creation.observe_symbolic(&description)
                };
                if let Some(symbolic) = symbolic {
                    let entry = symbolic.entry_count.clone();
                    // An imported control's checked equality to a population
                    // count entails this bound, including any member owned by
                    // the helper at entry. It is not an arbitrary C assumption.
                    let entry_owned = symbolic
                        .entry_symbolic_members
                        .clone()
                        .unwrap_or(Bitvector32Term::Constant(symbolic.entry_owned_members));
                    let minimum = Proposition::ConditionIs(
                        ConditionTerm::signed_greater_equal(entry.clone(), entry_owned),
                        true,
                    );
                    facts.push(ExecutionPureFact::certified(minimum.clone()));
                    // The composed quantity is itself signed arithmetic. A
                    // wrapped inner sum must not disappear inside entry + delta.
                    if let Some((true, quantity)) = &symbolic.symbolic_delta
                        && symbolic.delta > 0
                    {
                        let overflow = ConditionTerm::signed_add_overflows(
                            quantity.clone(),
                            Bitvector32Term::Constant(symbolic.delta as u32),
                        );
                        let no_overflow = Proposition::ConditionIs(overflow.clone(), false);
                        if !path_assumptions.proves_exact(&no_overflow)
                            && PureFactContext::decide_intrinsically(&overflow) != Some(false)
                            && path_assumptions.decide(&overflow) != Some(false)
                        {
                            obligations.push(
                                ProofObligation::verification_condition(no_overflow)
                                    .with_context("composed member quantity fits in int32"),
                            );
                        }
                    }
                    let delta = symbolic.combined_delta();
                    let count = match delta {
                        None => entry,
                        Some((true, quantity)) => {
                            let overflow = ConditionTerm::signed_add_overflows(
                                entry.clone(),
                                quantity.clone(),
                            );
                            let no_overflow = Proposition::ConditionIs(overflow.clone(), false);
                            let bounded = path_assumptions.assume_proposition(minimum);
                            if !bounded.proves_exact(&no_overflow)
                                && PureFactContext::decide_intrinsically(&overflow) != Some(false)
                                && bounded.decide(&overflow) != Some(false)
                                && !crate::kernel::api::checked_int32_reassociated_add_domain(
                                    &bounded,
                                    &no_overflow,
                                )
                            {
                                obligations.push(
                                    ProofObligation::verification_condition(no_overflow)
                                        .with_context("count(reference) fits in int32"),
                                );
                            }
                            Bitvector32Term::add(entry, quantity)
                        }
                        Some((false, quantity)) => {
                            let within = Proposition::ConditionIs(
                                ConditionTerm::signed_greater_equal(
                                    entry.clone(),
                                    quantity.clone(),
                                ),
                                true,
                            );
                            let bounded = path_assumptions.assume_proposition(minimum);
                            if !bounded.proves_exact(&within)
                                && bounded.decide(&ConditionTerm::signed_greater_equal(
                                    entry.clone(),
                                    quantity.clone(),
                                )) != Some(true)
                            {
                                obligations.push(
                                    ProofObligation::verification_condition(within)
                                        .with_context("count(reference) contains consumed members"),
                                );
                            }
                            Bitvector32Term::subtract(entry, quantity)
                        }
                    };
                    return Ok(SpecExpressionPath {
                        value: CValue::Int32(count),
                        facts,
                        obligations,
                    });
                }
                if anchor.offset != PointerOffsetTerm::Constant(0) {
                    return Err(ExecutionLimit::AuthorityCountNeedsExactPointer);
                }
                if creation.governing_authority(&description).as_ref() != Some(&description) {
                    return Err(ExecutionLimit::AuthorityCountNeedsOwnership);
                }
                let count = creation
                    .observe_term(&anchor.block, name)
                    .map_err(|_| ExecutionLimit::AuthorityCountNeedsOwnership)?;
                if let Some((base, quantity)) =
                    creation.observed_symbolic_batch(&anchor.block, name)
                {
                    facts.push(ExecutionPureFact::certified(Proposition::ConditionIs(
                        ConditionTerm::signed_add_overflows(
                            Bitvector32Term::Constant(base),
                            quantity,
                        ),
                        false,
                    )));
                }
                Ok(SpecExpressionPath {
                    value: CValue::Int32(count),
                    facts,
                    obligations,
                })
            }
        })
        .collect::<ExecutionResult<Vec<_>>>()
}

fn evaluate_spec_expression_paths_with_algebraic_bindings_one_in(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    let algebraic_bindings = scope.algebraic_bindings;
    budget.consume_expression_step()?;
    let paths = match expression {
        SpecExpression::AggregateFieldValue {
            parameter,
            pointer,
            value_type,
        } => {
            let entry = loop_entry_state
                .filter(|entry| entry.locals.aggregate_layout(parameter).is_some())
                .unwrap_or(state);
            let Some(CLocalBinding::AggregateObject { slot, .. }) = entry.locals.binding(parameter)
            else {
                // Requirement setup can bind the caller's aggregate image as
                // a plain pointer. It has no retired parameter value to expose.
                return evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    SpecScope::new(state, loop_entry_state, algebraic_bindings),
                    &SpecExpression::MemoryLoad {
                        memory: SpecMemory::Current,
                        pointer: pointer.clone(),
                        value_type: *value_type,
                    },
                    assumptions,
                    budget,
                );
            };
            let Some(pointer) = aggregate_projection_pointer(pointer, parameter, slot) else {
                return Ok(Vec::new());
            };
            // Current fields are read while storage exists. Once it ends,
            // the contract retains the value from entry, never its permission.
            // Contract validation separately refuses current reads of fields
            // modified by the body, as for ordinary by-value parameter claims.
            let memory = if state.memory.has_block(&slot.block) {
                state.memory()
            } else {
                entry.memory()
            };
            evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                &SpecExpression::MemoryLoad {
                    memory: SpecMemory::Fixed(memory.clone()),
                    pointer: Box::new(pointer),
                    value_type: *value_type,
                },
                assumptions,
                budget,
            )?
        }
        SpecExpression::IntegerToMachine { value, destination } => {
            let integer_paths = evaluate_spec_integer_expression_paths_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                value,
                assumptions,
                budget,
            )?;
            let (lower, upper) = integer_machine_bounds(*destination);
            let mut paths = Vec::new();
            for path in integer_paths {
                if let Some(value) = integer_constant_to_machine(&path.value, *destination) {
                    paths.push(SpecExpressionPath {
                        value,
                        facts: path.facts,
                        obligations: path.obligations,
                    });
                    continue;
                }
                if path.value.as_const().is_some() {
                    return Err(ExecutionLimit::Paths);
                }
                let mut obligations = path.obligations;
                let lower_bound = Proposition::ConditionIs(
                    ConditionTerm::integer_greater_equal(path.value.clone(), lower.clone()),
                    true,
                );
                let upper_bound = Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(path.value.clone(), upper.clone()),
                    true,
                );
                retain_required_integer_obligation(&mut obligations, assumptions, lower_bound);
                retain_required_integer_obligation(&mut obligations, assumptions, upper_bound);
                let value = c_value_from_bitvector_term(
                    destination.c_type(),
                    Bitvector32Term::IntegerToMachine {
                        value: path.value.into(),
                        destination: *destination,
                    },
                )
                .ok_or(ExecutionLimit::Paths)?;
                paths.push(SpecExpressionPath {
                    value,
                    facts: path.facts,
                    obligations,
                });
            }
            paths
        }
        SpecExpression::ResourceField { projection, c_type } => {
            let snapshot = if projection.at_entry {
                loop_entry_state.ok_or(ExecutionLimit::Paths)?
            } else {
                state
            };
            let Some(AlgebraicValue::C(value)) = snapshot
                .resource_instance_at_path(projection.identity, &projection.children)
                .and_then(|instance| instance.fields().get(projection.field_index))
            else {
                return Err(ExecutionLimit::ResourceFieldInstanceUnavailable);
            };
            if value.c_type() != *c_type {
                return Err(ExecutionLimit::Paths);
            }
            vec![SpecExpressionPath {
                value: value.clone(),
                facts: vec![].into(),
                obligations: vec![],
            }]
        }
        SpecExpression::Value(value) => vec![SpecExpressionPath {
            value: value.clone(),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            if !spec_scalar_match_arms_are_well_formed(&scrutinee.algebraic_type, arms) {
                return Err(ExecutionLimit::Paths);
            }
            let mut paths = Vec::new();
            for scrutinee_path in evaluate_spec_algebraic_at_state_with_bindings_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                scrutinee,
                assumptions,
                budget,
            )? {
                if !matches!(
                    scrutinee_path.value.node,
                    AlgebraicTermNode::Constructor { .. }
                ) {
                    let mut lowered_arms = Vec::with_capacity(arms.len());
                    let mut parameter_arms = Vec::new();
                    let mut result_type = None;
                    let facts = scrutinee_path.facts.clone();
                    let obligations = scrutinee_path.obligations.clone();
                    for arm in arms {
                        let Some(schema) = scrutinee_path
                            .value
                            .algebraic_type
                            .variants
                            .iter()
                            .find(|variant| variant.name == arm.variant)
                        else {
                            return Err(ExecutionLimit::Paths);
                        };
                        let bindings = symbolic_algebraic_match_binders_in(
                            &scrutinee_path.value.algebraic_type,
                            schema,
                            budget,
                        )?;
                        let mut body_state = state.clone();
                        let mut body_algebraic_bindings = algebraic_bindings.clone();
                        for (binding, value) in arm.bindings.iter().zip(&bindings) {
                            match value {
                                AlgebraicValue::C(value) => {
                                    body_state.locals.set(binding.clone(), value.clone());
                                }
                                AlgebraicValue::Integer(_) => {}
                                AlgebraicValue::Algebraic(value) => {
                                    body_algebraic_bindings.insert(binding.clone(), value.clone());
                                }
                            }
                        }
                        let body_assumptions =
                            assumptions_with_path_context(assumptions, &facts, &obligations);
                        let mut body_paths =
                            evaluate_spec_expression_paths_with_algebraic_bindings_in(
                                SpecScope::new(
                                    &body_state,
                                    loop_entry_state,
                                    &body_algebraic_bindings,
                                ),
                                &arm.body,
                                &body_assumptions,
                                budget,
                            )?;
                        let Some(body_path) = body_paths.pop() else {
                            return Err(ExecutionLimit::Paths);
                        };
                        if !body_paths.is_empty() {
                            return Err(ExecutionLimit::Paths);
                        }
                        // These side conditions would need to be guarded by the
                        // arm's constructor test. Reject instead of asserting them
                        // unconditionally beside the symbolic match term.
                        if body_path.facts.has_path_conditions()
                            || !body_path.obligations.is_empty()
                        {
                            return Err(ExecutionLimit::Paths);
                        }
                        let body_type = body_path.value.c_type();
                        if result_type.is_some_and(|expected| expected != body_type) {
                            return Err(ExecutionLimit::Paths);
                        }
                        result_type = Some(body_type);
                        // The only remaining body facts are derived read equations.
                        // They belong to this arm, not to the enclosing match.
                        if let CValue::Parameter(body) = body_path.value {
                            // A value of a Rust type parameter is a term of
                            // its type, so the match is one too.
                            parameter_arms.push(AlgebraicResultMatchArm {
                                binding_names: crate::kernel::BindingNames::written(&arm.bindings),
                                variant: arm.variant.clone(),
                                bindings,
                                body: *body,
                            });
                            continue;
                        }
                        let Some(body) = c_value_bitvector_term(&body_path.value) else {
                            return Err(ExecutionLimit::Paths);
                        };
                        lowered_arms.push(AlgebraicBitvectorMatchArm {
                            binding_names: crate::kernel::BindingNames::written(&arm.bindings),
                            variant: arm.variant.clone(),
                            bindings,
                            body,
                        });
                    }
                    let Some(result_type) = result_type else {
                        return Err(ExecutionLimit::Paths);
                    };
                    let value = if let CType::Parameter(name) = result_type {
                        CValue::Parameter(Box::new(AlgebraicTerm {
                            algebraic_type: name.algebraic_type(),
                            node: AlgebraicTermNode::Match {
                                scrutinee: Box::new(scrutinee_path.value),
                                arms: parameter_arms,
                            },
                        }))
                    } else {
                        c_value_from_bitvector_term(
                            result_type,
                            Bitvector32Term::AlgebraicMatch {
                                scrutinee: Box::new(scrutinee_path.value),
                                arms: lowered_arms,
                            },
                        )
                        .ok_or(ExecutionLimit::Paths)?
                    };
                    paths.push(SpecExpressionPath {
                        value,
                        facts,
                        obligations,
                    });
                    continue;
                }
                for case in algebraic_case_paths_in(&scrutinee_path.value, budget)? {
                    let Some(arm) = arms.iter().find(|arm| arm.variant == case.variant) else {
                        return Err(ExecutionLimit::Paths);
                    };
                    // Arms were checked against the scrutinee schema above;
                    // case construction supplies fields of those exact types.
                    // Re-inferring their carrier erases nominal pointer types.
                    if arm.bindings.len() != case.fields.len() {
                        return Err(ExecutionLimit::Paths);
                    }
                    let mut body_state = state.clone();
                    let mut body_algebraic_bindings = algebraic_bindings.clone();
                    for (binding, field) in arm.bindings.iter().zip(&case.fields) {
                        match field {
                            AlgebraicValue::C(field) => {
                                body_state.locals.set(binding.clone(), field.clone());
                            }
                            AlgebraicValue::Integer(_) => {}
                            AlgebraicValue::Algebraic(field) => {
                                body_algebraic_bindings.insert(binding.clone(), field.clone());
                            }
                        }
                    }
                    let Some((case_facts, case_obligations)) =
                        merge_execution_pure_facts_and_obligations(
                            &scrutinee_path.facts,
                            &scrutinee_path.obligations,
                            &case.facts,
                            &case.obligations,
                            assumptions,
                        )
                    else {
                        continue;
                    };
                    let body_assumptions =
                        assumptions_with_path_context(assumptions, &case_facts, &case_obligations);
                    for body_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                        SpecScope::new(&body_state, loop_entry_state, &body_algebraic_bindings),
                        &arm.body,
                        &body_assumptions,
                        budget,
                    )? {
                        if let Some((facts, obligations)) =
                            merge_execution_pure_facts_and_obligations_under(
                                &case_facts,
                                &case_obligations,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                &body_assumptions,
                            )
                        {
                            paths.push(SpecExpressionPath {
                                value: body_path.value,
                                facts,
                                obligations,
                            });
                        }
                    }
                }
            }
            paths
        }
        SpecExpression::CExpression(expression) => {
            let _specification = crate::kernel::eval::SpecificationReadScope::enter();
            spec_value_paths_in(
                evaluate_c_expression_paths(state, expression, assumptions, budget)?,
                budget,
            )
        }
        SpecExpression::CountedResourceCount { name, arguments } => evaluate_resource_count_paths(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            name,
            arguments,
            assumptions,
            budget,
        )?,
        SpecExpression::Add(left, right) => {
            let left_step_width = spec_expression_pointer_step_width(state, left);
            let right_step_width = spec_expression_pointer_step_width(state, right);
            evaluate_spec_scalar_binary_paths_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                left,
                right,
                assumptions,
                budget,
                |left, right, facts, obligations| {
                    apply_spec_arithmetic(
                        left,
                        right,
                        facts,
                        obligations,
                        assumptions,
                        |left, right, facts, obligations, context| {
                            apply_c_add(
                                state,
                                left,
                                right,
                                left_step_width,
                                right_step_width,
                                facts,
                                obligations,
                                context,
                            )
                        },
                    )
                },
            )?
        }
        SpecExpression::Subtract(left, right) => {
            let left_step_width = spec_expression_pointer_step_width(state, left);
            let right_step_width = spec_expression_pointer_step_width(state, right);
            evaluate_spec_scalar_binary_paths_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                left,
                right,
                assumptions,
                budget,
                |left, right, facts, obligations| {
                    apply_spec_arithmetic(
                        left,
                        right,
                        facts,
                        obligations,
                        assumptions,
                        |left, right, facts, obligations, context| {
                            apply_c_subtract(
                                state,
                                left,
                                right,
                                left_step_width,
                                right_step_width,
                                facts,
                                obligations,
                                context,
                            )
                        },
                    )
                },
            )?
        }
        SpecExpression::Multiply(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_spec_arithmetic(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    apply_c_multiply,
                )
            },
        )?,
        SpecExpression::Divide(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_spec_arithmetic(left, right, facts, obligations, assumptions, apply_c_divide)
            },
        )?,
        SpecExpression::Remainder(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_spec_arithmetic(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    apply_c_remainder,
                )
            },
        )?,
        SpecExpression::ShiftLeft(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::ShiftRight(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::BitwiseAnd(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::And,
                )
            },
        )?,
        SpecExpression::BitwiseOr(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Or,
                )
            },
        )?,
        SpecExpression::BitwiseXor(left, right) => evaluate_spec_scalar_binary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Xor,
                )
            },
        )?,
        SpecExpression::PointerCoercion(expression, target_type) => {
            evaluate_spec_scalar_unary_paths_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                expression,
                assumptions,
                budget,
                |value, facts, obligations| {
                    let outcome = match value {
                        CValue::Pointer(pointer)
                            if target_type.is_pointer()
                                && (*target_type != CType::VoidPointer
                                    || pointer.c_type().is_object_pointer()) =>
                        {
                            CExpressionOutcome::Value(CValue::Pointer(
                                pointer.with_type(*target_type),
                            ))
                        }
                        _ => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    };
                    vec![CExpressionPath {
                        outcome,
                        facts,
                        obligations,
                    }]
                },
            )?
        }
        SpecExpression::Cast(expression, target_type) => {
            let saved = budget.pointer_cast_operand;
            budget.pointer_cast_operand = target_type.is_pointer() || saved;
            let result = evaluate_spec_scalar_unary_paths_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                expression,
                assumptions,
                budget,
                |value, facts, mut obligations| {
                    // Rule C1: a specification `Bool`'s integer value at the
                    // target's format, `b as F`.
                    if let CValue::Bool(term) = &value
                        && let Some(condition) = term.bool_cast_operand()
                        && let Some(format) = MachineIntegerType::from_c_type(*target_type)
                        && let Some(cast) = c_value_from_bitvector_term(
                            *target_type,
                            Bitvector32Term::bool_cast(format, condition.clone()),
                        )
                    {
                        return vec![CExpressionPath {
                            outcome: CExpressionOutcome::Value(cast),
                            facts,
                            obligations,
                        }];
                    }
                    // A specification's cast is C's conversion, modulo 2^N,
                    // as the same cast in C source is; `to_T(...)` is the
                    // checked conversion.
                    let outcome = cast_c_value_to_type(
                        value,
                        *target_type,
                        crate::kernel::eval::IntegerConversion::Modular,
                        &mut obligations,
                        assumptions,
                    )
                    .map(CExpressionOutcome::Value)
                    .unwrap_or_else(CExpressionOutcome::RuntimeError);
                    vec![CExpressionPath {
                        outcome,
                        facts,
                        obligations,
                    }]
                },
            );
            budget.pointer_cast_operand = saved;
            result?
        }
        SpecExpression::BitwiseNot(expression) => evaluate_spec_scalar_unary_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            expression,
            assumptions,
            budget,
            apply_c_bitwise_not,
        )?,
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => evaluate_spec_if_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        )?,
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => evaluate_spec_range_fold_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            start,
            end,
            initial,
            accumulator,
            item,
            body,
            assumptions,
            budget,
        )?,
        SpecExpression::Let { name, value, body } => {
            let mut paths = Vec::new();
            for value_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                value,
                assumptions,
                budget,
            )? {
                let mut body_state = state.clone();
                body_state
                    .locals
                    .set(name.clone(), value_path.value.clone());
                let body_assumptions = assumptions_with_path_context(
                    assumptions,
                    &value_path.facts,
                    &value_path.obligations,
                );
                for body_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    SpecScope::new(&body_state, loop_entry_state, algebraic_bindings),
                    body,
                    &body_assumptions,
                    budget,
                )? {
                    if let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &value_path.facts,
                            &value_path.obligations,
                            &body_path.facts,
                            &body_path.obligations,
                            assumptions,
                            &body_assumptions,
                        )
                    {
                        paths.push(SpecExpressionPath {
                            value: body_path.value,
                            facts,
                            obligations,
                        });
                    }
                }
            }
            paths
        }
        SpecExpression::PureFunctionApplication {
            name,
            arguments,
            result_type,
            pointer_result,
            result_object_class,
        } => evaluate_spec_pure_function_application_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            name,
            arguments,
            *result_type,
            pointer_result.as_deref(),
            result_object_class.as_ref(),
            assumptions,
            budget,
        )?,
        SpecExpression::LoopEntrySnapshot(expression) => {
            if let Some(loop_entry_state) = loop_entry_state {
                evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    SpecScope::new(loop_entry_state, Some(loop_entry_state), algebraic_bindings),
                    expression,
                    assumptions,
                    budget,
                )?
            } else {
                Vec::new()
            }
        }
        SpecExpression::Subobject { pointer, width } => {
            evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                pointer,
                assumptions,
                budget,
            )?
            .into_iter()
            .filter_map(|mut path| {
                let CValue::Pointer(value) = path.value else {
                    return None;
                };
                path.value = CValue::Pointer(value.clone().with_extent(Some(SubobjectExtent {
                    start: value.pointer().clone(),
                    width: (*width).into(),
                })));
                Some(path)
            })
            .collect()
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => evaluate_spec_pointer_offset_paths_in(
            SpecScope::new(state, loop_entry_state, algebraic_bindings),
            pointer,
            elements,
            *byte_width,
            assumptions,
            budget,
        )?,
        SpecExpression::MemoryLoad {
            memory,
            pointer,
            value_type,
        } => {
            let mut paths = Vec::new();
            let entry_projection =
                if matches!(memory, SpecMemory::FunctionEntry | SpecMemory::LoopEntry) {
                    fn root(expression: &SpecExpression) -> Option<&str> {
                        match expression {
                            SpecExpression::CExpression(CExpression::Variable(name)) => Some(name),
                            SpecExpression::PointerOffset { pointer, .. } => root(pointer),
                            _ => None,
                        }
                    }
                    root(pointer).and_then(|name| {
                        let entry = loop_entry_state?;
                        let CLocalBinding::AggregateObject { slot, .. } =
                            entry.locals.binding(name)?
                        else {
                            return None;
                        };
                        aggregate_projection_pointer(pointer, name, slot)
                    })
                } else {
                    None
                };
            for pointer_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::new(state, loop_entry_state, algebraic_bindings),
                entry_projection.as_ref().unwrap_or(pointer),
                assumptions,
                budget,
            )? {
                let CValue::Pointer(pointer) = pointer_path.value else {
                    continue;
                };
                let pointer = pointer.into_pointer();
                let memory = match memory {
                    SpecMemory::Current => state.memory(),
                    SpecMemory::FunctionEntry => match loop_entry_state {
                        Some(entry_state) => entry_state.memory(),
                        None => continue,
                    },
                    SpecMemory::LoopEntry => match loop_entry_state {
                        Some(loop_entry_state) => loop_entry_state.memory(),
                        None => continue,
                    },
                    SpecMemory::Fixed(memory) => memory,
                };
                let mut obligations = pointer_path.obligations;
                if budget.checked_reads
                    && !PureFactContext::new().proves_memory_read_defined(
                        memory,
                        &pointer,
                        *value_type,
                    )
                {
                    obligations.push(ProofObligation::new(Proposition::CMemoryReadDefined {
                        memory: memory.clone(),
                        pointer: pointer.clone(),
                        value_type: *value_type,
                    }));
                }
                paths.extend(spec_value_paths_in(
                    crate::kernel::eval::evaluate_logical_memory_load_paths(
                        memory,
                        pointer,
                        *value_type,
                        pointer_path.facts,
                        obligations,
                        assumptions,
                    ),
                    budget,
                ));
            }
            paths
        }
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_spec_pure_function_application_paths_in(
    scope: SpecScope<'_>,
    name: &str,
    arguments: &[SpecPureFunctionArgument],
    result_type: CType,
    pointer_result: Option<&PurePointerResult>,
    result_object_class: Option<&crate::kernel::effective_type::CAccessClass>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = vec![(Vec::new(), ExecutionFacts::new(), Vec::new())];
    for argument in arguments {
        let mut next = Vec::new();
        for (values, facts, obligations) in paths {
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            for argument_path in evaluate_spec_pure_function_argument_paths_in(
                scope,
                argument,
                &path_assumptions,
                budget,
            )? {
                if let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations_under(
                        &facts,
                        &obligations,
                        &argument_path.facts,
                        &argument_path.obligations,
                        assumptions,
                        &path_assumptions,
                    )
                {
                    let mut merged_values = values.clone();
                    merged_values.push(argument_path.value);
                    next.push((merged_values, merged_facts, merged_obligations));
                }
            }
        }
        paths = next;
    }
    let mut results = Vec::new();
    for (arguments, facts, obligations) in paths {
        let value = if result_type.is_pointer() {
            let (all_null, object_class) = pure_pointer_result_class(pointer_result, &arguments);
            CValue::Pointer(
                CPointerValue::new(
                    if all_null {
                        Pointer::null()
                    } else {
                        Pointer {
                            block: PointerBlock::PureFunctionApplication(
                                SharedPureApplication::intern(name.to_string(), arguments),
                            ),
                            offset: PointerOffsetTerm::Constant(0),
                        }
                    },
                    result_type,
                )
                .with_declared_object_class(result_object_class.cloned())
                .with_object_type_evidence(object_class),
            )
        } else if let CType::Parameter(parameter) = result_type {
            // A value of an abstract type is an algebraic term: the
            // application is one of that type.
            CValue::Parameter(Box::new(AlgebraicTerm {
                algebraic_type: parameter.algebraic_type(),
                node: AlgebraicTermNode::PureFunctionApplication {
                    name: name.to_string(),
                    arguments,
                },
            }))
        } else if result_type == CType::Bool {
            // A `-> Bool` application is a `Bool` term of the kernel sort
            // (Stage 5), carried as its cast to `uint8` (rule C1).
            CValue::Bool(Bitvector32Term::bool_cast(
                MachineIntegerType::UInt8,
                ConditionTerm::bool_application(name, arguments),
            ))
        } else {
            c_value_from_bitvector_term(
                result_type,
                Bitvector32Term::ClickFunctionApplication {
                    name: name.to_string(),
                    arguments,
                },
            )
            .ok_or(ExecutionLimit::UnsupportedPureFunctionResult(result_type))?
        };
        results.push(SpecExpressionPath {
            value,
            facts,
            obligations,
        });
    }
    Ok(results)
}

/// Instantiate the body's pointer origins with this call's actual values.
/// A missing or conflicting origin keeps the result opaque and unclassified.
pub(super) fn pure_pointer_result_class(
    result: Option<&PurePointerResult>,
    arguments: &[PureFunctionArgument],
) -> (bool, Option<ObjectTypeEvidence>) {
    let Some(result) = result else {
        return (false, None);
    };
    if result.classes.len() > 1 {
        return (false, None);
    }
    let mut class = result
        .classes
        .first()
        .cloned()
        .map(ObjectTypeEvidence::from);
    let mut all_null = class.is_none();
    for index in &result.arguments {
        let Some(
            PureFunctionArgument::Value(CValue::Pointer(pointer))
            | PureFunctionArgument::ArrayRef {
                pointer: CValue::Pointer(pointer),
                ..
            },
        ) = arguments.get(*index)
        else {
            return (false, None);
        };
        if pointer.is_null() {
            continue;
        }
        all_null = false;
        let Some(argument_class) = pointer.object_origin_evidence().cloned() else {
            return (false, None);
        };
        if class
            .as_ref()
            .is_some_and(|class| class.class != argument_class.class)
        {
            return (false, None);
        }
        class = Some(match class {
            Some(class) => class.merge(&argument_class),
            None => argument_class,
        });
    }
    (all_null, class)
}

/// Retain original-class evidence, recover it at an exact declared block
/// base, or prove null. Incompatible evidence is replaced only for null;
/// a destination cast supplies no class.
pub(crate) fn refine_object_pointer_argument(
    value: &mut CValue,
    object_class: &crate::kernel::effective_type::CAccessClass,
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let CValue::Pointer(pointer) = value else {
        return false;
    };
    if pointer.is_null()
        || pointer
            .object_type_evidence()
            .is_some_and(|evidence| evidence.has_class(object_class))
    {
        return true;
    }
    if pointer.object_type_evidence().is_none()
        && (assumptions
            .equality_graph
            .has_object_type(pointer.pointer(), object_class)
            // A modular result may have a symbolic address while its checked
            // designation already names the actual declared object.
            || [pointer.pointer(), pointer.designation()]
                .into_iter()
                .any(|object| {
                    object.offset == PointerOffsetTerm::Constant(0)
                        && memory.declared_class(object).as_ref() == Some(object_class)
                })
            // A pointer the facts prove null meets the requirement too. It
            // keeps its written address rather than being respelled as null.
            || assumptions.decide(&ConditionTerm::pointer_equal(
                pointer.pointer().clone(),
                Pointer::null(),
            )) == Some(true))
    {
        *pointer = pointer
            .clone()
            .with_object_class(Some(object_class.clone()));
        return true;
    }
    false
}

fn evaluate_spec_pure_function_argument_paths_in(
    scope: SpecScope<'_>,
    argument: &SpecPureFunctionArgument,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPureFunctionArgumentPath>> {
    let state = scope.state;
    let loop_entry_state = scope.loop_entry_state;
    match argument {
        SpecPureFunctionArgument::ObjectPointer {
            argument,
            object_class,
        } => {
            let paths = evaluate_spec_pure_function_argument_paths_in(
                scope,
                argument,
                assumptions,
                budget,
            )?;
            Ok(paths
                .into_iter()
                .filter_map(|mut path| {
                    let value = match &mut path.value {
                        PureFunctionArgument::Value(value)
                        | PureFunctionArgument::ArrayRef { pointer: value, .. } => value,
                        _ => return None,
                    };
                    let context =
                        assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
                    if !refine_object_pointer_argument(
                        value,
                        object_class,
                        scope.state.memory(),
                        &context,
                    ) {
                        if !budget.recover_resource_call_types
                            || !matches!(value, CValue::Pointer(pointer)
                                if pointer.object_type_evidence().is_none())
                        {
                            return None;
                        }
                        // Only a held resource's selected body or an assumed
                        // interface proposition can introduce this domain.
                        // Existing incompatible evidence is never retyped, and
                        // a C cast never selects this mode.
                        *value = value
                            .clone()
                            .with_pointer_object_class(Some(object_class.clone()));
                    }
                    if budget.recover_resource_call_types {
                        path.facts.push(ExecutionPureFact::certified(
                            crate::kernel::object_types::checked_call_type_fact(
                                value,
                                object_class,
                            ),
                        ));
                    }
                    Some(path)
                })
                .collect())
        }
        SpecPureFunctionArgument::Integer(expression) => Ok(
            evaluate_spec_integer_expression_paths_in(scope, expression, assumptions, budget)?
                .into_iter()
                .map(|path| SpecPureFunctionArgumentPath {
                    value: PureFunctionArgument::Integer(path.value.into()),
                    facts: path.facts,
                    obligations: path.obligations,
                })
                .collect(),
        ),
        SpecPureFunctionArgument::Value(expression) => {
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                expression,
                assumptions,
                budget,
            )?;
            Ok(paths
                .into_iter()
                .map(|path| SpecPureFunctionArgumentPath {
                    value: PureFunctionArgument::Value(path.value),
                    facts: path.facts,
                    obligations: path.obligations,
                })
                .collect())
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            Ok(evaluate_spec_algebraic_at_state_with_bindings_in(
                scope,
                expression,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPureFunctionArgumentPath {
                value: PureFunctionArgument::Algebraic(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
        SpecPureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => {
            let memory = match memory {
                SpecMemory::Current => state.memory(),
                SpecMemory::FunctionEntry | SpecMemory::LoopEntry => {
                    let Some(entry) = loop_entry_state else {
                        return Ok(Vec::new());
                    };
                    entry.memory()
                }
                SpecMemory::Fixed(memory) => memory,
            };
            Ok(evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                pointer,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPureFunctionArgumentPath {
                value: PureFunctionArgument::ArrayRef {
                    // The argument names the snapshot it reads, and that
                    // snapshot is compared structurally, so the live one
                    // would make this argument -- and every fact about a
                    // function of it -- different after any step at all.
                    // `array_ref_argument_memory` gives the latest snapshot
                    // that still agrees with this one about everything the
                    // function can observe through this pointer, so a fact
                    // survives exactly the steps that cannot touch the array.
                    memory: array_ref_argument_memory(memory, &path.value),
                    pointer: path.value,
                    element_type: *element_type,
                },
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
    }
}

/// The snapshot an array argument at `pointer` names, given the state it was
/// evaluated at.
///
/// See [`crate::kernel::resource_tracker`] for
/// what the epoch guarantees and which derivation edges it crosses. An
/// argument that is not a pointer at all keeps the live snapshot, which is
/// always sound and merely as fragile as before; so does a block the walk
/// cannot separate from anything, because it then crosses no edge.
fn array_ref_argument_memory(memory: &CMemory, pointer: &CValue) -> CMemory {
    let CValue::Pointer(pointer) = pointer else {
        return memory.clone();
    };
    let interned = crate::kernel::intern_c_memory(memory.clone());
    crate::kernel::resource_tracker::last_same_point(
        crate::kernel::resource_tracker::Resource::Block(&pointer.pointer().block),
        &crate::kernel::resource_tracker::ProgramPoint::at(&interned),
    )
    .map(|point| point.memory().clone())
    .unwrap_or_else(|| memory.clone())
}

pub(in crate::kernel) fn c_value_bitvector_term(value: &CValue) -> Option<Bitvector32Term> {
    let value = value.numeric_value();
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Bool(term) => Some(term.clone()),
        CValue::Int8(term) => Some(term.clone()),
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Int128(term)
        | CValue::UInt128(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => Some(term.clone()),
        CValue::Void | CValue::Pointer(_) | CValue::Parameter(_) => None,
    }
}

fn integer_constant_to_machine(
    value: &IntegerTerm,
    destination: MachineIntegerType,
) -> Option<CValue> {
    let value = MachineIntegerConstant::from_integer(destination.format(), value.as_const()?)?;
    destination.constant_value(value)
}

pub(super) fn integer_machine_bounds(
    destination: MachineIntegerType,
) -> (IntegerTerm, IntegerTerm) {
    let (lower, upper) = destination.format().bounds();
    (IntegerTerm::constant(lower), IntegerTerm::constant(upper))
}

fn c_value_from_bitvector_term(c_type: CType, term: Bitvector32Term) -> Option<CValue> {
    CValue::from_bitvector_term(c_type, term)
}

fn evaluate_spec_pointer_offset_paths_in(
    scope: SpecScope<'_>,
    pointer: &SpecExpression,
    elements: &SpecExpression,
    byte_width: u32,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for pointer_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        pointer,
        assumptions,
        budget,
    )? {
        let CValue::Pointer(pointer) = pointer_path.value else {
            continue;
        };
        let element_assumptions = assumptions_with_path_context(
            assumptions,
            &pointer_path.facts,
            &pointer_path.obligations,
        );
        for element_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            elements,
            &element_assumptions,
            budget,
        )? {
            let Some((elements, unsigned, wide)) = crate::kernel::eval::pointer_index_term(
                element_path.value,
                &element_path.facts,
                &element_assumptions,
            ) else {
                continue;
            };
            let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &pointer_path.facts,
                &pointer_path.obligations,
                &element_path.facts,
                &element_path.obligations,
                assumptions,
                &element_assumptions,
            ) else {
                continue;
            };
            let elements = if wide {
                elements
            } else {
                canonicalized_offset_index_term(elements, &mut facts)
            };
            paths.push(SpecExpressionPath {
                value: CValue::Pointer(
                    pointer.clone().with_address(
                        pointer
                            .pointer()
                            .offset_by_typed_elements(elements, byte_width, unsigned, wide),
                    ),
                ),
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

/// A specification cannot use the value of a conversion whose range bound
/// is intrinsically false. Keep that bound's diagnostic before path merging
/// removes the impossible value path; otherwise lowering reports only zero
/// paths, losing both the destination range and the constant that failed it.
fn refuted_narrowing_error(obligations: &[ProofObligation]) -> Option<CRuntimeError> {
    for obligation in obligations {
        let Some(context) = obligation
            .context()
            .filter(|context| context.contains("narrowing"))
        else {
            continue;
        };
        let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
            continue;
        };
        if PureFactContext::decide_intrinsically(condition) != Some(false) {
            continue;
        }
        let comparison = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => {
                let op = if matches!(
                    condition,
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        ..
                    }
                ) {
                    "<="
                } else {
                    ">="
                };
                left.as_const()
                    .zip(right.as_const())
                    .map(|(left, right)| format!("{} {op} {}", left as i32, right as i32))
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => {
                let op = if matches!(
                    condition,
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::LessEqual,
                        ..
                    }
                ) {
                    "<="
                } else {
                    ">="
                };
                left.int64_as_const()
                    .zip(right.int64_as_const())
                    .map(|(left, right)| format!("{left} {op} {right}"))
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => left
                .uint64_as_const()
                .zip(right.uint64_as_const())
                .map(|(left, right)| format!("{left} <= {right}")),
            ConditionTerm::IntegerLessEqual(left, right)
            | ConditionTerm::IntegerGreaterEqual(left, right) => {
                let op = if matches!(condition, ConditionTerm::IntegerLessEqual(..)) {
                    "<="
                } else {
                    ">="
                };
                left.as_const()
                    .zip(right.as_const())
                    .map(|(left, right)| format!("{left} {op} {right}"))
            }
            _ => None,
        };
        let reason = comparison.map_or_else(
            || "the range prerequisite is false".to_string(),
            |comparison| format!("{comparison} is false"),
        );
        return Some(CRuntimeError::FunctionContract(format!(
            "{context}: {reason}"
        )));
    }
    None
}

/// The value paths of a C-level evaluation, for a specification that reads
/// them. A path that ended in a runtime error carries no value and is
/// dropped. When every path did, the first error is recorded on the budget:
/// a proposition with no evaluation path is reported by count, and the count
/// says nothing about why (a load of the wrong width, a read no resource
/// permits). Zero paths stays an ordinary answer here, since a requirement
/// that lowers to no path is retained as an obligation downstream.
fn spec_value_paths_in(
    paths: Vec<CExpressionPath>,
    budget: &mut SpecEvaluation<'_>,
) -> Vec<SpecExpressionPath> {
    let mut first_error = None;
    let mut values = Vec::new();
    for path in paths {
        if let Some(error) = refuted_narrowing_error(&path.obligations) {
            first_error.get_or_insert(error);
            continue;
        }
        match path.outcome {
            CExpressionOutcome::Value(value) => values.push(SpecExpressionPath {
                value,
                facts: path.facts,
                obligations: path.obligations,
            }),
            CExpressionOutcome::RuntimeError(error) => {
                first_error.get_or_insert(error);
            }
            CExpressionOutcome::UndefinedBehavior(_) => {}
        }
    }
    if values.is_empty()
        && let Some(error) = first_error
    {
        budget.dropped_runtime_error.get_or_insert(error);
    }
    values
}

fn spec_expression_pointer_step_width(state: &CState, expression: &SpecExpression) -> Option<u32> {
    match expression {
        SpecExpression::CExpression(expression) => {
            c_expression_pointer_step_width(state, expression)
        }
        SpecExpression::PointerOffset { byte_width, .. } => Some(*byte_width),
        SpecExpression::Add(left, right) => spec_expression_pointer_step_width(state, left)
            .or_else(|| spec_expression_pointer_step_width(state, right)),
        SpecExpression::Subtract(left, _) => spec_expression_pointer_step_width(state, left),
        _ => None,
    }
}

/// An impossible specification path still needs the term named by its syntax.
/// Its recorded falsehood discharges every arithmetic domain guard; do not let
/// an arbitrary decision in that context select only an undefined C path.
/// Consistent contexts and pointer operations retain their ordinary lowering.
fn apply_spec_arithmetic(
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply: impl Fn(
        CValue,
        CValue,
        ExecutionFacts,
        Vec<ProofObligation>,
        &PureFactContext,
    ) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    if !assumptions.contains_assumed_exact(&Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    )) || matches!(left, CValue::Pointer(_) | CValue::PointerInteger(_))
        || matches!(right, CValue::Pointer(_) | CValue::PointerInteger(_))
    {
        return apply(left, right, facts, obligations, assumptions);
    }
    apply(
        left,
        right,
        ExecutionFacts::default(),
        Vec::new(),
        &PureFactContext::new(),
    )
    .into_iter()
    .map(|mut path| {
        // These are the operator's arithmetic guards, all discharged by
        // the exact false premise. Keep the operands' own facts and debts.
        path.facts = facts.clone();
        let mut inherited = obligations.clone();
        inherited.extend(path.obligations);
        path.obligations = inherited;
        path
    })
    .collect()
}

fn evaluate_spec_scalar_binary_paths_in(
    scope: SpecScope<'_>,
    left: &SpecExpression,
    right: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
    apply: impl Fn(CValue, CValue, ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in
        evaluate_spec_expression_paths_with_algebraic_bindings_in(scope, left, assumptions, budget)?
    {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            right,
            &right_assumptions,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
                &right_assumptions,
            ) else {
                continue;
            };
            if matches!(left_path.value, CValue::Bool(_))
                || matches!(right_path.value, CValue::Bool(_))
            {
                // Decision D2: a `Bool` is not a number.
                return Err(ExecutionLimit::BoolArithmetic);
            }
            paths.extend(spec_value_paths_in(
                apply(
                    left_path.value.clone(),
                    right_path.value,
                    facts,
                    obligations,
                ),
                budget,
            ));
        }
    }
    Ok(paths)
}

fn evaluate_spec_scalar_unary_paths_in(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
    apply: impl Fn(CValue, ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        expression,
        assumptions,
        budget,
    )? {
        paths.extend(spec_value_paths_in(
            apply(path.value, path.facts, path.obligations),
            budget,
        ));
    }
    Ok(paths)
}

fn evaluate_spec_if_paths_in(
    scope: SpecScope<'_>,
    condition: &SpecProposition,
    then_branch: &SpecExpression,
    else_branch: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    let condition_paths = with_integer_comparisons_preserved(false, || {
        lower_spec_proposition_at_state_with_algebraic_bindings_in(
            scope,
            condition,
            assumptions,
            budget,
        )
    })?;
    for condition_path in condition_paths {
        let branch_assumptions = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        // Logical expressions must have the same shape at declaration and
        // application sites. Ambient proof facts justify explicit reductions,
        // not a different expression during lowering. The only branch this
        // lowering decides is one a literally constant condition folds away;
        // every other condition lowers both branches.
        let condition_truth = constant_spec_condition_value(&condition_path.proposition);

        let branch_paths = match condition_truth {
            Some(true) => evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                then_branch,
                &branch_assumptions,
                budget,
            )?,
            Some(false) => evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                else_branch,
                &branch_assumptions,
                budget,
            )?,
            None => {
                let then_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    scope,
                    then_branch,
                    &branch_assumptions,
                    budget,
                )?;
                let else_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    scope,
                    else_branch,
                    &branch_assumptions,
                    budget,
                )?;
                let mut branch_paths = Vec::new();
                for then_path in then_paths {
                    for else_path in &else_paths {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &then_path.facts,
                            &then_path.obligations,
                            &else_path.facts,
                            &else_path.obligations,
                            &branch_assumptions,
                        ) else {
                            continue;
                        };
                        // Decision D2: an integer arm beside a `Bool` one.
                        if bool_beside_integer(&then_path.value, &else_path.value) {
                            return Err(ExecutionLimit::MixedBoolArms);
                        }
                        let Some(value) = conditional_spec_value(
                            &condition_path.proposition,
                            then_path.value.clone(),
                            else_path.value.clone(),
                        ) else {
                            continue;
                        };
                        branch_paths.push(SpecExpressionPath {
                            value,
                            facts,
                            obligations,
                        });
                    }
                }
                branch_paths
            }
        };

        for branch_path in branch_paths {
            if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &condition_path.facts,
                &condition_path.obligations,
                &branch_path.facts,
                &branch_path.obligations,
                assumptions,
                &branch_assumptions,
            ) {
                paths.push(SpecExpressionPath {
                    value: branch_path.value,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

/// An algebraic `if`, as [`evaluate_spec_if_paths_in`] evaluates a scalar
/// one: a literally constant condition selects its branch, and any other
/// lowers both into one conditional term.
fn evaluate_spec_algebraic_if_paths_in(
    scope: SpecScope<'_>,
    algebraic_type: &AlgebraicType,
    condition: &SpecProposition,
    then_branch: &SpecAlgebraicExpression,
    else_branch: &SpecAlgebraicExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecAlgebraicPath>> {
    if then_branch.algebraic_type != *algebraic_type
        || else_branch.algebraic_type != *algebraic_type
    {
        return Err(ExecutionLimit::Paths);
    }
    let mut paths = Vec::new();
    for condition_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        condition,
        assumptions,
        budget,
    )? {
        let branch_assumptions = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        let branch_paths = match constant_spec_condition_value(&condition_path.proposition) {
            Some(truth) => evaluate_spec_algebraic_at_state_with_bindings_in(
                scope,
                if truth { then_branch } else { else_branch },
                &branch_assumptions,
                budget,
            )?,
            None => {
                let (condition, expected) =
                    proposition_as_single_condition(&condition_path.proposition)
                        .or_else(|| compound_spec_value_condition(&condition_path.proposition))
                        .ok_or(ExecutionLimit::Paths)?;
                let then_paths = evaluate_spec_algebraic_at_state_with_bindings_in(
                    scope,
                    then_branch,
                    &branch_assumptions,
                    budget,
                )?;
                let else_paths = evaluate_spec_algebraic_at_state_with_bindings_in(
                    scope,
                    else_branch,
                    &branch_assumptions,
                    budget,
                )?;
                let mut branch_paths = Vec::new();
                for then_path in then_paths {
                    for else_path in &else_paths {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &then_path.facts,
                            &then_path.obligations,
                            &else_path.facts,
                            &else_path.obligations,
                            &branch_assumptions,
                        ) else {
                            continue;
                        };
                        let (then_value, else_value) = if expected {
                            (then_path.value.clone(), else_path.value.clone())
                        } else {
                            (else_path.value.clone(), then_path.value.clone())
                        };
                        branch_paths.push(SpecAlgebraicPath {
                            value: AlgebraicTerm::if_then_else(
                                condition.clone(),
                                then_value,
                                else_value,
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
                branch_paths
            }
        };
        for branch_path in branch_paths {
            if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &condition_path.facts,
                &condition_path.obligations,
                &branch_path.facts,
                &branch_path.obligations,
                assumptions,
                &branch_assumptions,
            ) {
                paths.push(SpecAlgebraicPath {
                    value: branch_path.value,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

/// An Integer `if`, as [`evaluate_spec_if_paths_in`] evaluates a scalar
/// one: a literally constant condition selects its branch, and any other
/// lowers both into one conditional term.
fn evaluate_spec_integer_if_paths_in(
    scope: SpecScope<'_>,
    condition: &SpecProposition,
    then_branch: &SpecIntegerExpression,
    else_branch: &SpecIntegerExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecIntegerPath>> {
    let mut paths = Vec::new();
    for condition_path in with_integer_comparisons_preserved(false, || {
        lower_spec_proposition_at_state_with_algebraic_bindings_in(
            scope,
            condition,
            assumptions,
            budget,
        )
    })? {
        let branch_assumptions = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        let branch_paths = match constant_spec_condition_value(&condition_path.proposition) {
            Some(truth) => evaluate_spec_integer_expression_paths_in(
                scope,
                if truth { then_branch } else { else_branch },
                &branch_assumptions,
                budget,
            )?,
            None => {
                let (condition, expected) =
                    proposition_as_single_condition(&condition_path.proposition)
                        .or_else(|| compound_spec_value_condition(&condition_path.proposition))
                        .ok_or(ExecutionLimit::Paths)?;
                let then_paths = evaluate_spec_integer_expression_paths_in(
                    scope,
                    then_branch,
                    &branch_assumptions,
                    budget,
                )?;
                let else_paths = evaluate_spec_integer_expression_paths_in(
                    scope,
                    else_branch,
                    &branch_assumptions,
                    budget,
                )?;
                let mut branch_paths = Vec::new();
                for then_path in then_paths {
                    for else_path in &else_paths {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &then_path.facts,
                            &then_path.obligations,
                            &else_path.facts,
                            &else_path.obligations,
                            &branch_assumptions,
                        ) else {
                            continue;
                        };
                        let (then_value, else_value) = if expected {
                            (then_path.value.clone(), else_path.value.clone())
                        } else {
                            (else_path.value.clone(), then_path.value.clone())
                        };
                        branch_paths.push(SpecIntegerPath {
                            value: IntegerTerm::if_then_else(
                                condition.clone(),
                                then_value,
                                else_value,
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
                branch_paths
            }
        };
        for branch_path in branch_paths {
            if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &condition_path.facts,
                &condition_path.obligations,
                &branch_path.facts,
                &branch_path.obligations,
                assumptions,
                &branch_assumptions,
            ) {
                paths.push(SpecIntegerPath {
                    value: branch_path.value,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

fn evaluate_spec_range_fold_paths_in(
    scope: SpecScope<'_>,
    start: &SpecExpression,
    end: &SpecExpression,
    initial: &SpecExpression,
    accumulator: &str,
    item: &str,
    body: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for start_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        start,
        assumptions,
        budget,
    )? {
        let CValue::Int32(start) = start_path.value else {
            continue;
        };
        let start_assumptions =
            assumptions_with_path_context(assumptions, &start_path.facts, &start_path.obligations);
        for end_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            end,
            &start_assumptions,
            budget,
        )? {
            let CValue::Int32(end) = end_path.value else {
                continue;
            };
            let Some((bound_facts, bound_obligations)) =
                merge_execution_pure_facts_and_obligations_under(
                    &start_path.facts,
                    &start_path.obligations,
                    &end_path.facts,
                    &end_path.obligations,
                    assumptions,
                    &start_assumptions,
                )
            else {
                continue;
            };
            let bound_assumptions =
                assumptions_with_path_context(assumptions, &bound_facts, &bound_obligations);
            for initial_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                initial,
                &bound_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &bound_facts,
                    &bound_obligations,
                    &initial_path.facts,
                    &initial_path.obligations,
                    assumptions,
                    &bound_assumptions,
                ) else {
                    continue;
                };
                let Some(path) = evaluate_spec_range_fold_body_path_in(
                    scope,
                    start.clone(),
                    end.clone(),
                    initial_path.value,
                    accumulator,
                    item,
                    body,
                    facts,
                    obligations,
                    assumptions,
                    budget,
                )?
                else {
                    continue;
                };
                paths.push(path);
            }
        }
    }
    Ok(paths)
}

fn evaluate_spec_range_fold_body_path_in(
    scope: SpecScope<'_>,
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body: &SpecExpression,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<SpecExpressionPath>> {
    let state = scope.state;
    match (start.as_const(), end.as_const()) {
        (Some(start), Some(end)) => {
            let mut value = initial;
            let mut facts = facts;
            let mut obligations = obligations;
            for index in concrete_spec_fold_range(start as i32, end as i32) {
                let mut body_state = state.clone();
                body_state.locals.set(accumulator.to_string(), value);
                body_state.locals.set(item.to_string(), int32(index as u32));
                let body_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let mut body_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    SpecScope {
                        state: &body_state,
                        ..scope
                    },
                    body,
                    &body_assumptions,
                    budget,
                )?;
                let Some(body_path) = body_paths.pop() else {
                    return Ok(None);
                };
                if !body_paths.is_empty() {
                    return Ok(None);
                }
                let Some((next_facts, next_obligations)) =
                    merge_execution_pure_facts_and_obligations_under(
                        &facts,
                        &obligations,
                        &body_path.facts,
                        &body_path.obligations,
                        assumptions,
                        &body_assumptions,
                    )
                else {
                    return Ok(None);
                };
                value = body_path.value;
                facts = next_facts;
                obligations = next_obligations;
            }
            Ok(Some(SpecExpressionPath {
                value,
                facts,
                obligations,
            }))
        }
        _ => {
            let mut body_state = state.clone();
            body_state.locals.set(
                accumulator.to_string(),
                int32(Bitvector32Term::Variable(spec_fold_bound_variable(
                    accumulator,
                    0,
                ))),
            );
            body_state.locals.set(
                item.to_string(),
                int32(Bitvector32Term::Variable(spec_fold_bound_variable(item, 1))),
            );
            let body_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            let mut body_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope {
                    state: &body_state,
                    ..scope
                },
                body,
                &body_assumptions,
                budget,
            )?;
            let Some(body_path) = body_paths.pop() else {
                return Ok(None);
            };
            if !body_paths.is_empty() {
                return Ok(None);
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &facts,
                &obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                return Ok(None);
            };
            let Some(value) = symbolic_spec_range_fold_value(
                start,
                end,
                initial,
                accumulator,
                item,
                body_path.value,
            ) else {
                return Ok(None);
            };
            Ok(Some(SpecExpressionPath {
                value,
                facts,
                obligations,
            }))
        }
    }
}

pub(super) fn concrete_spec_fold_range(start: i32, end: i32) -> std::ops::Range<i32> {
    if start <= end {
        start..end
    } else {
        start..start
    }
}

/// The fold binder's range is above universal witnesses and below the
/// refutation/induction producers. Surface lowerers refuse before reaching it.
pub(super) const SPEC_FOLD_BINDER_VARIABLE_BASE: u64 = 1 << 43;
pub(super) const SPEC_FOLD_BINDER_VARIABLE_CEILING: u64 = 1 << 44;

pub(super) fn spec_fold_bound_variable(name: &str, salt: u64) -> Variable {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ salt;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x1000_0000_01b3);
    }
    Variable(
        SPEC_FOLD_BINDER_VARIABLE_BASE
            + (hash % (SPEC_FOLD_BINDER_VARIABLE_CEILING - SPEC_FOLD_BINDER_VARIABLE_BASE)),
    )
}

pub(super) fn symbolic_spec_range_fold_value(
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body_value: CValue,
) -> Option<CValue> {
    let CValue::Int32(initial) = initial else {
        return None;
    };
    let CValue::Int32(body) = body_value else {
        return None;
    };
    Some(CValue::Int32(Bitvector32Term::range_fold(
        start,
        end,
        initial,
        spec_fold_bound_variable(accumulator, 0),
        spec_fold_bound_variable(item, 1),
        body,
    )))
}

/// Turn a compound scalar guard into one existing condition without changing
/// its meaning under ambient facts. Each logical node owns its children once;
/// the selected value's arms are not copied through the guard tree.
fn compound_spec_value_condition(proposition: &Proposition) -> Option<(ConditionTerm, bool)> {
    crate::instrumentation::record_deterministic_work(1);
    let (left, right, conjunction) = match proposition {
        Proposition::And(left, right) => (left.as_ref(), right.as_ref(), true),
        Proposition::Or(left, right) => (left.as_ref(), right.as_ref(), false),
        Proposition::Not(body) => {
            let (condition, expected) = compound_spec_value_condition(body)?;
            return Some((condition, !expected));
        }
        _ => return proposition_as_single_condition(proposition),
    };
    let (left, left_expected) = compound_spec_value_condition(left)?;
    let (right, right_expected) = compound_spec_value_condition(right)?;
    let right_value = Bitvector32Term::if_then_else(
        right,
        Bitvector32Term::Constant(u32::from(right_expected)),
        Bitvector32Term::Constant(u32::from(!right_expected)),
    );
    let constant = Bitvector32Term::Constant(u32::from(!conjunction));
    let (then_term, else_term) = if conjunction == left_expected {
        (right_value, constant)
    } else {
        (constant, right_value)
    };
    let value = Bitvector32Term::if_then_else(left, then_term, else_term);
    Some((
        ConditionTerm::equal(value, Bitvector32Term::Constant(1)),
        true,
    ))
}

pub(super) fn conditional_spec_value(
    proposition: &Proposition,
    then_value: CValue,
    else_value: CValue,
) -> Option<CValue> {
    if then_value == else_value {
        return Some(then_value);
    }
    let (condition, expected) = proposition_as_single_condition(proposition)
        .or_else(|| compound_spec_value_condition(proposition))?;
    // A `bool` conditional of two `bool` values selects one of them, so its
    // leaves stay exactly `0` or `1`.
    let (then_term, else_term, rebuild): (_, _, fn(Bitvector32Term) -> CValue) =
        match (then_value, else_value) {
            (CValue::Int32(then_term), CValue::Int32(else_term)) => {
                (then_term, else_term, CValue::Int32)
            }
            // A `Bool` conditional is the kernel sort's `if` (rule L-If).
            (CValue::Bool(then_term), CValue::Bool(else_term)) => {
                let (then_term, else_term) = if expected {
                    (then_term, else_term)
                } else {
                    (else_term, then_term)
                };
                return Some(CValue::Bool(Bitvector32Term::bool_cast(
                    MachineIntegerType::UInt8,
                    ConditionTerm::bool_if(
                        condition,
                        ConditionTerm::truth_of_bool_word(&then_term),
                        ConditionTerm::truth_of_bool_word(&else_term),
                    ),
                )));
            }
            // Two arms of one integer type: each leaf is already in that
            // type's range, so the selection is too.
            (CValue::Int8(then_term), CValue::Int8(else_term)) => {
                (then_term, else_term, CValue::Int8)
            }
            (CValue::Int16(then_term), CValue::Int16(else_term)) => {
                (then_term, else_term, CValue::Int16)
            }
            (CValue::UInt8(then_term), CValue::UInt8(else_term)) => {
                (then_term, else_term, CValue::UInt8)
            }
            (CValue::UInt16(then_term), CValue::UInt16(else_term)) => {
                (then_term, else_term, CValue::UInt16)
            }
            (CValue::UInt32(then_term), CValue::UInt32(else_term)) => {
                (then_term, else_term, CValue::UInt32)
            }
            // An `int` arm beside an `unsigned int` one converts to
            // `unsigned int`, which keeps its 32 bits.
            (CValue::UInt32(then_term), CValue::Int32(else_term))
            | (CValue::Int32(then_term), CValue::UInt32(else_term)) => {
                (then_term, else_term, CValue::UInt32)
            }
            (CValue::Int64(then_term), CValue::Int64(else_term)) => {
                (then_term, else_term, CValue::Int64)
            }
            (CValue::UInt64(then_term), CValue::UInt64(else_term)) => {
                (then_term, else_term, CValue::UInt64)
            }
            (CValue::Int128(then_term), CValue::Int128(else_term)) => {
                (then_term, else_term, CValue::Int128)
            }
            (CValue::UInt128(then_term), CValue::UInt128(else_term)) => {
                (then_term, else_term, CValue::UInt128)
            }
            _ => return None,
        };
    let (then_term, else_term) = if expected {
        (then_term, else_term)
    } else {
        (else_term, then_term)
    };
    Some(rebuild(Bitvector32Term::if_then_else(
        condition, then_term, else_term,
    )))
}

pub(super) fn proposition_as_single_condition(
    proposition: &Proposition,
) -> Option<(ConditionTerm, bool)> {
    match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => Some((
            ConditionTerm::AlgebraicEqual(Box::new(left.clone()), Box::new(right.clone())),
            true,
        )),
        Proposition::Not(body) => {
            let (condition, value) = proposition_as_single_condition(body)?;
            Some((condition, !value))
        }
        _ => None,
    }
}

/// The truth value a lowered specification condition folds to on its own,
/// or `None` when deciding it would need an ambient fact.
///
/// This is exact constant folding: context-free builtin solving of the
/// lowered proposition, plus the frozen condition checker on the empty
/// context for a bare `ConditionIs`, which is where a folded comparison of
/// two constants is decided. Nothing here reads the surrounding proof
/// context, so a specification `if` lowers to the same shape wherever it is
/// written and wherever it is applied; a condition that holds only under
/// ambient facts is chosen by a proof step, not by lowering.
pub(super) fn constant_spec_condition_value(proposition: &Proposition) -> Option<bool> {
    if solve_builtin_prop(proposition) {
        return Some(true);
    }
    if disprove_builtin_prop(proposition) {
        return Some(false);
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            PureFactContext::decide_intrinsically(condition).map(|decided| decided == *value)
        }
        _ => None,
    }
}

/// Whether one of two values is a `bool` and the other an integer, which
/// decision D2 (Stage 5) refuses to compare or to join.
fn bool_beside_integer(left: &CValue, right: &CValue) -> bool {
    let is_integer = |value: &CValue| {
        !matches!(value, CValue::Bool(_))
            && MachineIntegerType::from_c_type(value.numeric_value().c_type()).is_some()
    };
    (matches!(left, CValue::Bool(_)) && is_integer(right))
        || (is_integer(left) && matches!(right, CValue::Bool(_)))
}

/// The claim that a `CValue::Bool` word has truth `value`. A specification
/// `Bool` (the cast `b as uint8`, rule C1) is the claim on `b` itself; any
/// other word, a C `bool` value this stage still holds as an integer, is
/// C's test of it against zero, `w != 0` for `true` and `w == 0` for
/// `false`, the same test a C branch on the value makes.
fn bool_word_truth_proposition(word: &CValue, value: bool) -> Option<Proposition> {
    let CValue::Bool(term) = word else {
        return None;
    };
    if let Some(condition) = term.bool_cast_operand() {
        return Some(condition.truth_claim(value));
    }
    c_value_comparison_proposition(
        word,
        if value {
            CComparisonOperator::NotEqual
        } else {
            CComparisonOperator::Equal
        },
        &CValue::Bool(Bitvector32Term::Constant(0)),
    )
}

/// A comparison with a `bool` operand (Stage 5). `Bool` has equality and
/// nothing else, and is not an integer (decision D2): an order, or a
/// comparison with an integer, is refused. Two `Bool` values are equal when
/// they have the same truth (rule L-Eq), and a comparison with `true` or
/// `false` is the claim on the other operand. Two `Bool` words of which one
/// is not a cast (a `match` whose arms are `Bool` values) keep their word
/// equality (`None`), which is the same claim by rule C1c.
fn bool_comparison_proposition(
    left: &CValue,
    operator: CComparisonOperator,
    right: &CValue,
) -> Option<ExecutionResult<Proposition>> {
    let is_bool = |value: &CValue| matches!(value, CValue::Bool(_));
    if !is_bool(left) && !is_bool(right) {
        return None;
    }
    if bool_beside_integer(left, right) {
        return Some(Err(ExecutionLimit::BoolComparedWithInteger));
    }
    if !is_bool(left) || !is_bool(right) {
        return None;
    }
    let equal = match operator {
        CComparisonOperator::Equal => true,
        CComparisonOperator::NotEqual => false,
        _ => return Some(Err(ExecutionLimit::BoolOrdered)),
    };
    let (CValue::Bool(left_term), CValue::Bool(right_term)) = (left, right) else {
        unreachable!("both operands are `bool`");
    };
    let literal = |term: &Bitvector32Term| match term {
        Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
            Some(*value != 0)
        }
        _ => None,
    };
    match (literal(left_term), literal(right_term)) {
        (Some(left), Some(right)) => {
            return Some(Ok(Proposition::ConditionIs(
                ConditionTerm::Constant((left == right) == equal),
                true,
            )));
        }
        (Some(constant), None) => {
            return bool_word_truth_proposition(right, constant == equal).map(Ok);
        }
        (None, Some(constant)) => {
            return bool_word_truth_proposition(left, constant == equal).map(Ok);
        }
        (None, None) => {}
    }
    // A `Bool` word that is not a cast, such as a `match` whose arms are
    // `Bool` values, is compared as the word it is: every `Bool` word is the
    // canonical 1 or 0 (rule C1c), so two are equal exactly when their
    // truths are, and the word keeps the `match` for its reduction.
    if left_term.bool_cast_operand().is_none() || right_term.bool_cast_operand().is_none() {
        return None;
    }
    Some(Ok(Proposition::ConditionIs(
        ConditionTerm::bool_equal(
            ConditionTerm::truth_of_bool_word(left_term),
            ConditionTerm::truth_of_bool_word(right_term),
        ),
        equal,
    )))
}

pub(super) fn c_value_comparison_proposition(
    left: &CValue,
    operator: CComparisonOperator,
    right: &CValue,
) -> Option<Proposition> {
    let left = left.numeric_value();
    let right = right.numeric_value();
    // Two values of one abstract type have equality and nothing else.
    match (left, right) {
        (CValue::Parameter(a), CValue::Parameter(b))
            if a.algebraic_type == b.algebraic_type
                && matches!(
                    operator,
                    CComparisonOperator::Equal | CComparisonOperator::NotEqual
                ) =>
        {
            return Some(Proposition::ConditionIs(
                ConditionTerm::AlgebraicEqual(a.clone(), b.clone()),
                operator == CComparisonOperator::Equal,
            ));
        }
        (CValue::Parameter(_), _) | (_, CValue::Parameter(_)) => return None,
        _ => {}
    }
    if let (CValue::Pointer(a), CValue::Pointer(b)) = (left, right)
        && !a.is_null()
        && !b.is_null()
        && a.c_type().pointer_types_compatible(b.c_type())
        && matches!(
            operator,
            CComparisonOperator::Equal | CComparisonOperator::NotEqual
        )
    {
        let condition = ConditionTerm::pointer_value_equal(a.clone(), b.clone());
        return Some(Proposition::ConditionIs(
            condition,
            operator == CComparisonOperator::Equal,
        ));
    }
    if matches!(left, CValue::Int128(_) | CValue::UInt128(_))
        || matches!(right, CValue::Int128(_) | CValue::UInt128(_))
    {
        return crate::kernel::eval::wide_integer_comparison_condition(operator, left, right)
            .map(|condition| Proposition::ConditionIs(condition, true));
    }
    let pointer_condition = match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right))
            if left.c_type().pointer_types_compatible(right.c_type())
                || left.is_null()
                || right.is_null() =>
        {
            match operator {
                CComparisonOperator::Equal => Some((
                    pointer_equality_condition(left.pointer().clone(), right.pointer().clone()),
                    true,
                )),
                CComparisonOperator::NotEqual => Some((
                    pointer_equality_condition(left.pointer().clone(), right.pointer().clone()),
                    false,
                )),
                CComparisonOperator::LessThan
                | CComparisonOperator::LessEqual
                | CComparisonOperator::GreaterThan
                | CComparisonOperator::GreaterEqual
                    if left.block == right.block =>
                {
                    let left = byte_offset_from_pointer_offset(&left.offset)?;
                    let right = byte_offset_from_pointer_offset(&right.offset)?;
                    Some((pointer_order_condition(left, right, operator), true))
                }
                CComparisonOperator::LessThan
                | CComparisonOperator::LessEqual
                | CComparisonOperator::GreaterThan
                | CComparisonOperator::GreaterEqual => None,
            }
        }
        (CValue::Pointer(_), CValue::Pointer(_)) => None,
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            match operator {
                CComparisonOperator::Equal => {
                    Some((pointer_is_null_condition(pointer.pointer().clone()), true))
                }
                CComparisonOperator::NotEqual => {
                    Some((pointer_is_null_condition(pointer.pointer().clone()), false))
                }
                CComparisonOperator::LessThan
                | CComparisonOperator::LessEqual
                | CComparisonOperator::GreaterThan
                | CComparisonOperator::GreaterEqual => None,
            }
        }
        _ => None,
    };
    if let Some((condition, value)) = pointer_condition {
        return Some(Proposition::ConditionIs(condition, value));
    }

    let target_type = if matches!(left, CValue::Float64(_)) || matches!(right, CValue::Float64(_)) {
        Some(CType::Float64)
    } else if matches!(left, CValue::Float32(_)) || matches!(right, CValue::Float32(_)) {
        Some(CType::Float32)
    } else {
        None
    };
    if let Some(target_type) = target_type {
        let mut obligations = Vec::new();
        let left = coerce_c_value_to_type(
            left.clone(),
            target_type,
            &mut obligations,
            &PureFactContext::new(),
        )?;
        let right = coerce_c_value_to_type(
            right.clone(),
            target_type,
            &mut obligations,
            &PureFactContext::new(),
        )?;
        if !obligations.is_empty() {
            return None;
        }
        let condition = match (target_type, left, right) {
            (CType::Float32, CValue::Float32(left), CValue::Float32(right)) => {
                ConditionTerm::float32_compare(left, right, operator)
            }
            (CType::Float64, CValue::Float64(left), CValue::Float64(right)) => {
                ConditionTerm::float64_compare(left, right, operator)
            }
            _ => return None,
        };
        return Some(Proposition::ConditionIs(
            condition,
            !matches!(operator, CComparisonOperator::NotEqual),
        ));
    }

    if matches!(left, CValue::UInt64(_)) || matches!(right, CValue::UInt64(_)) {
        let left = c_value_uint64_term(left)?;
        let right = c_value_uint64_term(right)?;
        let condition = match operator {
            CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
                ConditionTerm::uint64_equal(left, right)
            }
            CComparisonOperator::LessThan => ConditionTerm::uint64_less_than(left, right),
            CComparisonOperator::LessEqual => ConditionTerm::uint64_less_equal(left, right),
            CComparisonOperator::GreaterThan => ConditionTerm::uint64_greater_than(left, right),
            CComparisonOperator::GreaterEqual => ConditionTerm::uint64_greater_equal(left, right),
        };
        return Some(Proposition::ConditionIs(
            condition,
            !matches!(operator, CComparisonOperator::NotEqual),
        ));
    }
    if matches!(left, CValue::Int64(_)) || matches!(right, CValue::Int64(_)) {
        let left = c_value_int64_term(left)?;
        let right = c_value_int64_term(right)?;
        let condition = match operator {
            CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
                ConditionTerm::int64_equal(left, right)
            }
            CComparisonOperator::LessThan => ConditionTerm::int64_signed_less_than(left, right),
            CComparisonOperator::LessEqual => ConditionTerm::int64_signed_less_equal(left, right),
            CComparisonOperator::GreaterThan => {
                ConditionTerm::int64_signed_greater_than(left, right)
            }
            CComparisonOperator::GreaterEqual => {
                ConditionTerm::int64_signed_greater_equal(left, right)
            }
        };
        return Some(Proposition::ConditionIs(
            condition,
            !matches!(operator, CComparisonOperator::NotEqual),
        ));
    }

    let unsigned = matches!(left, CValue::UInt32(_)) || matches!(right, CValue::UInt32(_));
    let left = c_value_int32_term(left)?;
    let right = c_value_int32_term(right)?;
    let (condition, value) = match operator {
        CComparisonOperator::Equal | CComparisonOperator::NotEqual => (
            if unsigned {
                ConditionTerm::uint32_equal(left, right)
            } else {
                ConditionTerm::equal(left, right)
            },
            matches!(operator, CComparisonOperator::Equal),
        ),
        CComparisonOperator::LessThan => (
            if unsigned {
                ConditionTerm::unsigned_less_than(left, right)
            } else {
                ConditionTerm::signed_less_than(left, right)
            },
            true,
        ),
        CComparisonOperator::LessEqual => (
            if unsigned {
                ConditionTerm::unsigned_less_equal(left, right)
            } else {
                ConditionTerm::signed_less_equal(left, right)
            },
            true,
        ),
        CComparisonOperator::GreaterThan => (
            if unsigned {
                ConditionTerm::unsigned_greater_than(left, right)
            } else {
                ConditionTerm::signed_greater_than(left, right)
            },
            true,
        ),
        CComparisonOperator::GreaterEqual => (
            if unsigned {
                ConditionTerm::unsigned_greater_equal(left, right)
            } else {
                ConditionTerm::signed_greater_equal(left, right)
            },
            true,
        ),
    };
    Some(Proposition::ConditionIs(condition, value))
}

fn c_value_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int8(value) => Some(value.clone()),
        CValue::Bool(value)
        | CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value)
        | CValue::UInt32(value) => Some(value.clone()),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Parameter(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn c_value_int64_term(value: &CValue) -> Option<Bitvector32Term> {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int64(value) => Some(value.clone()),
        CValue::Bool(value) => Some(Bitvector32Term::int64_from_32(value.clone())),
        CValue::Int8(value) => Some(Bitvector32Term::int64_from_32(value.clone())),
        CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value) => Some(Bitvector32Term::int64_from_32(value.clone())),
        CValue::UInt32(value) => Some(Bitvector32Term::int64_from_uint32(value.clone())),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Parameter(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn c_value_uint64_term(value: &CValue) -> Option<Bitvector32Term> {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::UInt64(value) => Some(value.clone()),
        CValue::Bool(value) => Some(Bitvector32Term::uint64_from_32(value.clone())),
        CValue::Int64(value) => Some(Bitvector32Term::uint64_from_int64(value.clone())),
        CValue::Int8(value) => Some(Bitvector32Term::uint64_from_int32(value.clone())),
        CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value) => Some(Bitvector32Term::uint64_from_int32(value.clone())),
        CValue::UInt32(value) => Some(Bitvector32Term::uint64_from_32(value.clone())),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Pointer(_)
        | CValue::Parameter(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

#[cfg(test)]
mod integer_budget_tests;

#[cfg(test)]
mod lowering_provenance_tests;

#[cfg(test)]
mod spec_pointer_subtraction_tests;

#[cfg(test)]
mod no_value_path_tests;

#[cfg(test)]
mod integer_capture_condition_tests;

#[cfg(test)]
mod wide_scalar_conversion_tests;

#[cfg(test)]
mod integer_truncation_tests;

#[cfg(test)]
mod compound_conditional_tests;

#[cfg(test)]
mod resource_call_type_tests;

#[cfg(test)]
mod pointer_integer_observation_tests {
    use super::*;

    #[test]
    fn integer_specifications_observe_bits_without_a_pointer_record() {
        let context = PureFactContext::new();
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(994_001)), CType::Int32Pointer);
        let word = crate::kernel::eval::cast_c_value_to_type(
            CValue::Pointer(pointer),
            CType::UInt64,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        assert!(crate::kernel::resource_arguments_proven_equal(
            &AlgebraicValue::C(word.clone()),
            &AlgebraicValue::C(word.numeric_value().clone()),
            &context,
        ));
        let state = CState::new().with_local("word", word.clone());
        for expression in [
            SpecExpression::Value(word.clone()),
            SpecExpression::CExpression(CExpression::Variable("word".into())),
        ] {
            let paths = evaluate_spec_expression_paths_with_bindings(
                &state,
                &expression,
                &context,
                &BTreeMap::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            assert_eq!(&paths[0].value, word.numeric_value());
            assert!(!matches!(paths[0].value, CValue::PointerInteger(_)));
        }
    }
}

#[cfg(test)]
mod pointer_coercion_tests;

#[cfg(test)]
mod certificate_observation_tests {
    use super::*;

    #[test]
    fn certificate_lowering_preserves_types_without_changing_ordinary_facts() {
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let observe = |id| {
                IntegerTerm::from_machine(ty, Bitvector32Term::Variable(Variable(id))).unwrap()
            };
            let left = observe(994_011);
            let right = observe(994_012);
            let written = SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(left.clone()),
                operator: IntegerComparisonOperator::Equal,
                right: SpecIntegerExpression::Term(right.clone()),
            };
            let lower = || {
                crate::kernel::c_lower_spec_proposition_with_checked_obligations(
                    &CState::new(),
                    &written,
                    None,
                    &PureFactContext::new(),
                )
                .unwrap()
                .0
            };
            let ordinary = lower();
            let typed = Proposition::ConditionIs(ConditionTerm::integer_equal(left, right), true);
            assert_ne!(ordinary, typed);
            with_preserved_integer_comparisons(|| {
                assert_eq!(lower(), typed);
                with_preserved_integer_comparisons(|| assert_eq!(lower(), typed));
                assert_eq!(lower(), typed);
            });
            assert_eq!(lower(), ordinary);
        }
    }
}

#[cfg(test)]
mod arithmetic_domain_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/spec/arithmetic_domains.rs");
}
