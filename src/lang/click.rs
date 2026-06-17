//! Tiny `.click` sidecar verifier for the C0 megakernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::lang::c::syntax::{self, C0Expression, C0Type};
use crate::megakernel::{
    Assumptions, Bitvector32Term, CComparisonOperator, CExpression, CFunction,
    CFunctionEnvironment, CFunctionOutcome, CFunctionSpecification, CLoopInvariantCheck, CMemory,
    CProposition, CState, CStatement, CValue, ConditionTerm, PathFact, Pointer, PointerOffsetTerm,
    ProofObligation, Proposition, Sort, Theorem, Variable, c_function, c_function_specification,
    c_labeled_assert, c_pointer_value, c_seq, c_while_with_invariant_checks,
    prove_c_function_satisfies_specification_from_symbolic_path,
    prove_c_function_satisfies_specification_with_environment,
    prove_symbolic_c_function_execution_paths_with_environment,
    prove_symbolic_c_function_verification_paths_with_environment,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFile {
    verifying_sources: Vec<String>,
    function_blocks: Vec<FunctionBlock>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionBlock {
    signature: FunctionSignature,
    requires: Vec<Requirement>,
    structural_clauses: Vec<StructuralClause>,
    ensures: Vec<EnsureClause>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSignature {
    return_type: C0Type,
    name: String,
    parameters: Vec<FunctionParameter>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionParameter {
    c_type: C0Type,
    name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    ValidRange {
        name: String,
        bytes: RangeBytes,
    },
    ValidRangeSegment {
        name: String,
        start: RangeBytes,
        end: RangeBytes,
    },
    Proposition(ClickProposition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RangeBytes {
    Constant(u32),
    Parameter(String),
    Add(Box<RangeBytes>, Box<RangeBytes>),
    Subtract(Box<RangeBytes>, Box<RangeBytes>),
    Multiply(Box<RangeBytes>, Box<RangeBytes>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnsureClause {
    name: Option<String>,
    ensure: Ensure,
    proof: Proof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralClause {
    target: StructuralTarget,
    items: Vec<StructuralItem>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum StructuralTarget {
    Loop(usize),
    Statement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralItem {
    kind: StructuralItemKind,
    proposition: ClickProposition,
    proof: Proof,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralItemKind {
    Invariant,
    Assert,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ensure {
    Proposition(ClickProposition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClickProposition {
    Comparison {
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
    },
    Preserves(ContractSegment),
    WritesOnly(ContractSegment),
    And(Box<ClickProposition>, Box<ClickProposition>),
    Or(Box<ClickProposition>, Box<ClickProposition>),
    Not(Box<ClickProposition>),
    Implies(Box<ClickProposition>, Box<ClickProposition>),
    ForAll {
        c_type: C0Type,
        name: String,
        body: Box<ClickProposition>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContractExpression {
    Current(CExpression),
    Old(CExpression),
    Add(Box<ContractExpression>, Box<ContractExpression>),
    Subtract(Box<ContractExpression>, Box<ContractExpression>),
    Index(Box<ContractExpression>, Box<ContractExpression>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractSegment {
    state: ContractSegmentState,
    base: CExpression,
    start: CExpression,
    end: CExpression,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContractSegmentState {
    Current,
    Old,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

impl fmt::Display for ComparisonOperator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let spelling = match self {
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
        };
        formatter.write_str(spelling)
    }
}

/// A `.click` `by` clause proving one theorem.
///
/// `auto` is a heuristic tactic. Deterministic proof replay should grow through
/// `Proof::Steps`, where each `ProofStep` is an explicit axiom invocation or a
/// fixed deterministic sequence of axiom invocations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
    Tactic(Tactic),
    Steps(Vec<ProofStep>),
}

/// A deterministic `.click` proof step.
///
/// This is intentionally separate from `Tactic`: tactics may search, but proof
/// steps should be stable and replayable. The first explicit proof steps will be
/// added when `auto` starts emitting proof certificates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofStep {}

/// A heuristic `.click` tactic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Tactic {
    Auto,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedCTheorem {
    pub source_path: String,
    pub function_block: FunctionBlock,
    pub ensure_index: usize,
    pub ensure_clause: EnsureClause,
    pub proof_kind: AutoProofKind,
    pub specification: CFunctionSpecification,
    pub theorem: Theorem,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AutoProofKind {
    LoopVerification,
    BoundedExecution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickError {
    message: String,
}

impl ClickFile {
    pub fn verifying_sources(&self) -> &[String] {
        &self.verifying_sources
    }

    pub fn function_blocks(&self) -> &[FunctionBlock] {
        &self.function_blocks
    }
}

impl FunctionBlock {
    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    pub fn structural_clauses(&self) -> &[StructuralClause] {
        &self.structural_clauses
    }

    pub fn ensures(&self) -> &[EnsureClause] {
        &self.ensures
    }
}

impl FunctionSignature {
    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }
}

impl FunctionParameter {
    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl EnsureClause {
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn ensure(&self) -> &Ensure {
        &self.ensure
    }

    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl StructuralClause {
    pub fn target(&self) -> &StructuralTarget {
        &self.target
    }

    pub fn items(&self) -> &[StructuralItem] {
        &self.items
    }
}

impl StructuralItem {
    pub fn kind(&self) -> StructuralItemKind {
        self.kind
    }

    pub fn proposition(&self) -> &ClickProposition {
        &self.proposition
    }

    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl Proof {
    pub fn is_auto_tactic(&self) -> bool {
        matches!(self, Self::Tactic(Tactic::Auto))
    }

    pub fn steps(&self) -> Option<&[ProofStep]> {
        match self {
            Self::Tactic(_) => None,
            Self::Steps(steps) => Some(steps),
        }
    }
}

impl VerifiedCTheorem {
    pub fn proof_kind(&self) -> AutoProofKind {
        self.proof_kind
    }
}

impl ClickError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

pub fn parse(source: &str) -> Result<ClickFile, ClickError> {
    Parser::new(source)?.parse_file()
}

pub fn verify_c0_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let file = parse(click_source)?;
    let c_sources: BTreeMap<&str, &str> = c_sources.iter().copied().collect();
    let parsed_sources = parse_verified_sources(&file, &c_sources)?;
    let function_environment = build_function_environment(&parsed_sources);
    let mut verified = Vec::new();

    for function_block in file.function_blocks {
        let (source_path, parsed_function) = parsed_sources
            .get(function_block.signature.name())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{}` is not defined by any `verifying` source",
                    function_block.signature.name()
                ))
            })?;
        check_signature(&function_block.signature, parsed_function, source_path)?;
        validate_structural_clauses(&function_block, parsed_function)?;
        for (ensure_index, ensure_clause) in function_block.ensures.iter().enumerate() {
            let ensure_label =
                ensure_label(function_block.signature.name(), ensure_clause, ensure_index);
            if !ensure_clause.proof.is_auto_tactic() {
                return Err(ClickError::new(format!(
                    "`{ensure_label}` must use exactly `by auto;` in this first slice"
                )));
            }

            let (state, arguments, requirement_propositions) = initial_call(
                function_block.signature.name(),
                function_block.requires(),
                parsed_function.parameters(),
            )?;
            let function =
                annotated_function(&function_block, parsed_function, &state, &arguments)?;
            let assumptions = assumptions_from_propositions(&requirement_propositions);
            let vc_execution = prove_symbolic_c_function_verification_paths_with_environment(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                function_environment.clone(),
            );
            if let Some(error) =
                execution_obligation_error(&vc_execution, &ensure_label, &requirement_propositions)
            {
                return Err(error);
            }
            let loop_verification_error = match prove_ensure_from_execution(
                &vc_execution,
                AutoExecutionKind::LoopVerification,
                source_path,
                &function_block,
                ensure_index,
                ensure_clause,
                &ensure_label,
                parsed_function.parameters(),
                &function,
                &state,
                &arguments,
                &requirement_propositions,
            ) {
                Ok(theorems) => {
                    verified.extend(theorems);
                    continue;
                }
                Err(error) => Some(error),
            };
            let execution = prove_symbolic_c_function_execution_paths_with_environment(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions,
                function_environment.clone(),
            );
            if let Some(error) =
                execution_obligation_error(&execution, &ensure_label, &requirement_propositions)
            {
                if let Some(loop_verification_error) = loop_verification_error {
                    return Err(loop_verification_error);
                }
                return Err(error);
            }
            let theorems = prove_ensure_from_execution(
                &execution,
                AutoExecutionKind::BoundedExecution {
                    environment: &function_environment,
                },
                source_path,
                &function_block,
                ensure_index,
                ensure_clause,
                &ensure_label,
                parsed_function.parameters(),
                &function,
                &state,
                &arguments,
                &requirement_propositions,
            )?;
            verified.extend(theorems);
        }
    }

    Ok(verified)
}

enum AutoExecutionKind<'a> {
    LoopVerification,
    BoundedExecution {
        environment: &'a CFunctionEnvironment,
    },
}

impl AutoExecutionKind<'_> {
    fn proof_kind(&self) -> AutoProofKind {
        match self {
            Self::LoopVerification => AutoProofKind::LoopVerification,
            Self::BoundedExecution { .. } => AutoProofKind::BoundedExecution,
        }
    }
}

fn execution_obligation_error(
    execution: &crate::megakernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_propositions: &[Proposition],
) -> Option<ClickError> {
    if let Some(limit) = execution.limit() {
        return Some(ClickError::new(format!(
            "`auto` hit execution limit {limit:?} for `{ensure_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Some(ClickError::new(format!(
            "`auto` could not prove any complete execution path for `{ensure_label}`"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Some(ClickError::new(format!(
                "`auto` failed for `{ensure_label}` path {path_index}: remaining proof obligations: {}\n  available requirements: {}\n  path facts: {}",
                describe_obligations(path.obligations()),
                describe_propositions(&requirement_propositions),
                describe_facts(path.facts())
            )));
        }
    }

    None
}

fn prove_ensure_from_execution(
    execution: &crate::megakernel::SymbolicCExecution,
    execution_kind: AutoExecutionKind<'_>,
    source_path: &str,
    function_block: &FunctionBlock,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    ensure_label: &str,
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_propositions: &[Proposition],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let proof_kind = execution_kind.proof_kind();
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`auto` hit execution limit {limit:?} for `{ensure_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`auto` could not prove any complete execution path for `{ensure_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`auto` failed for `{ensure_label}` path {path_index}: unexpected theorem body {proposition:?}\n  available requirements: {}\n  path facts: {}",
                    describe_propositions(&requirement_propositions),
                    describe_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_propositions.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_ensure(
            ensure_label,
            path_index,
            path.facts(),
            &path_requirements,
            ensure_clause,
            parameters,
            arguments,
            state,
            &outcome,
        )?;
        let path_requirements_description = describe_propositions(&path_requirements);
        let specification = c_function_specification(
            state.clone(),
            arguments.to_vec(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = match execution_kind {
            AutoExecutionKind::LoopVerification => {
                prove_c_function_satisfies_specification_from_symbolic_path(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    path.facts(),
                    path.obligations(),
                )
            }
            AutoExecutionKind::BoundedExecution { environment } => {
                prove_c_function_satisfies_specification_with_environment(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    (*environment).clone(),
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`auto` failed for `{ensure_label}` path {path_index}: execution did not satisfy the packaged specification\n  available requirements: {}\n  path facts: {}",
                        path_requirements_description,
                        describe_facts(path.facts())
                    ))
                })?
            }
        };

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            ensure_index,
            ensure_clause: ensure_clause.clone(),
            proof_kind,
            specification,
            theorem,
        });
    }

    Ok(verified)
}

fn parse_verified_sources<'a>(
    file: &ClickFile,
    c_sources: &'a BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, (String, syntax::C0Function)>, ClickError> {
    if file.verifying_sources.is_empty() {
        return Err(ClickError::new(
            "`.click` file must declare at least one `verifying \"source.c\";`",
        ));
    }

    let mut parsed = BTreeMap::new();
    for source_path in &file.verifying_sources {
        let c_source = *c_sources.get(source_path.as_str()).ok_or_else(|| {
            ClickError::new(format!(
                "`verifying` refers to missing C source `{source_path}`"
            ))
        })?;
        let function = syntax::parse_function(c_source).map_err(|error| {
            ClickError::new(format!(
                "failed to parse C source `{source_path}`: {}",
                error.message()
            ))
        })?;
        let function_name = function.name().to_string();
        let previous = parsed.insert(function_name.clone(), (source_path.clone(), function));
        if previous.is_some() {
            return Err(ClickError::new(format!(
                "more than one `verifying` source defines function `{function_name}`"
            )));
        }
    }

    Ok(parsed)
}

fn build_function_environment(
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
) -> CFunctionEnvironment {
    parsed_sources
        .values()
        .fold(CFunctionEnvironment::new(), |environment, (_, function)| {
            environment.with_function(function.to_megakernel_function())
        })
}

fn ensure_label(function_name: &str, ensure: &EnsureClause, index: usize) -> String {
    match ensure.name() {
        Some(name) => format!("{function_name}.{name}"),
        None => format!("{function_name}.ensures_{index}"),
    }
}

fn implication_body(proposition: &Proposition) -> &Proposition {
    match proposition {
        Proposition::Implies(_, body) => implication_body(body),
        _ => proposition,
    }
}

fn assumptions_from_propositions(propositions: &[Proposition]) -> Assumptions {
    propositions
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition)
}

fn describe_propositions(propositions: &[Proposition]) -> String {
    if propositions.is_empty() {
        return "[]".to_string();
    }

    format!("{propositions:?}")
}

fn describe_facts(facts: &[PathFact]) -> String {
    if facts.is_empty() {
        return "[]".to_string();
    }

    let entries = facts
        .iter()
        .map(|fact| format!("{:?}", fact.proposition()))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn describe_obligations(obligations: &[ProofObligation]) -> String {
    if obligations.is_empty() {
        return "[]".to_string();
    }

    let entries = obligations
        .iter()
        .map(|obligation| match obligation.context() {
            Some(context) => format!("{context}: {:?}", obligation.proposition()),
            None => format!("{:?}", obligation.proposition()),
        })
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn check_signature(
    signature: &FunctionSignature,
    parsed_function: &syntax::C0Function,
    source_path: &str,
) -> Result<(), ClickError> {
    if signature.return_type() != parsed_function.return_type() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click return type is {:?}, C return type is {:?}",
            signature.name(),
            signature.return_type(),
            parsed_function.return_type()
        )));
    }

    if signature.parameters().len() != parsed_function.parameters().len() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click has {} parameters, C has {}",
            signature.name(),
            signature.parameters().len(),
            parsed_function.parameters().len()
        )));
    }

    for (index, (expected, actual)) in signature
        .parameters()
        .iter()
        .zip(parsed_function.parameters())
        .enumerate()
    {
        if expected.c_type() != actual.c_type() || expected.name() != actual.name() {
            return Err(ClickError::new(format!(
                "signature mismatch for `{}` parameter {} in `{source_path}`: .click has {:?} {}, C has {:?} {}",
                signature.name(),
                index + 1,
                expected.c_type(),
                expected.name(),
                actual.c_type(),
                actual.name()
            )));
        }
    }

    Ok(())
}

fn validate_structural_clauses(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    let statement_count = count_statements(parsed_function.body());
    for structural_clause in function_block.structural_clauses() {
        match structural_clause.target() {
            StructuralTarget::Loop(index) if *index >= loop_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `loop {index}` target; it contains {loop_count} loop(s)",
                    function_block.signature().name()
                )));
            }
            StructuralTarget::Statement(index) if *index >= statement_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `statement {index}` target; it contains {statement_count} statement(s)",
                    function_block.signature().name()
                )));
            }
            StructuralTarget::Statement(_) => {
                for item in structural_clause.items() {
                    if item.kind() == StructuralItemKind::Invariant {
                        return Err(ClickError::new(
                            "`invariant` is only supported at `loop` targets",
                        ));
                    }
                }
            }
            StructuralTarget::Loop(_) => {}
        }

        for item in structural_clause.items() {
            if !item.proof().is_auto_tactic() {
                return Err(ClickError::new(
                    "structural proof blocks must use exactly `by auto;` in this first slice",
                ));
            }
            if item.kind() == StructuralItemKind::Assert
                && click_proposition_to_c_expression(item.proposition()).is_none()
            {
                return Err(ClickError::new(
                    "`assert` clauses currently support executable propositions only",
                ));
            }
        }
    }
    Ok(())
}

fn annotated_function(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    entry_state: &CState,
    arguments: &[CExpression],
) -> Result<CFunction, ClickError> {
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        entry_state,
        entry_values: parameter_values(parsed_function.parameters(), arguments)?,
        quantified_values: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_000_000,
    };
    let body = lowerer.lower_statement(parsed_function.body())?;
    Ok(c_function(
        parsed_function.return_type().to_megakernel_type(),
        parsed_function.name().to_string(),
        parsed_function
            .parameters()
            .iter()
            .map(syntax::C0Parameter::to_megakernel_parameter)
            .collect(),
        body,
    ))
}

struct AnnotationLowerer<'a> {
    structural_clauses: &'a [StructuralClause],
    entry_state: &'a CState,
    entry_values: BTreeMap<String, CValue>,
    quantified_values: BTreeMap<String, CValue>,
    loop_index: usize,
    statement_index: usize,
    next_quantifier_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LabeledCheck {
    condition: CExpression,
    label: String,
}

impl AnnotationLowerer<'_> {
    fn lower_statement(
        &mut self,
        statement: &syntax::C0Statement,
    ) -> Result<CStatement, ClickError> {
        Ok(match statement {
            syntax::C0Statement::Seq(first, second) => {
                c_seq(self.lower_statement(first)?, self.lower_statement(second)?)
            }
            syntax::C0Statement::While { condition, body } => {
                let statement_index = self.next_statement_index();
                let loop_index = self.next_loop_index();
                let lowered_body = self.lower_statement(body)?;
                let loop_asserts = self.loop_assert_checks(loop_index);
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let lowered_loop = c_while_with_invariant_checks(
                    condition.to_megakernel_expression(),
                    Vec::new(),
                    invariant_checks,
                    lowered_body,
                );
                let lowered_loop = prepend_labeled_asserts(lowered_loop, &loop_asserts);
                self.prepend_statement_asserts(statement_index, lowered_loop)
            }
            statement => {
                let statement_index = self.next_statement_index();
                let lowered = statement.to_megakernel_statement();
                self.prepend_statement_asserts(statement_index, lowered)
            }
        })
    }

    fn next_statement_index(&mut self) -> usize {
        let index = self.statement_index;
        self.statement_index += 1;
        index
    }

    fn next_loop_index(&mut self) -> usize {
        let index = self.loop_index;
        self.loop_index += 1;
        index
    }

    fn prepend_statement_asserts(
        &self,
        statement_index: usize,
        statement: CStatement,
    ) -> CStatement {
        let checks = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.target() == &StructuralTarget::Statement(statement_index))
            .flat_map(StructuralClause::items)
            .enumerate()
            .map(|(item_index, item)| LabeledCheck {
                condition: click_proposition_to_c_expression(item.proposition())
                    .expect("structural propositions should be validated before lowering"),
                label: format!(
                    "statement {statement_index} {} {item_index}",
                    structural_item_kind_label(item.kind())
                ),
            })
            .collect::<Vec<_>>();
        prepend_labeled_asserts(statement, &checks)
    }

    fn loop_invariant_checks(
        &mut self,
        loop_index: usize,
    ) -> Result<Vec<CLoopInvariantCheck>, ClickError> {
        self.structural_clauses
            .iter()
            .filter(|clause| clause.target() == &StructuralTarget::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .enumerate()
            .map(|(item_index, item)| {
                Ok(CLoopInvariantCheck::new(
                    self.click_proposition_to_c_proposition(item.proposition())
                        .map_err(|message| {
                            ClickError::new(format!(
                                "loop {loop_index} invariant {item_index}: {message}"
                            ))
                        })?,
                    Some(format!("loop {loop_index} invariant {item_index} entry")),
                    Some(format!(
                        "loop {loop_index} invariant {item_index} preservation"
                    )),
                ))
            })
            .collect()
    }

    fn click_proposition_to_c_proposition(
        &mut self,
        proposition: &ClickProposition,
    ) -> Result<CProposition, String> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => Ok(CProposition::Comparison {
                left: self.lower_invariant_contract_expression(left)?,
                operator: c_comparison_operator(*operator),
                right: self.lower_invariant_contract_expression(right)?,
            }),
            ClickProposition::Preserves(segment) => {
                self.lower_preserves_segment_to_c_proposition(segment)
            }
            ClickProposition::WritesOnly(_) => {
                Err("`writes_only(...)` is not available in loop invariants yet".to_string())
            }
            ClickProposition::And(left, right) => Ok(CProposition::And(
                Box::new(self.click_proposition_to_c_proposition(left)?),
                Box::new(self.click_proposition_to_c_proposition(right)?),
            )),
            ClickProposition::Or(left, right) => Ok(CProposition::Or(
                Box::new(self.click_proposition_to_c_proposition(left)?),
                Box::new(self.click_proposition_to_c_proposition(right)?),
            )),
            ClickProposition::Not(body) => Ok(CProposition::Not(Box::new(
                self.click_proposition_to_c_proposition(body)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(CProposition::Implies(
                Box::new(self.click_proposition_to_c_proposition(left)?),
                Box::new(self.click_proposition_to_c_proposition(right)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err("only `forall (int32 ...)` is supported".to_string());
                }
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let previous = self.quantified_values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_c_proposition(body)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                Ok(CProposition::ForAllInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                })
            }
        }
    }

    fn lower_preserves_segment_to_c_proposition(
        &mut self,
        segment: &ContractSegment,
    ) -> Result<CProposition, String> {
        if segment.state != ContractSegmentState::Current {
            return Err("`preserves(...)` expects a current-state segment".to_string());
        }

        let variable = Variable(self.next_quantifier_variable);
        self.next_quantifier_variable += 1;
        let index_name = format!("__click_segment_index_{}", variable.0);
        let index = CExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
        let base = self.lower_current_invariant_c_expression(&segment.base)?;
        let start = self.lower_current_invariant_c_expression(&segment.start)?;
        let end = self.lower_current_invariant_c_expression(&segment.end)?;
        let current = CExpression::Index(Box::new(base.clone()), Box::new(index.clone()));
        let old = CExpression::Value(self.evaluate_old_invariant_c_expression(
            &CExpression::Index(Box::new(segment.base.clone()), Box::new(index.clone())),
        )?);

        Ok(CProposition::ForAllInt32 {
            name: index_name,
            variable,
            body: Box::new(segment_preservation_body(start, end, index, current, old)),
        })
    }

    fn lower_invariant_contract_expression(
        &self,
        expression: &ContractExpression,
    ) -> Result<CExpression, String> {
        match expression {
            ContractExpression::Current(expression) => {
                self.lower_current_invariant_c_expression(expression)
            }
            ContractExpression::Old(expression) => Ok(CExpression::Value(
                self.evaluate_old_invariant_c_expression(expression)?,
            )),
            ContractExpression::Add(left, right) => Ok(CExpression::Add(
                Box::new(self.lower_invariant_contract_expression(left)?),
                Box::new(self.lower_invariant_contract_expression(right)?),
            )),
            ContractExpression::Subtract(left, right) => Ok(CExpression::Subtract(
                Box::new(self.lower_invariant_contract_expression(left)?),
                Box::new(self.lower_invariant_contract_expression(right)?),
            )),
            ContractExpression::Index(base, index) => Ok(CExpression::Index(
                Box::new(self.lower_invariant_contract_expression(base)?),
                Box::new(self.lower_invariant_contract_expression(index)?),
            )),
        }
    }

    fn lower_current_invariant_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(CExpression::Value(value.clone())),
            CExpression::Variable(name) => Ok(self
                .quantified_values
                .get(name)
                .cloned()
                .map(CExpression::Value)
                .unwrap_or_else(|| CExpression::Variable(name.clone()))),
            CExpression::Add(left, right) => Ok(CExpression::Add(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Index(base, index) => Ok(CExpression::Index(
                Box::new(self.lower_current_invariant_c_expression(base)?),
                Box::new(self.lower_current_invariant_c_expression(index)?),
            )),
            expression => Err(format!(
                "unsupported expression in loop invariant: `{expression:?}`"
            )),
        }
    }

    fn evaluate_old_invariant_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CValue, String> {
        match expression {
            CExpression::Value(value) => Ok(value.clone()),
            CExpression::Variable(name) if name == "result" => {
                Err("`result` is not available inside `old(...)`".to_string())
            }
            CExpression::Variable(name) => self
                .quantified_values
                .get(name)
                .or_else(|| self.entry_values.get(name))
                .cloned()
                .ok_or_else(|| format!("unknown old-state variable `{name}`")),
            CExpression::Add(left, right) => {
                let left = self.evaluate_old_invariant_c_expression(left)?;
                let right = self.evaluate_old_invariant_c_expression(right)?;
                evaluate_postcondition_add(left, right)
            }
            CExpression::Subtract(left, right) => {
                let left = self.evaluate_old_invariant_c_expression(left)?;
                let right = self.evaluate_old_invariant_c_expression(right)?;
                evaluate_postcondition_sub(left, right)
            }
            CExpression::Index(base, index) => {
                let base = self.evaluate_old_invariant_c_expression(base)?;
                let index = self.evaluate_old_invariant_c_expression(index)?;
                let pointer = evaluate_postcondition_pointer_add(base, index)?;
                Ok(match self.entry_state.memory().load(&pointer) {
                    crate::megakernel::CExpressionOutcome::Value(value) => value,
                    _ => CValue::Int32(Bitvector32Term::MemoryLoad(
                        Box::new(self.entry_state.memory().clone()),
                        Box::new(pointer),
                    )),
                })
            }
            expression => Err(format!(
                "unsupported expression inside loop invariant `old(...)`: `{expression:?}`"
            )),
        }
    }

    fn loop_assert_checks(&self, loop_index: usize) -> Vec<LabeledCheck> {
        self.structural_clauses
            .iter()
            .filter(|clause| clause.target() == &StructuralTarget::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Assert)
            .enumerate()
            .map(|(item_index, item)| LabeledCheck {
                condition: click_proposition_to_c_expression(item.proposition())
                    .expect("structural propositions should be validated before lowering"),
                label: format!("loop {loop_index} assert {item_index}"),
            })
            .collect()
    }
}

fn structural_item_kind_label(kind: StructuralItemKind) -> &'static str {
    match kind {
        StructuralItemKind::Assert => "assert",
        StructuralItemKind::Invariant => "invariant",
    }
}

fn prepend_labeled_asserts(statement: CStatement, checks: &[LabeledCheck]) -> CStatement {
    checks.iter().rev().fold(statement, |statement, check| {
        c_seq(
            c_labeled_assert(check.condition.clone(), check.label.clone()),
            statement,
        )
    })
}

fn click_proposition_to_c_expression(proposition: &ClickProposition) -> Option<CExpression> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = contract_expression_to_current_c_expression(left)?;
            let right = contract_expression_to_current_c_expression(right)?;
            Some(match operator {
                ComparisonOperator::Equal => CExpression::Equal(Box::new(left), Box::new(right)),
                ComparisonOperator::NotEqual => {
                    CExpression::NotEqual(Box::new(left), Box::new(right))
                }
                ComparisonOperator::LessThan => {
                    CExpression::LessThan(Box::new(left), Box::new(right))
                }
                ComparisonOperator::LessEqual => {
                    CExpression::LessEqual(Box::new(left), Box::new(right))
                }
                ComparisonOperator::GreaterThan => {
                    CExpression::GreaterThan(Box::new(left), Box::new(right))
                }
                ComparisonOperator::GreaterEqual => {
                    CExpression::GreaterEqual(Box::new(left), Box::new(right))
                }
            })
        }
        ClickProposition::And(left, right) => Some(CExpression::And(
            Box::new(click_proposition_to_c_expression(left)?),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Or(left, right) => Some(CExpression::Or(
            Box::new(click_proposition_to_c_expression(left)?),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Not(body) => Some(CExpression::Not(Box::new(
            click_proposition_to_c_expression(body)?,
        ))),
        ClickProposition::Implies(left, right) => Some(CExpression::Or(
            Box::new(CExpression::Not(Box::new(
                click_proposition_to_c_expression(left)?,
            ))),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Preserves(_) => None,
        ClickProposition::WritesOnly(_) => None,
        ClickProposition::ForAll { .. } => None,
    }
}

fn c_comparison_operator(operator: ComparisonOperator) -> CComparisonOperator {
    match operator {
        ComparisonOperator::Equal => CComparisonOperator::Equal,
        ComparisonOperator::NotEqual => CComparisonOperator::NotEqual,
        ComparisonOperator::LessThan => CComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => CComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => CComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => CComparisonOperator::GreaterEqual,
    }
}

fn segment_preservation_body(
    start: CExpression,
    end: CExpression,
    index: CExpression,
    current: CExpression,
    old: CExpression,
) -> CProposition {
    CProposition::Implies(
        Box::new(CProposition::And(
            Box::new(CProposition::Comparison {
                left: start,
                operator: CComparisonOperator::LessEqual,
                right: index.clone(),
            }),
            Box::new(CProposition::Comparison {
                left: index,
                operator: CComparisonOperator::LessThan,
                right: end,
            }),
        )),
        Box::new(CProposition::Comparison {
            left: current,
            operator: CComparisonOperator::Equal,
            right: old,
        }),
    )
}

fn contract_expression_to_current_c_expression(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::Current(expression) => Some(expression.clone()),
        ContractExpression::Old(_) => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_to_current_c_expression(left)?),
            Box::new(contract_expression_to_current_c_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_to_current_c_expression(left)?),
            Box::new(contract_expression_to_current_c_expression(right)?),
        )),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_to_current_c_expression(base)?),
            Box::new(contract_expression_to_current_c_expression(index)?),
        )),
    }
}

fn count_loops(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => count_loops(first) + count_loops(second),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => count_loops(then_branch) + count_loops(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_loops(body),
        _ => 0,
    }
}

fn count_statements(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => {
            count_statements(first) + count_statements(second)
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => 1 + count_statements(then_branch) + count_statements(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_statements(body),
        _ => 1,
    }
}

fn initial_call(
    function_name: &str,
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
) -> Result<(CState, Vec<CExpression>, Vec<Proposition>), ClickError> {
    let mut valid_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, bytes)) = concrete_valid_range_block(requirement)? {
            valid_ranges.insert(name, bytes);
        }
    }
    let mut memory = CMemory::new();
    let mut arguments = Vec::new();

    for parameter in parameters {
        match parameter.c_type() {
            C0Type::Int32Pointer => {
                if let Some(bytes) = valid_ranges.get(parameter.name()) {
                    memory = memory.with_block(parameter.name(), *bytes);
                }
                arguments.push(c_pointer_value(Pointer {
                    block: parameter.name().to_string(),
                    offset: PointerOffsetTerm::Constant(0),
                }));
            }
            C0Type::Int32 => {
                arguments.push(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
        }
    }

    for name in requires.iter().filter_map(requirement_valid_range_name) {
        if !parameters.iter().any(|parameter| parameter.name() == name) {
            return Err(ClickError::new(format!(
                "`valid_range` names `{name}`, but `{}` has no such parameter",
                function_name
            )));
        }
    }

    memory = memory_with_symbolic_valid_range_cells(memory, &valid_ranges);
    let requirement_propositions =
        requirement_propositions(requires, parameters, &arguments, &memory)?;
    Ok((
        CState::new().with_memory(memory),
        arguments,
        requirement_propositions,
    ))
}

fn memory_with_symbolic_valid_range_cells(
    mut memory: CMemory,
    valid_ranges: &BTreeMap<&str, u32>,
) -> CMemory {
    let base_memory = memory.clone();
    for (name, bytes) in valid_ranges {
        let mut offset: u32 = 0;
        while offset.checked_add(4).is_some_and(|end| end <= *bytes) {
            let pointer = Pointer {
                block: (*name).to_string(),
                offset: PointerOffsetTerm::Constant(i64::from(offset)),
            };
            let value = CValue::Int32(Bitvector32Term::MemoryLoad(
                Box::new(base_memory.clone()),
                Box::new(pointer.clone()),
            ));
            memory = memory.store(pointer, value);
            offset += 4;
        }
    }
    memory
}

fn requirement_propositions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Vec<Proposition>, ClickError> {
    requires
        .iter()
        .map(|requirement| match requirement {
            Requirement::ValidRange { .. } | Requirement::ValidRangeSegment { .. } => {
                valid_range_requirement_prop(requirement, parameters, arguments, memory)
            }
            Requirement::Proposition(proposition) => {
                requirement_proposition_prop(parameters, arguments, proposition)
            }
        })
        .collect()
}

fn valid_range_requirement_prop(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Proposition, ClickError> {
    let (base, bytes) = valid_range_base_and_bytes(requirement, parameters, arguments)?;
    Ok(Proposition::CMemoryValidRange {
        memory: memory.clone(),
        base,
        bytes,
    })
}

fn requirement_valid_range_name(requirement: &Requirement) -> Option<&str> {
    match requirement {
        Requirement::ValidRange { name, .. } | Requirement::ValidRangeSegment { name, .. } => {
            Some(name)
        }
        Requirement::Proposition(_) => None,
    }
}

fn concrete_valid_range_block(
    requirement: &Requirement,
) -> Result<Option<(&str, u32)>, ClickError> {
    match requirement {
        Requirement::ValidRange { name, bytes } => {
            Ok(range_bytes_constant(bytes).map(|bytes| (name.as_str(), bytes)))
        }
        Requirement::ValidRangeSegment { name, start, end } => {
            let (Some(start), Some(end)) = (range_bytes_constant(start), range_bytes_constant(end))
            else {
                return Ok(None);
            };
            if start != 0 {
                return Ok(None);
            }
            let bytes = end.checked_mul(4).ok_or_else(|| {
                ClickError::new(format!(
                    "`valid_range({name}[0..{end}])` overflows byte count"
                ))
            })?;
            Ok(Some((name.as_str(), bytes)))
        }
        Requirement::Proposition(_) => Ok(None),
    }
}

fn valid_range_base_and_bytes(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<(Pointer, Bitvector32Term), ClickError> {
    let Some(name) = requirement_valid_range_name(requirement) else {
        return Err(ClickError::new("expected valid_range requirement"));
    };
    let Some((_, argument)) = parameters
        .iter()
        .zip(arguments)
        .find(|(parameter, _)| parameter.name() == name)
    else {
        return Err(ClickError::new(format!(
            "`valid_range` names `{name}`, but no such parameter exists"
        )));
    };
    let CExpression::Value(CValue::Pointer(base)) = argument else {
        return Err(ClickError::new(format!(
            "`valid_range` names `{name}`, but it is not a pointer parameter"
        )));
    };
    let parameter_values = parameter_values(parameters, arguments)?;

    match requirement {
        Requirement::ValidRange { bytes, .. } => {
            Ok((base.clone(), lower_range_bytes(bytes, &parameter_values)?))
        }
        Requirement::ValidRangeSegment { start, end, .. } => {
            if let (Some(start), Some(end)) =
                (range_bytes_constant(start), range_bytes_constant(end))
            {
                if end < start {
                    return Err(ClickError::new(format!(
                        "`valid_range({name}[{start}..{end}])` has an end before its start"
                    )));
                }
            }
            let start = lower_range_bytes(start, &parameter_values)?;
            let end = lower_range_bytes(end, &parameter_values)?;
            let element_count = bitvector32_subtract(end, start.clone());
            let bytes = bitvector32_multiply(element_count, Bitvector32Term::Constant(4));
            Ok((offset_pointer_by_int32_elements(base.clone(), start), bytes))
        }
        Requirement::Proposition(_) => Err(ClickError::new("expected valid_range requirement")),
    }
}

fn range_bytes_constant(bytes: &RangeBytes) -> Option<u32> {
    match bytes {
        RangeBytes::Constant(value) => Some(*value),
        RangeBytes::Parameter(_) => None,
        RangeBytes::Add(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_add(range_bytes_constant(right)?))
        }
        RangeBytes::Subtract(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_sub(range_bytes_constant(right)?))
        }
        RangeBytes::Multiply(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_mul(range_bytes_constant(right)?))
        }
    }
}

fn lower_range_bytes(
    bytes: &RangeBytes,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<Bitvector32Term, ClickError> {
    match bytes {
        RangeBytes::Constant(value) => Ok(Bitvector32Term::Constant(*value)),
        RangeBytes::Parameter(name) => match parameter_values.get(name) {
            Some(CValue::Int32(bits)) => Ok(bits.clone()),
            Some(_) => Err(ClickError::new(format!(
                "`valid_range` byte expression references pointer parameter `{name}`"
            ))),
            None => Err(ClickError::new(format!(
                "`valid_range` byte expression references unknown parameter `{name}`"
            ))),
        },
        RangeBytes::Add(left, right) => Ok(bitvector32_add(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
        RangeBytes::Subtract(left, right) => Ok(bitvector32_subtract(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
        RangeBytes::Multiply(left, right) => Ok(bitvector32_multiply(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
    }
}

fn requirement_proposition_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    proposition: &ClickProposition,
) -> Result<Proposition, ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;
    let mut lowerer = KernelPropositionLowerer::new(parameter_values);
    lowerer.lower_requirement_proposition(proposition)
}

fn parameter_values(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<BTreeMap<String, CValue>, ClickError> {
    parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            let CExpression::Value(value) = argument else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    parameter.name()
                )));
            };
            Ok((parameter.name().to_string(), value.clone()))
        })
        .collect()
}

struct KernelPropositionLowerer {
    values: BTreeMap<String, CValue>,
    next_variable: u64,
}

impl KernelPropositionLowerer {
    fn new(values: BTreeMap<String, CValue>) -> Self {
        Self {
            values,
            next_variable: 2_000_000,
        }
    }

    fn lower_requirement_proposition(
        &mut self,
        proposition: &ClickProposition,
    ) -> Result<Proposition, ClickError> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                comparison_proposition(left, *operator, right)
            }
            ClickProposition::Preserves(_) => Err(ClickError::new(
                "`preserves(...)` is not available in `requires` clauses",
            )),
            ClickProposition::WritesOnly(_) => Err(ClickError::new(
                "`writes_only(...)` is not available in `requires` clauses",
            )),
            ClickProposition::And(left, right) => Ok(Proposition::And(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Or(left, right) => Ok(Proposition::Or(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
                self.lower_requirement_proposition(body)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(Proposition::Implies(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err(ClickError::new("only `forall (int32 ...)` is supported"));
                }
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let previous = self.values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.lower_requirement_proposition(body)?;
                match previous {
                    Some(value) => {
                        self.values.insert(name.clone(), value);
                    }
                    None => {
                        self.values.remove(name);
                    }
                }
                Ok(Proposition::ForAll {
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                })
            }
        }
    }

    fn lower_requirement_value(
        &self,
        expression: &ContractExpression,
    ) -> Result<CValue, ClickError> {
        match expression {
            ContractExpression::Current(expression) => {
                self.lower_requirement_c_expression(expression)
            }
            ContractExpression::Old(_) => Err(ClickError::new(
                "`old(...)` is not available in `requires` clauses",
            )),
            ContractExpression::Add(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_add(left, right)
            }
            ContractExpression::Subtract(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_subtract(left, right)
            }
            ContractExpression::Index(_, _) => Err(ClickError::new(
                "memory reads are not supported in `requires` propositions yet",
            )),
        }
    }

    fn lower_requirement_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CValue, ClickError> {
        match expression {
            CExpression::Value(value) => Ok(value.clone()),
            CExpression::Variable(name) => {
                self.values.get(name).cloned().ok_or_else(|| {
                    ClickError::new(format!("unknown requirement variable `{name}`"))
                })
            }
            CExpression::Add(left, right) => lower_contract_add(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Subtract(left, right) => lower_contract_subtract(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            _ => Err(ClickError::new(format!(
                "unsupported expression in `requires` proposition: `{expression:?}`"
            ))),
        }
    }
}

fn comparison_proposition(
    left: CValue,
    operator: ComparisonOperator,
    right: CValue,
) -> Result<Proposition, ClickError> {
    let CValue::Int32(left) = left else {
        return Err(ClickError::new("left side of proposition is not int32"));
    };
    let CValue::Int32(right) = right else {
        return Err(ClickError::new("right side of proposition is not int32"));
    };
    let Some((condition, value)) = comparison_condition(left, operator, right) else {
        return Err(ClickError::new("unsupported proposition comparison"));
    };
    Ok(Proposition::ConditionIs(condition, value))
}

fn lower_contract_add(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            Ok(CValue::Int32(bitvector32_add(left, right)))
        }
        (CValue::Pointer(pointer), CValue::Int32(index))
        | (CValue::Int32(index), CValue::Pointer(pointer)) => Ok(CValue::Pointer(
            offset_pointer_by_int32_elements(pointer, index),
        )),
        (left, right) => Err(ClickError::new(format!(
            "cannot add `{left:?}` and `{right:?}` in proposition"
        ))),
    }
}

fn lower_contract_subtract(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            Ok(CValue::Int32(bitvector32_subtract(left, right)))
        }
        (CValue::Pointer(pointer), CValue::Int32(index)) => {
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(ClickError::new(format!(
            "cannot subtract `{right:?}` from `{left:?}` in proposition"
        ))),
    }
}

fn bitvector32_add(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_add(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ => Bitvector32Term::Add(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_subtract(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        _ if left == right => Bitvector32Term::Constant(0),
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_multiply(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_mul(*right))
        }
        (_, Bitvector32Term::Constant(1)) => left,
        (Bitvector32Term::Constant(1), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ => Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
    }
}

fn signed_less_than(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) < (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
    }
}

fn signed_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) <= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
    }
}

fn signed_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) > (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
    }
}

fn signed_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) >= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant(left == right)
        }
        _ => ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
    }
}

fn check_ensure(
    ensure_label: &str,
    path_index: usize,
    path_facts: &[crate::megakernel::PathFact],
    available_propositions: &[Proposition],
    ensure_clause: &EnsureClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    match ensure_clause.ensure() {
        Ensure::Proposition(proposition) => prove_ensure_proposition(
            ensure_label,
            path_index,
            path_facts,
            available_propositions,
            proposition,
            parameters,
            arguments,
            pre_state,
            outcome,
        )?,
    }

    Ok(())
}

fn prove_ensure_proposition(
    ensure_label: &str,
    path_index: usize,
    path_facts: &[crate::megakernel::PathFact],
    available_propositions: &[Proposition],
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => match outcome {
            CFunctionOutcome::Return { value, state } => {
                let left_value = evaluate_contract_expression(
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    value,
                    available_propositions,
                    left,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: could not evaluate left side: {message}"
                    ))
                })?;
                let right_value = evaluate_contract_expression(
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    value,
                    available_propositions,
                    right,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: could not evaluate right side: {message}"
                    ))
                })?;
                prove_value_comparison(
                    &left_value,
                    *operator,
                    &right_value,
                    available_propositions,
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: left side evaluated to {left_value:?}, right side evaluated to {right_value:?}\n  path facts: {}",
                        describe_facts(path_facts)
                    ))
                })?;
            }
            other => {
                return Err(ClickError::new(format!(
                    "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: outcome was {other:?}\n  path facts: {}",
                    describe_facts(path_facts)
                )));
            }
        },
        ClickProposition::WritesOnly(segment) => match outcome {
            CFunctionOutcome::Return { value, state } => prove_writes_only_segment(
                ensure_label,
                path_index,
                path_facts,
                available_propositions,
                parameters,
                arguments,
                pre_state,
                state,
                value,
                segment,
            )?,
            other => {
                return Err(ClickError::new(format!(
                    "`ensures writes_only({segment:?})` failed for `{ensure_label}` path {path_index}: outcome was {other:?}\n  path facts: {}",
                    describe_facts(path_facts)
                )));
            }
        },
        ClickProposition::And(left, right) => {
            prove_ensure_proposition(
                ensure_label,
                path_index,
                path_facts,
                available_propositions,
                left,
                parameters,
                arguments,
                pre_state,
                outcome,
            )?;
            prove_ensure_proposition(
                ensure_label,
                path_index,
                path_facts,
                available_propositions,
                right,
                parameters,
                arguments,
                pre_state,
                outcome,
            )?;
        }
        _ => {
            let CFunctionOutcome::Return { value, state } = outcome else {
                return Err(ClickError::new(format!(
                    "`ensures {proposition:?}` failed for `{ensure_label}` path {path_index}: outcome was {outcome:?}\n  path facts: {}",
                    describe_facts(path_facts)
                )));
            };
            let proposition = lower_outcome_proposition(
                parameters,
                arguments,
                pre_state,
                state,
                value,
                available_propositions,
                proposition,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`ensures {proposition:?}` failed for `{ensure_label}` path {path_index}: could not lower proposition: {message}"
                ))
            })?;
            let assumptions = assumptions_from_propositions(available_propositions);
            if !assumptions.proves(&proposition) {
                return Err(ClickError::new(format!(
                    "`ensures {proposition:?}` failed for `{ensure_label}` path {path_index}: proposition was not provable\n  path facts: {}",
                    describe_facts(path_facts)
                )));
            }
        }
    }
    Ok(())
}

fn prove_writes_only_segment(
    ensure_label: &str,
    path_index: usize,
    path_facts: &[crate::megakernel::PathFact],
    available_propositions: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    segment: &ContractSegment,
) -> Result<(), ClickError> {
    if segment.state != ContractSegmentState::Current {
        return Err(ClickError::new(format!(
            "`ensures writes_only({segment:?})` failed for `{ensure_label}` path {path_index}: expected a current-state segment"
        )));
    }
    let segment = evaluate_contract_segment(
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        available_propositions,
        segment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`ensures writes_only({segment:?})` failed for `{ensure_label}` path {path_index}: could not evaluate segment: {message}"
        ))
    })?;
    let assumptions = assumptions_from_propositions(available_propositions);
    let mut writes = post_state
        .memory()
        .differing_cell_pointers(pre_state.memory())
        .into_iter()
        .filter(is_frame_relevant_pointer)
        .collect::<BTreeSet<_>>();
    writes.extend(
        path_facts
            .iter()
            .filter_map(|fact| match fact.proposition() {
                Proposition::CMemoryWritesOnly { pointers, .. } => Some(pointers.as_slice()),
                _ => None,
            })
            .flatten()
            .cloned(),
    );
    writes.retain(is_frame_relevant_pointer);

    for pointer in &writes {
        if !segment_contains_pointer(&segment, pointer, &assumptions) {
            return Err(ClickError::new(format!(
                "`ensures writes_only({:?})` failed for `{ensure_label}` path {path_index}: write to {pointer:?} is outside the segment\n  path facts: {}",
                segment.source,
                describe_facts(path_facts)
            )));
        }
    }

    Ok(())
}

fn is_frame_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct EvaluatedContractSegment {
    source: ContractSegment,
    base: Pointer,
    start: Bitvector32Term,
    end: Bitvector32Term,
}

fn evaluate_contract_segment(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_propositions: &[Proposition],
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let assumptions = assumptions_from_propositions(available_propositions);
    let (state, result) = match segment.state {
        ContractSegmentState::Current => (post_state, Some(result)),
        ContractSegmentState::Old => (pre_state, None),
    };
    let base = evaluate_c_contract_expression(
        &parameter_values,
        state,
        result,
        &assumptions,
        &segment.base,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_c_contract_expression(
        &parameter_values,
        state,
        result,
        &assumptions,
        &segment.start,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_c_contract_expression(
        &parameter_values,
        state,
        result,
        &assumptions,
        &segment.end,
    )?;
    let CValue::Int32(end) = end else {
        return Err("segment end did not evaluate to int32".to_string());
    };

    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base,
        start,
        end,
    })
}

fn segment_contains_pointer(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    let Some(index) = pointer_element_index_from_base(pointer, &segment.base) else {
        return false;
    };
    assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        signed_less_than(index, segment.end.clone()),
        true,
    ))
}

fn pointer_element_index_from_base(pointer: &Pointer, base: &Pointer) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return int32_element_index_from_pointer_offset(&pointer.offset);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            int32_element_index_from_pointer_offset(left)
        }
        _ => None,
    }
}

fn int32_element_index_from_pointer_offset(offset: &PointerOffsetTerm) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % 4 == 0 => {
            let index = offset / 4;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width == 4 => {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            int32_element_index_from_pointer_offset(left)
        }
        _ => None,
    }
}

fn prove_value_comparison(
    actual: &CValue,
    operator: ComparisonOperator,
    expected: &CValue,
    available_propositions: &[Proposition],
) -> Option<()> {
    let CValue::Int32(actual) = actual else {
        return None;
    };
    let CValue::Int32(expected) = expected else {
        return None;
    };
    let (condition, value) = comparison_condition(actual.clone(), operator, expected.clone())?;
    let assumptions = available_propositions
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition);
    assumptions
        .proves(&Proposition::ConditionIs(condition, value))
        .then_some(())
}

fn comparison_condition(
    actual: Bitvector32Term,
    operator: ComparisonOperator,
    expected: Bitvector32Term,
) -> Option<(ConditionTerm, bool)> {
    match operator {
        ComparisonOperator::Equal => Some((bitvector32_equal(actual, expected), true)),
        ComparisonOperator::NotEqual => Some((bitvector32_equal(actual, expected), false)),
        ComparisonOperator::LessThan => Some((signed_less_than(actual, expected), true)),
        ComparisonOperator::LessEqual => Some((signed_less_equal(actual, expected), true)),
        ComparisonOperator::GreaterThan => Some((signed_greater_than(actual, expected), true)),
        ComparisonOperator::GreaterEqual => Some((signed_greater_equal(actual, expected), true)),
    }
}

fn evaluate_contract_expression(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_propositions: &[Proposition],
    expression: &ContractExpression,
) -> Result<CValue, String> {
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let assumptions = assumptions_from_propositions(available_propositions);
    evaluate_contract_expression_with_environment(
        &parameter_values,
        pre_state,
        post_state,
        result,
        &assumptions,
        expression,
    )
}

fn lower_outcome_proposition(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_propositions: &[Proposition],
    proposition: &ClickProposition,
) -> Result<Proposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let assumptions = assumptions_from_propositions(available_propositions);
    let mut next_variable = 2_000_000;
    lower_outcome_proposition_with_environment(
        &mut values,
        pre_state,
        post_state,
        result,
        &assumptions,
        proposition,
        &mut next_variable,
    )
}

fn lower_outcome_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &Assumptions,
    proposition: &ClickProposition,
    next_variable: &mut u64,
) -> Result<Proposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_contract_expression_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
            )?;
            let right = evaluate_contract_expression_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
            )?;
            comparison_proposition(left, *operator, right).map_err(|error| error.message)
        }
        ClickProposition::Preserves(segment) => lower_outcome_preserves_segment(
            values,
            pre_state,
            post_state,
            result,
            assumptions,
            segment,
            next_variable,
        ),
        ClickProposition::WritesOnly(_) => {
            Err("`writes_only(...)` can only be checked directly by `auto`".to_string())
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
            )?),
        )),
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
            )?,
        ))),
        ClickProposition::Implies(left, right) => {
            let left = lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                &right_assumptions,
                right,
                next_variable,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        ClickProposition::ForAll { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `forall (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::ForAll {
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
    }
}

fn lower_outcome_preserves_segment(
    values: &mut BTreeMap<String, CValue>,
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &Assumptions,
    segment: &ContractSegment,
    next_variable: &mut u64,
) -> Result<Proposition, String> {
    if segment.state != ContractSegmentState::Current {
        return Err("`preserves(...)` expects a current-state segment".to_string());
    }

    let variable = Variable(*next_variable);
    *next_variable += 1;
    let index = Bitvector32Term::Variable(variable);
    let index_value = CValue::Int32(index.clone());
    let base = evaluate_c_contract_expression(
        values,
        post_state,
        Some(result),
        assumptions,
        &segment.base,
    )?;
    let start = evaluate_c_contract_expression(
        values,
        post_state,
        Some(result),
        assumptions,
        &segment.start,
    )?;
    let end = evaluate_c_contract_expression(
        values,
        post_state,
        Some(result),
        assumptions,
        &segment.end,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let CValue::Int32(end) = end else {
        return Err("segment end did not evaluate to int32".to_string());
    };

    let lower_bound = comparison_proposition(
        CValue::Int32(start),
        ComparisonOperator::LessEqual,
        index_value.clone(),
    )
    .map_err(|error| error.message)?;
    let upper_bound = comparison_proposition(
        index_value.clone(),
        ComparisonOperator::LessThan,
        CValue::Int32(end),
    )
    .map_err(|error| error.message)?;
    let range = Proposition::And(Box::new(lower_bound), Box::new(upper_bound));
    let range_assumptions = assumptions.clone().assume_proposition(range.clone());

    let pointer = evaluate_postcondition_pointer_add(base, index_value)?;
    let current = evaluate_contract_memory_load(post_state, pointer.clone(), &range_assumptions)?;
    let old = evaluate_contract_memory_load(pre_state, pointer, &range_assumptions)?;
    let equality = comparison_proposition(current, ComparisonOperator::Equal, old)
        .map_err(|error| error.message)?;

    Ok(Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(Box::new(range), Box::new(equality))),
    })
}

fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &Assumptions,
    expression: &ContractExpression,
) -> Result<CValue, String> {
    match expression {
        ContractExpression::Current(expression) => evaluate_c_contract_expression(
            parameter_values,
            post_state,
            Some(result),
            assumptions,
            expression,
        ),
        ContractExpression::Old(expression) => evaluate_c_contract_expression(
            parameter_values,
            pre_state,
            None,
            assumptions,
            expression,
        ),
        ContractExpression::Add(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_add(left, right)
        }
        ContractExpression::Subtract(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        ContractExpression::Index(base, index) => {
            let base = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                assumptions,
                base,
            )?;
            let index = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                assumptions,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            evaluate_contract_memory_load(post_state, pointer, assumptions)
        }
    }
}

fn evaluate_c_contract_expression(
    parameter_values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &CExpression,
) -> Result<CValue, String> {
    match expression {
        CExpression::Value(value) => Ok(value.clone()),
        CExpression::Variable(name) if name == "result" => result
            .cloned()
            .ok_or_else(|| "`result` is not available inside `old(...)`".to_string()),
        CExpression::Variable(name) => parameter_values
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown contract variable `{name}`")),
        CExpression::Add(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_add(left, right)
        }
        CExpression::Subtract(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        CExpression::Index(base, index) => {
            let base =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, base)?;
            let index = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            evaluate_contract_memory_load(state, pointer, assumptions)
        }
        _ => Err(format!(
            "unsupported postcondition expression `{expression:?}`"
        )),
    }
}

fn evaluate_contract_memory_load(
    state: &CState,
    pointer: Pointer,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    match state.memory().load(&pointer) {
        crate::megakernel::CExpressionOutcome::Value(value) => Ok(value),
        _ if assumptions.proves(&Proposition::CMemoryCanLoad {
            memory: state.memory().clone(),
            pointer: pointer.clone(),
        }) =>
        {
            Ok(CValue::Int32(Bitvector32Term::MemoryLoad(
                Box::new(state.memory().clone()),
                Box::new(pointer),
            )))
        }
        outcome => Err(format!("load from {pointer:?} produced {outcome:?}")),
    }
}

fn evaluate_postcondition_add(left: CValue, right: CValue) -> Result<CValue, String> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            Ok(CValue::Int32(bitvector32_add(left, right)))
        }
        (CValue::Pointer(pointer), CValue::Int32(index))
        | (CValue::Int32(index), CValue::Pointer(pointer)) => Ok(CValue::Pointer(
            offset_pointer_by_int32_elements(pointer, index),
        )),
        (left, right) => Err(format!("cannot add `{left:?}` and `{right:?}`")),
    }
}

fn evaluate_postcondition_sub(left: CValue, right: CValue) -> Result<CValue, String> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            Ok(CValue::Int32(bitvector32_subtract(left, right)))
        }
        (CValue::Pointer(pointer), CValue::Int32(index)) => {
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(format!("cannot subtract `{right:?}` from `{left:?}`")),
    }
}

fn evaluate_postcondition_pointer_add(left: CValue, right: CValue) -> Result<Pointer, String> {
    match evaluate_postcondition_add(left, right)? {
        CValue::Pointer(pointer) => Ok(pointer),
        value => Err(format!(
            "index base did not evaluate to a pointer: `{value:?}`"
        )),
    }
}

fn offset_pointer_by_int32_elements(pointer: Pointer, elements: Bitvector32Term) -> Pointer {
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(pointer.offset, scale_int32_offset(elements, 4)),
    }
}

fn add_pointer_offset(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

fn scale_int32_offset(value: Bitvector32Term, byte_width: i64) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(u32),
    String(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    Comma,
    Semicolon,
    DotDot,
    EqualEqual,
    BangEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Plus,
    Minus,
    Star,
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn new(source: &str) -> Result<Self, ClickError> {
        Ok(Self {
            tokens: tokenize(source)?,
            position: 0,
        })
    }

    fn parse_file(mut self) -> Result<ClickFile, ClickError> {
        let mut verifying_sources = Vec::new();
        let mut function_blocks = Vec::new();

        while self.peek().is_some() {
            if self.peek_ident() == Some("verifying") {
                verifying_sources.push(self.parse_verifying_source()?);
            } else {
                function_blocks.push(self.parse_function_block()?);
            }
        }

        Ok(ClickFile {
            verifying_sources,
            function_blocks,
        })
    }

    fn parse_verifying_source(&mut self) -> Result<String, ClickError> {
        self.expect_ident_spelling("verifying")?;
        let source_path = self.expect_string("C source path")?;
        self.expect(Token::Semicolon)?;
        Ok(source_path)
    }

    fn parse_function_block(&mut self) -> Result<FunctionBlock, ClickError> {
        let signature = self.parse_function_signature()?;
        self.expect(Token::LBrace)?;

        let mut requires = Vec::new();
        let mut structural_clauses = Vec::new();
        let mut ensures = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("requires") => requires.push(self.parse_requirement()?),
                Some("loop" | "statement") => {
                    structural_clauses.push(self.parse_structural_clause()?)
                }
                Some("ensures") => ensures.push(self.parse_ensure_clause()?),
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `requires`, `loop`, `statement`, `ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `requires`, `loop`, `statement`, `ensures`, or `}}` in `{}`",
                        signature.name()
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;

        if ensures.is_empty() {
            return Err(self.error(format!(
                "`{}` must contain at least one `ensures` clause",
                signature.name()
            )));
        }

        Ok(FunctionBlock {
            signature,
            requires,
            structural_clauses,
            ensures,
        })
    }

    fn parse_function_signature(&mut self) -> Result<FunctionSignature, ClickError> {
        let return_type = self.parse_type()?;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;

        Ok(FunctionSignature {
            return_type,
            name,
            parameters,
        })
    }

    fn parse_parameters(&mut self) -> Result<Vec<FunctionParameter>, ClickError> {
        let mut parameters = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(parameters);
        }

        loop {
            let c_type = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            let c_type = self.parse_parameter_array_suffix(c_type)?;
            parameters.push(FunctionParameter { c_type, name });

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => return Ok(parameters),
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    fn parse_type(&mut self) -> Result<C0Type, ClickError> {
        self.expect_ident_spelling("int32")?;
        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            Ok(C0Type::Int32Pointer)
        } else {
            Ok(C0Type::Int32)
        }
    }

    fn parse_parameter_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, ClickError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        if c_type != C0Type::Int32 {
            return Err(self.error("only `int32 name[]` array parameters are supported"));
        }

        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(C0Type::Int32Pointer)
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        if self.peek_ident() != Some("valid_range") || self.peek_next() != Some(&Token::LParen) {
            let proposition = self.parse_proposition()?;
            self.expect(Token::Semicolon)?;
            return Ok(Requirement::Proposition(proposition));
        }

        self.expect_ident_spelling("valid_range")?;
        self.expect(Token::LParen)?;
        let name = self.expect_ident("range base name")?;
        let requirement = if self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let start = self.parse_range_bytes()?;
            self.expect(Token::DotDot)?;
            let end = self.parse_range_bytes()?;
            self.expect(Token::RBracket)?;
            Requirement::ValidRangeSegment { name, start, end }
        } else {
            self.expect(Token::Comma)?;
            let bytes = self.parse_range_bytes()?;
            Requirement::ValidRange { name, bytes }
        };
        self.expect(Token::RParen)?;
        self.expect(Token::Semicolon)?;

        Ok(requirement)
    }

    fn parse_range_bytes(&mut self) -> Result<RangeBytes, ClickError> {
        self.parse_range_bytes_add()
    }

    fn parse_range_bytes_add(&mut self) -> Result<RangeBytes, ClickError> {
        let mut expression = self.parse_range_bytes_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_range_bytes_multiply()?;
                    RangeBytes::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_range_bytes_multiply()?;
                    RangeBytes::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_range_bytes_multiply(&mut self) -> Result<RangeBytes, ClickError> {
        let mut expression = self.parse_range_bytes_primary()?;
        while self.peek() == Some(&Token::Star) {
            self.position += 1;
            let right = self.parse_range_bytes_primary()?;
            expression = RangeBytes::Multiply(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_range_bytes_primary(&mut self) -> Result<RangeBytes, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(RangeBytes::Parameter(name)),
            Some(Token::Number(value)) => Ok(RangeBytes::Constant(value)),
            Some(Token::LParen) => {
                let expression = self.parse_range_bytes()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!(
                "expected valid_range byte expression, got {token:?}"
            ))),
            None => Err(self.error("expected valid_range byte expression, got end of input")),
        }
    }

    fn parse_structural_clause(&mut self) -> Result<StructuralClause, ClickError> {
        let target = self.parse_structural_target()?;
        self.expect(Token::LBrace)?;
        let mut items = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            items.push(self.parse_structural_item()?);
        }
        self.expect(Token::RBrace)?;
        if items.is_empty() {
            return Err(self.error("structural proof block must contain at least one item"));
        }
        Ok(StructuralClause { target, items })
    }

    fn parse_structural_target(&mut self) -> Result<StructuralTarget, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "loop" => {
                Ok(StructuralTarget::Loop(self.expect_index("loop index")?))
            }
            Some(Token::Ident(kind)) if kind == "statement" => Ok(StructuralTarget::Statement(
                self.expect_index("statement index")?,
            )),
            Some(Token::Ident(kind)) => {
                Err(self.error(format!("expected `loop` or `statement`, got `{kind}`")))
            }
            Some(token) => {
                Err(self.error(format!("expected `loop` or `statement`, got {token:?}")))
            }
            None => Err(self.error("expected `loop` or `statement`, got end of input")),
        }
    }

    fn parse_structural_item(&mut self) -> Result<StructuralItem, ClickError> {
        let kind = match self.next() {
            Some(Token::Ident(kind)) if kind == "invariant" => StructuralItemKind::Invariant,
            Some(Token::Ident(kind)) if kind == "assert" => StructuralItemKind::Assert,
            Some(Token::Ident(kind)) => {
                return Err(self.error(format!("expected `invariant` or `assert`, got `{kind}`")));
            }
            Some(token) => {
                return Err(self.error(format!("expected `invariant` or `assert`, got {token:?}")));
            }
            None => {
                return Err(self.error("expected `invariant` or `assert`, got end of input"));
            }
        };
        let proposition = self.parse_proposition()?;
        let proof = self.parse_by_clause()?;
        Ok(StructuralItem {
            kind,
            proposition,
            proof,
        })
    }

    fn parse_ensure_clause(&mut self) -> Result<EnsureClause, ClickError> {
        self.expect_ident_spelling("ensures")?;
        let name = if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next() == Some(&Token::Colon)
        {
            let name = self.expect_ident("ensure name")?;
            self.expect(Token::Colon)?;
            Some(name)
        } else {
            None
        };
        let ensure = self.parse_ensure_condition()?;
        let proof = self.parse_by_clause()?;

        Ok(EnsureClause {
            name,
            ensure,
            proof,
        })
    }

    fn parse_ensure_condition(&mut self) -> Result<Ensure, ClickError> {
        Ok(Ensure::Proposition(self.parse_proposition()?))
    }

    fn parse_proposition(&mut self) -> Result<ClickProposition, ClickError> {
        self.parse_proposition_implies()
    }

    fn parse_proposition_implies(&mut self) -> Result<ClickProposition, ClickError> {
        let left = self.parse_proposition_or()?;
        if self.peek_ident() == Some("implies") {
            self.position += 1;
            let right = self.parse_proposition_implies()?;
            Ok(ClickProposition::Implies(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_proposition_or(&mut self) -> Result<ClickProposition, ClickError> {
        let mut proposition = self.parse_proposition_and()?;
        while self.peek_ident() == Some("or") {
            self.position += 1;
            let right = self.parse_proposition_and()?;
            proposition = ClickProposition::Or(Box::new(proposition), Box::new(right));
        }
        Ok(proposition)
    }

    fn parse_proposition_and(&mut self) -> Result<ClickProposition, ClickError> {
        let mut proposition = self.parse_proposition_not()?;
        while self.peek_ident() == Some("and") {
            self.position += 1;
            let right = self.parse_proposition_not()?;
            proposition = ClickProposition::And(Box::new(proposition), Box::new(right));
        }
        Ok(proposition)
    }

    fn parse_proposition_not(&mut self) -> Result<ClickProposition, ClickError> {
        if self.peek_ident() == Some("not") {
            self.position += 1;
            Ok(ClickProposition::Not(Box::new(
                self.parse_proposition_not()?,
            )))
        } else {
            self.parse_proposition_atom()
        }
    }

    fn parse_proposition_atom(&mut self) -> Result<ClickProposition, ClickError> {
        if self.peek_ident() == Some("preserves") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let segment = self.parse_contract_segment()?;
            self.expect(Token::RParen)?;
            return Ok(ClickProposition::Preserves(segment));
        }

        if self.peek_ident() == Some("writes_only") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let segment = self.parse_contract_segment()?;
            self.expect(Token::RParen)?;
            return Ok(ClickProposition::WritesOnly(segment));
        }

        if self.peek_ident() == Some("forall") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let c_type = self.parse_type()?;
            let name = self.expect_ident("forall variable name")?;
            self.expect(Token::RParen)?;
            self.expect(Token::LBrace)?;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            return Ok(ClickProposition::ForAll {
                c_type,
                name,
                body: Box::new(body),
            });
        }

        if self.peek() == Some(&Token::LParen) {
            let start = self.position;
            self.position += 1;
            let grouped = self.parse_proposition().and_then(|proposition| {
                self.expect(Token::RParen)?;
                Ok(proposition)
            });
            if grouped.is_ok() {
                return grouped;
            }
            self.position = start;
        }

        self.parse_proposition_comparison()
    }

    fn parse_proposition_comparison(&mut self) -> Result<ClickProposition, ClickError> {
        let left = self.parse_contract_expression()?;
        let operator = self.parse_comparison_operator("proposition")?;
        let right = self.parse_contract_expression()?;

        Ok(ClickProposition::Comparison {
            left,
            operator,
            right,
        })
    }

    fn parse_comparison_operator(
        &mut self,
        clause: &str,
    ) -> Result<ComparisonOperator, ClickError> {
        let operator = self.next().ok_or_else(|| {
            self.error(format!(
                "expected comparison operator in `{clause}`, got end of input"
            ))
        })?;

        match operator {
            Token::LessThan => Ok(ComparisonOperator::LessThan),
            Token::LessEqual => Ok(ComparisonOperator::LessEqual),
            Token::GreaterThan => Ok(ComparisonOperator::GreaterThan),
            Token::GreaterEqual => Ok(ComparisonOperator::GreaterEqual),
            Token::EqualEqual => Ok(ComparisonOperator::Equal),
            Token::BangEqual => Ok(ComparisonOperator::NotEqual),
            token => Err(self.error(format!(
                "expected comparison operator in `{clause}`, got {token:?}"
            ))),
        }
    }

    fn parse_by_clause(&mut self) -> Result<Proof, ClickError> {
        self.expect_ident_spelling("by")?;
        let tactic = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let mut tactics = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                tactics.push(self.parse_tactic()?);
            }
            self.expect(Token::RBrace)?;
            if tactics.is_empty() {
                return Err(self.error("`by` block must contain at least one proof step or tactic"));
            }
            if tactics.len() != 1 {
                return Err(self.error("`by` blocks currently support exactly one tactic"));
            }
            tactics.remove(0)
        } else {
            self.parse_tactic()?
        };

        Ok(Proof::Tactic(tactic))
    }

    fn parse_ensure_expression(&mut self) -> Result<C0Expression, ClickError> {
        self.parse_ensure_add()
    }

    fn parse_contract_expression(&mut self) -> Result<ContractExpression, ClickError> {
        self.parse_contract_add()
    }

    fn parse_contract_segment(&mut self) -> Result<ContractSegment, ClickError> {
        if self.peek_ident() == Some("old") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let mut segment = self.parse_current_contract_segment()?;
            segment.state = ContractSegmentState::Old;
            self.expect(Token::RParen)?;
            return Ok(segment);
        }

        self.parse_current_contract_segment()
    }

    fn parse_current_contract_segment(&mut self) -> Result<ContractSegment, ClickError> {
        let base = self.parse_ensure_primary()?.to_megakernel_expression();
        self.expect(Token::LBracket)?;
        let start = self.parse_ensure_expression()?.to_megakernel_expression();
        self.expect(Token::DotDot)?;
        let end = self.parse_ensure_expression()?.to_megakernel_expression();
        self.expect(Token::RBracket)?;
        Ok(ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start,
            end,
        })
    }

    fn parse_contract_add(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_postfix()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_contract_postfix()?;
                    ContractExpression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_contract_postfix()?;
                    ContractExpression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_contract_postfix(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_primary()?;
        while self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let index = self.parse_contract_expression()?;
            self.expect(Token::RBracket)?;
            expression = ContractExpression::Index(Box::new(expression), Box::new(index));
        }
        Ok(expression)
    }

    fn parse_contract_primary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.peek_ident() == Some("old") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let expression = self.parse_ensure_expression()?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::Old(
                expression.to_megakernel_expression(),
            ));
        }

        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected contract expression, got `by`"))
            }
            Some(Token::Ident(name)) => {
                Ok(ContractExpression::Current(CExpression::Variable(name)))
            }
            Some(Token::Number(value)) => Ok(ContractExpression::Current(CExpression::Value(
                CValue::Int32(Bitvector32Term::Constant(value)),
            ))),
            Some(Token::LParen) => {
                let expression = self.parse_contract_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected contract expression, got {token:?}"))),
            None => Err(self.error("expected contract expression, got end of input")),
        }
    }

    fn parse_ensure_add(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_postfix()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_ensure_postfix()?;
                    C0Expression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_ensure_postfix()?;
                    C0Expression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_postfix(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_primary()?;
        while self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let index = self.parse_ensure_expression()?;
            self.expect(Token::RBracket)?;
            expression = C0Expression::Index(Box::new(expression), Box::new(index));
        }
        Ok(expression)
    }

    fn parse_ensure_primary(&mut self) -> Result<C0Expression, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected result expression, got `by`"))
            }
            Some(Token::Ident(name)) => Ok(C0Expression::Variable(name)),
            Some(Token::Number(value)) => Ok(C0Expression::Int32Literal(value)),
            Some(Token::LParen) => {
                let expression = self.parse_ensure_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected result expression, got {token:?}"))),
            None => Err(self.error("expected result expression, got end of input")),
        }
    }

    fn parse_tactic(&mut self) -> Result<Tactic, ClickError> {
        match self.peek_ident() {
            Some("auto") => {
                self.position += 1;
                self.expect(Token::Semicolon)?;
                Ok(Tactic::Auto)
            }
            Some(keyword) => Err(self.error(format!("expected tactic, got `{keyword}`"))),
            None => Err(self.error("expected tactic")),
        }
    }

    fn expect_ident(&mut self, expected: &str) -> Result<String, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => Err(self.error(format!("expected {expected}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected}, got end of input"))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == expected => Ok(()),
            Some(Token::Ident(name)) => {
                Err(self.error(format!("expected `{expected}`, got `{name}`")))
            }
            Some(token) => Err(self.error(format!("expected `{expected}`, got {token:?}"))),
            None => Err(self.error(format!("expected `{expected}`, got end of input"))),
        }
    }

    fn expect_number(&mut self, expected: &str) -> Result<u32, ClickError> {
        match self.next() {
            Some(Token::Number(value)) => Ok(value),
            Some(token) => Err(self.error(format!("expected {expected}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected}, got end of input"))),
        }
    }

    fn expect_index(&mut self, expected: &str) -> Result<usize, ClickError> {
        usize::try_from(self.expect_number(expected)?)
            .map_err(|_| self.error(format!("{expected} does not fit in usize")))
    }

    fn expect_string(&mut self, expected: &str) -> Result<String, ClickError> {
        match self.next() {
            Some(Token::String(value)) => Ok(value),
            Some(token) => Err(self.error(format!("expected {expected}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected}, got end of input"))),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), ClickError> {
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(self.error(format!("expected {expected:?}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected:?}, got end of input"))),
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned()?;
        self.position += 1;
        Some(token)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn peek_next(&self) -> Option<&Token> {
        self.tokens.get(self.position + 1)
    }

    fn peek_ident(&self) -> Option<&str> {
        match self.peek() {
            Some(Token::Ident(name)) => Some(name),
            _ => None,
        }
    }

    fn error(&self, message: impl Into<String>) -> ClickError {
        ClickError::new(format!("at token {}: {}", self.position, message.into()))
    }
}

fn tokenize(source: &str) -> Result<Vec<Token>, ClickError> {
    let chars: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut index = 0;

    while let Some(ch) = chars.get(index).copied() {
        match ch {
            ch if ch.is_whitespace() => {
                index += 1;
            }
            '{' => {
                tokens.push(Token::LBrace);
                index += 1;
            }
            '}' => {
                tokens.push(Token::RBrace);
                index += 1;
            }
            '(' => {
                tokens.push(Token::LParen);
                index += 1;
            }
            ')' => {
                tokens.push(Token::RParen);
                index += 1;
            }
            '[' => {
                tokens.push(Token::LBracket);
                index += 1;
            }
            ']' => {
                tokens.push(Token::RBracket);
                index += 1;
            }
            ':' => {
                tokens.push(Token::Colon);
                index += 1;
            }
            ',' => {
                tokens.push(Token::Comma);
                index += 1;
            }
            ';' => {
                tokens.push(Token::Semicolon);
                index += 1;
            }
            '.' => {
                if chars.get(index + 1) == Some(&'.') {
                    tokens.push(Token::DotDot);
                    index += 2;
                } else {
                    return Err(ClickError::new(format!(
                        "expected `..`, got `.` at byte offset {index}"
                    )));
                }
            }
            '+' => {
                tokens.push(Token::Plus);
                index += 1;
            }
            '-' => {
                tokens.push(Token::Minus);
                index += 1;
            }
            '*' => {
                tokens.push(Token::Star);
                index += 1;
            }
            '<' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::LessEqual);
                    index += 2;
                } else {
                    tokens.push(Token::LessThan);
                    index += 1;
                }
            }
            '>' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::GreaterEqual);
                    index += 2;
                } else {
                    tokens.push(Token::GreaterThan);
                    index += 1;
                }
            }
            '!' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::BangEqual);
                    index += 2;
                } else {
                    return Err(ClickError::new(format!(
                        "expected `!=`, got `!` at byte offset {index}"
                    )));
                }
            }
            '=' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::EqualEqual);
                    index += 2;
                } else {
                    return Err(ClickError::new(format!(
                        "expected `==`, got `=` at byte offset {index}"
                    )));
                }
            }
            '"' => {
                let (value, next_index) = tokenize_string(&chars, index)?;
                tokens.push(Token::String(value));
                index = next_index;
            }
            ch if ch.is_ascii_digit() => {
                let start = index;
                while chars.get(index).is_some_and(|next| next.is_ascii_digit()) {
                    index += 1;
                }
                let spelling: String = chars[start..index].iter().collect();
                let value = spelling.parse::<u32>().map_err(|_| {
                    ClickError::new(format!("number `{spelling}` does not fit in u32"))
                })?;
                tokens.push(Token::Number(value));
            }
            ch if is_ident_start(ch) => {
                let start = index;
                index += 1;
                while chars
                    .get(index)
                    .is_some_and(|next| is_ident_continue(*next))
                {
                    index += 1;
                }
                tokens.push(Token::Ident(chars[start..index].iter().collect()));
            }
            other => {
                return Err(ClickError::new(format!(
                    "unexpected character `{other}` at byte offset {index}"
                )));
            }
        }
    }

    Ok(tokens)
}

fn tokenize_string(chars: &[char], start: usize) -> Result<(String, usize), ClickError> {
    let mut value = String::new();
    let mut index = start + 1;
    while let Some(ch) = chars.get(index).copied() {
        match ch {
            '"' => return Ok((value, index + 1)),
            '\\' => {
                let Some(escaped) = chars.get(index + 1).copied() else {
                    return Err(ClickError::new("unterminated string literal"));
                };
                match escaped {
                    '"' | '\\' => value.push(escaped),
                    'n' => value.push('\n'),
                    't' => value.push('\t'),
                    other => {
                        return Err(ClickError::new(format!(
                            "unsupported escape `\\{other}` in string literal"
                        )));
                    }
                }
                index += 2;
            }
            other => {
                value.push(other);
                index += 1;
            }
        }
    }

    Err(ClickError::new("unterminated string literal"))
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::megakernel::int32;

    const FILL3_C: &str = r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                p[i] = i;
                i = i + 1;
            }
            return p[2];
        }
    "#;

    const FILL3_CLICK: &str = r#"
        verifying "fill3.c";

        int32 fill3(int32* p) {
            requires valid_range(p, 12);
            ensures returns_second: result == 2 by auto;
        }
    "#;

    fn current(expression: CExpression) -> ContractExpression {
        ContractExpression::Current(expression)
    }

    fn current_var(name: &str) -> ContractExpression {
        current(CExpression::Variable(name.to_string()))
    }

    fn current_int(value: u32) -> ContractExpression {
        current(CExpression::Value(int32(value)))
    }

    fn current_index(base: &str, index: u32) -> ContractExpression {
        ContractExpression::Index(Box::new(current_var(base)), Box::new(current_int(index)))
    }

    fn old_index(base: &str, index: u32) -> ContractExpression {
        ContractExpression::Old(CExpression::Index(
            Box::new(CExpression::Variable(base.to_string())),
            Box::new(CExpression::Value(int32(index))),
        ))
    }

    fn ensure_comparison(
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
    ) -> Ensure {
        Ensure::Proposition(ClickProposition::Comparison {
            left,
            operator,
            right,
        })
    }

    #[test]
    fn parses_checked_signature_and_contract_clauses() {
        let file = parse(FILL3_CLICK).expect("sidecar should parse");

        assert_eq!(file.verifying_sources(), &["fill3.c".to_string()]);
        assert_eq!(file.function_blocks().len(), 1);
        let function = &file.function_blocks()[0];
        assert_eq!(function.signature().return_type(), C0Type::Int32);
        assert_eq!(function.signature().name(), "fill3");
        assert_eq!(
            function.signature().parameters(),
            &[FunctionParameter {
                c_type: C0Type::Int32Pointer,
                name: "p".to_string()
            }]
        );
        assert_eq!(
            function.requires(),
            &[Requirement::ValidRange {
                name: "p".to_string(),
                bytes: RangeBytes::Constant(12)
            }]
        );
        assert_eq!(function.ensures().len(), 1);
        let ensure = &function.ensures()[0];
        assert_eq!(ensure.name(), Some("returns_second"));
        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_var("result"),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
        assert!(ensure.proof().is_auto_tactic());
    }

    #[test]
    fn parses_symbolic_valid_range_bytes() {
        let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires valid_range(p, n * 4);
                ensures result == n by auto;
            }
        "#;
        let file = parse(source).expect("symbolic valid_range should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.requires(),
            &[Requirement::ValidRange {
                name: "p".to_string(),
                bytes: RangeBytes::Multiply(
                    Box::new(RangeBytes::Parameter("n".to_string())),
                    Box::new(RangeBytes::Constant(4)),
                )
            }]
        );
    }

    #[test]
    fn parses_valid_range_segment_syntax() {
        let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires valid_range(p[0..n]);
                ensures result == n by auto;
            }
        "#;
        let file = parse(source).expect("segment valid_range should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.requires(),
            &[Requirement::ValidRangeSegment {
                name: "p".to_string(),
                start: RangeBytes::Constant(0),
                end: RangeBytes::Parameter("n".to_string()),
            }]
        );
    }

    #[test]
    fn rejects_reversed_constant_valid_range_segment() {
        let c_source = r#"
            int32 read_second(int32* p) {
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "read_second.c";

            int32 read_second(int32* p) {
                requires valid_range(p[3..1]);
                ensures reads: result == p[1] by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("read_second.c", c_source)])
            .expect_err("reversed concrete segment should fail");

        assert!(
            error
                .message()
                .contains("`valid_range(p[3..1])` has an end before its start"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn parses_array_parameter_signature_as_pointer() {
        let source = FILL3_CLICK.replace("int32* p", "int32 p[3]");
        let file = parse(&source).expect("array parameter signature should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.signature().parameters(),
            &[FunctionParameter {
                c_type: C0Type::Int32Pointer,
                name: "p".to_string(),
            }]
        );
    }

    #[test]
    fn parses_block_by_clause() {
        let source = FILL3_CLICK.replace("by auto;", "by { auto; }");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(ensure.proof().is_auto_tactic());
    }

    #[test]
    fn parses_unnamed_ensure_clause() {
        let source =
            FILL3_CLICK.replace("ensures returns_second: result == 2", "ensures result == 2");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(ensure.name(), None);
        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_var("result"),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
    }

    #[test]
    fn parses_memory_postcondition() {
        let source = FILL3_CLICK.replace("result == 2", "p[2] == 2");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_index("p", 2),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
    }

    #[test]
    fn parses_old_memory_postcondition() {
        let source = FILL3_CLICK.replace("result == 2", "p[0] == old(p[0])");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_index("p", 0),
                ComparisonOperator::Equal,
                old_index("p", 0),
            )
        );
    }

    #[test]
    fn parses_loop_invariants_and_statement_asserts() {
        let source = r#"
            verifying "count.c";

            int32 count() {
                statement 2 {
                    assert i == 0 by auto;
                }

                loop 0 {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;
        let file = parse(source).expect("sidecar should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(function.structural_clauses().len(), 2);
        assert_eq!(
            function.structural_clauses()[0].target(),
            &StructuralTarget::Statement(2)
        );
        assert_eq!(
            function.structural_clauses()[0].items()[0].kind(),
            StructuralItemKind::Assert
        );
        assert_eq!(
            function.structural_clauses()[1].target(),
            &StructuralTarget::Loop(0)
        );
        assert_eq!(function.structural_clauses()[1].items().len(), 2);
        assert_eq!(
            function.structural_clauses()[1].items()[0].kind(),
            StructuralItemKind::Invariant
        );
    }

    #[test]
    fn parses_click_proposition_syntax() {
        let source = r#"
            verifying "logic.c";

            int32 logic(int32 x) {
                requires x >= 0 and x < 10;
                ensures bounded: result >= 0 and result < 10 by auto;
                ensures implication: result == x implies result >= 0 by auto;
                ensures quantified: forall (int32 k) {
                    0 <= k implies k >= 0
                } by auto;
                ensures segment: preserves(p[0..n]) by auto;
                ensures writes: writes_only(p[0..n]) by auto;
            }
        "#;
        let file = parse(source).expect("proposition syntax should parse");
        let function = &file.function_blocks()[0];

        assert!(matches!(
            function.requires()[0],
            Requirement::Proposition(ClickProposition::And(_, _))
        ));
        assert!(matches!(
            function.ensures()[0].ensure(),
            Ensure::Proposition(ClickProposition::And(_, _))
        ));
        assert!(matches!(
            function.ensures()[1].ensure(),
            Ensure::Proposition(ClickProposition::Implies(_, _))
        ));
        assert!(matches!(
            function.ensures()[2].ensure(),
            Ensure::Proposition(ClickProposition::ForAll { .. })
        ));
        assert!(matches!(
            function.ensures()[3].ensure(),
            Ensure::Proposition(ClickProposition::Preserves(_))
        ));
        assert!(matches!(
            function.ensures()[4].ensure(),
            Ensure::Proposition(ClickProposition::WritesOnly(_))
        ));
    }

    #[test]
    fn verifies_click_proposition_logic() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures prop_logic: result == x and not (result != x) by auto;
                ensures prop_implies: result == x implies result == x by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect("proposition logic should verify");

        assert_eq!(verified.len(), 2);
    }

    #[test]
    fn verifies_symbolic_result_expression() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_argument: result == x by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect("identity sidecar should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(
            verified[0].ensure_clause.ensure(),
            &ensure_comparison(
                current_var("result"),
                ComparisonOperator::Equal,
                current_var("x"),
            )
        );
    }

    #[test]
    fn verifies_memory_postcondition() {
        let source = FILL3_CLICK.replace(
            "ensures returns_second: result == 2",
            "ensures third: p[2] == 2",
        );
        let verified = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect("fill3 memory postcondition should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(
            verified[0].ensure_clause.ensure(),
            &ensure_comparison(
                current_index("p", 2),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
    }

    #[test]
    fn verifies_old_memory_postcondition_for_unmodified_cell() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                ensures writes_second: p[1] == 9 by auto;
                ensures preserves_first: p[0] == old(p[0]) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("old memory postcondition should verify");

        assert_eq!(verified.len(), 2);
        assert_eq!(
            verified[1].ensure_clause.ensure(),
            &ensure_comparison(
                current_index("p", 0),
                ComparisonOperator::Equal,
                old_index("p", 0),
            )
        );
    }

    #[test]
    fn verifies_preserves_segment_postcondition() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                ensures preserves_first_cell: preserves(p[0..1]) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("unwritten segment should be preserved");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn preserves_segment_rejects_overwritten_cell() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                ensures preserves_second_cell: preserves(p[1..2]) by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("overwritten segment should not be preserved");

        assert!(
            error.message().contains("proposition was not provable"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_writes_only_segment_postcondition() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                ensures writes_second_cell: writes_only(p[1..2]) by auto;
                ensures writes_within_two_cells: writes_only(p[0..2]) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("write should stay inside declared segments");

        assert_eq!(verified.len(), 2);
    }

    #[test]
    fn writes_only_segment_rejects_write_outside_segment() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                ensures writes_first_cell_only: writes_only(p[0..1]) by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("write outside segment should fail");

        assert!(
            error.message().contains("is outside the segment"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn old_memory_postcondition_fails_for_overwritten_cell() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                ensures preserves_second: p[1] == old(p[1]) by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("old memory postcondition for overwritten cell should fail");

        assert!(
            error
                .message()
                .contains("left side evaluated to Int32(Constant(9))"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_loop_invariants_and_statement_assert() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                statement 2 {
                    assert i == 0 by auto;
                }

                loop 0 {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect("loop invariants and statement assert should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), AutoProofKind::LoopVerification);
    }

    #[test]
    fn verifies_old_memory_loop_invariant() {
        let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
                int32 i;
                i = 1;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1 and n <= 2147483647;
                requires valid_range(p, n * 4);
                loop 0 {
                    invariant i >= 1 and i <= n by auto;
                    invariant p[0] == old(p[0]) by auto;
                }
                ensures frame_and_result: p[0] == old(p[0]) and result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
            .expect("old memory loop invariant should verify");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn verifies_preserves_segment_loop_invariant() {
        let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
                int32 i;
                i = 1;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1 and n <= 2147483647;
                requires valid_range(p[0..n]);
                loop 0 {
                    invariant i >= 1 and i <= n by auto;
                    invariant preserves(p[0..1]) by auto;
                }
                ensures frame_and_result: preserves(p[0..1]) and result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
            .expect("preserves segment loop invariant should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), AutoProofKind::LoopVerification);
    }

    #[test]
    fn verifies_symbolic_segment_valid_range() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                loop 0 {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("segment valid_range should verify symbolic pointer loop");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), AutoProofKind::LoopVerification);
    }

    #[test]
    fn verifies_symbolic_loop_writes_only_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                loop 0 {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                }
                ensures writes_segment: writes_only(p[0..n]) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("symbolic pointer loop writes should stay inside segment");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), AutoProofKind::LoopVerification);
    }

    #[test]
    fn false_loop_invariant_fails() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                loop 0 {
                    invariant i < 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("false loop invariant should fail");

        assert!(
            error.message().contains("loop 0 invariant 0 preservation"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn false_loop_invariant_initialization_fails() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                loop 0 {
                    invariant i == 1 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("false loop invariant initialization should fail");

        assert!(
            error.message().contains("loop 0 invariant 0 entry"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_symbolic_increment_with_numeric_requirement() {
        let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
        let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures increments: result == x + 1 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("increment.c", c_source)])
            .expect("increment sidecar should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].specification.requires().len(), 1);
    }

    #[test]
    fn symbolic_increment_without_numeric_requirement_fails() {
        let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
        let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                ensures increments: result == x + 1 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
            .expect_err("increment without overflow requirement should fail");

        assert!(
            error
                .message()
                .contains("failed for `increment.increments` path"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_fill3_c0_source_with_sidecar_specification() {
        let verified = verify_c0_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
            .expect("fill3 sidecar should verify");

        assert_eq!(verified.len(), 1);
        let verified = &verified[0];
        let base = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let second = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let third = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let local_i = Pointer {
            block: "local:i".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let initial_memory = memory_with_symbolic_valid_range_cells(
            CMemory::new().with_block("p", 12),
            &std::collections::BTreeMap::from([("p", 12)]),
        );
        let final_memory = initial_memory
            .clone()
            .with_block("local:i", 4)
            .store(first, int32(0))
            .store(second, int32(1))
            .store(third, int32(2))
            .store(local_i, int32(3));

        assert_eq!(
            verified.specification.state(),
            &CState::new().with_memory(initial_memory)
        );
        assert_eq!(verified.specification.arguments(), &[c_pointer_value(base)]);
        assert_eq!(
            verified.specification.outcome(),
            &CFunctionOutcome::Return {
                value: int32(2),
                state: CState::new().with_memory(final_memory),
            }
        );
        assert_eq!(
            implication_body(verified.theorem.proposition()),
            &Proposition::CFunctionSatisfiesSpecification {
                function: syntax::parse_function(FILL3_C)
                    .expect("fill3 should parse")
                    .to_megakernel_function(),
                specification: verified.specification.clone(),
            }
        );
    }

    #[test]
    fn signature_mismatch_reports_direct_error() {
        let source = FILL3_CLICK.replace("int32* p", "int32 q");
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong signature should fail");

        assert!(
            error.message().contains("signature mismatch"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn failed_ensure_reports_actual_return() {
        let source = FILL3_CLICK.replace("result == 2", "result == 3");
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong result should fail");

        assert!(
            error
                .message()
                .contains("left side evaluated to Int32(Constant(2))"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn failed_memory_postcondition_reports_loaded_value() {
        let source = FILL3_CLICK.replace(
            "ensures returns_second: result == 2",
            "ensures third: p[2] == 3",
        );
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong memory postcondition should fail");

        assert!(
            error
                .message()
                .contains("left side evaluated to Int32(Constant(2))"),
            "{}",
            error.message()
        );
    }
}
