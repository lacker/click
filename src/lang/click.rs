//! Tiny `.click` sidecar verifier for the C0 megakernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::BTreeMap;
use std::fmt;

use crate::lang::c::syntax::{self, C0Expression, C0Type};
use crate::megakernel::{
    Assumptions, Bitvector32Term, CExpression, CFunction, CFunctionEnvironment, CFunctionOutcome,
    CFunctionSpecification, CMemory, CState, CStatement, CValue, ConditionTerm, Pointer,
    PointerOffsetTerm, Proposition, Theorem, Variable, c_assert, c_function,
    c_function_specification, c_pointer_value, c_seq,
    prove_c_function_satisfies_specification_with_environment,
    prove_symbolic_c_function_execution_paths_with_environment,
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
    at_clauses: Vec<AtClause>,
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
    ValidRange { name: String, bytes: u32 },
    Condition(CExpression),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnsureClause {
    name: Option<String>,
    ensure: Ensure,
    proof: Proof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AtClause {
    target: AtTarget,
    items: Vec<AtItem>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum AtTarget {
    Loop(usize),
    Statement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AtItem {
    kind: AtItemKind,
    condition: CExpression,
    proof: Proof,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AtItemKind {
    Invariant,
    Assert,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ensure {
    Comparison {
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
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

/// A `.click` `by` clause: a sequence of tactic calls proving a theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proof {
    tactics: Vec<Tactic>,
}

/// A `.click` proof-language command.
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
    pub specification: CFunctionSpecification,
    pub theorem: Theorem,
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

    pub fn at_clauses(&self) -> &[AtClause] {
        &self.at_clauses
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

impl AtClause {
    pub fn target(&self) -> &AtTarget {
        &self.target
    }

    pub fn items(&self) -> &[AtItem] {
        &self.items
    }
}

impl AtItem {
    pub fn kind(&self) -> AtItemKind {
        self.kind
    }

    pub fn condition(&self) -> &CExpression {
        &self.condition
    }

    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl Proof {
    pub fn tactics(&self) -> &[Tactic] {
        &self.tactics
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
        validate_at_clauses(&function_block, parsed_function)?;
        let function = annotated_function(&function_block, parsed_function)?;

        for (ensure_index, ensure_clause) in function_block.ensures.iter().enumerate() {
            let ensure_label =
                ensure_label(function_block.signature.name(), ensure_clause, ensure_index);
            if ensure_clause.proof.tactics() != [Tactic::Auto] {
                return Err(ClickError::new(format!(
                    "`{ensure_label}` must use exactly `by auto;` in this first slice"
                )));
            }

            let (state, arguments, requirement_propositions) = initial_call(
                function_block.signature.name(),
                function_block.requires(),
                parsed_function.parameters(),
            )?;
            let assumptions = assumptions_from_propositions(&requirement_propositions);
            let execution = prove_symbolic_c_function_execution_paths_with_environment(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions,
                function_environment.clone(),
            );
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

            for (path_index, path) in execution.paths().iter().enumerate() {
                if !path.obligations().is_empty() {
                    return Err(ClickError::new(format!(
                        "`auto` left proof obligations on path {} for `{ensure_label}`: {:?}",
                        path_index,
                        path.obligations()
                    )));
                }
                let outcome = match implication_body(path.theorem().proposition()) {
                    Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
                    proposition => {
                        return Err(ClickError::new(format!(
                            "`auto` produced an unexpected theorem on path {path_index} for `{ensure_label}`: {proposition:?}"
                        )));
                    }
                };

                check_ensure(
                    &ensure_label,
                    path_index,
                    path.facts(),
                    ensure_clause,
                    parsed_function.parameters(),
                    &arguments,
                    &state,
                    &outcome,
                )?;
                let mut path_requirements = requirement_propositions.clone();
                path_requirements
                    .extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                let specification = c_function_specification(
                    state.clone(),
                    arguments.clone(),
                    path_requirements,
                    outcome.clone(),
                );
                let theorem = prove_c_function_satisfies_specification_with_environment(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    function_environment.clone(),
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`auto` execution for `{ensure_label}` path {path_index} did not satisfy the packaged specification"
                    ))
                })?;

                verified.push(VerifiedCTheorem {
                    source_path: source_path.clone(),
                    function_block: function_block.clone(),
                    ensure_index,
                    ensure_clause: ensure_clause.clone(),
                    specification,
                    theorem,
                });
            }
        }
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

fn validate_at_clauses(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    let statement_count = count_statements(parsed_function.body());
    for at_clause in function_block.at_clauses() {
        match at_clause.target() {
            AtTarget::Loop(index) if *index >= loop_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `loop {index}` target; it contains {loop_count} loop(s)",
                    function_block.signature().name()
                )));
            }
            AtTarget::Statement(index) if *index >= statement_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `statement {index}` target; it contains {statement_count} statement(s)",
                    function_block.signature().name()
                )));
            }
            AtTarget::Statement(_) => {
                for item in at_clause.items() {
                    if item.kind() == AtItemKind::Invariant {
                        return Err(ClickError::new(
                            "`invariant` is only supported at `loop` targets",
                        ));
                    }
                }
            }
            AtTarget::Loop(_) => {}
        }

        for item in at_clause.items() {
            if item.proof().tactics() != [Tactic::Auto] {
                return Err(ClickError::new(
                    "`at` clauses must use exactly `by auto;` in this first slice",
                ));
            }
        }
    }
    Ok(())
}

fn annotated_function(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
) -> Result<CFunction, ClickError> {
    let mut lowerer = AnnotationLowerer {
        at_clauses: function_block.at_clauses(),
        loop_index: 0,
        statement_index: 0,
    };
    let body = lowerer.lower_statement(parsed_function.body());
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
    at_clauses: &'a [AtClause],
    loop_index: usize,
    statement_index: usize,
}

impl AnnotationLowerer<'_> {
    fn lower_statement(&mut self, statement: &syntax::C0Statement) -> CStatement {
        match statement {
            syntax::C0Statement::Seq(first, second) => {
                c_seq(self.lower_statement(first), self.lower_statement(second))
            }
            syntax::C0Statement::While { condition, body } => {
                let statement_index = self.next_statement_index();
                let loop_index = self.next_loop_index();
                let lowered_body = self.lower_statement(body);
                let loop_checks = self.loop_checks(loop_index);
                let checked_body = append_asserts(lowered_body, &loop_checks);
                let lowered_loop = crate::megakernel::c_while(
                    condition.to_megakernel_expression(),
                    Vec::new(),
                    checked_body,
                );
                let lowered_loop = prepend_asserts(lowered_loop, &loop_checks);
                self.prepend_statement_asserts(statement_index, lowered_loop)
            }
            statement => {
                let statement_index = self.next_statement_index();
                let lowered = statement.to_megakernel_statement();
                self.prepend_statement_asserts(statement_index, lowered)
            }
        }
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
            .at_clauses
            .iter()
            .filter(|clause| clause.target() == &AtTarget::Statement(statement_index))
            .flat_map(AtClause::items)
            .map(AtItem::condition)
            .cloned()
            .collect::<Vec<_>>();
        prepend_asserts(statement, &checks)
    }

    fn loop_checks(&self, loop_index: usize) -> Vec<CExpression> {
        self.at_clauses
            .iter()
            .filter(|clause| clause.target() == &AtTarget::Loop(loop_index))
            .flat_map(AtClause::items)
            .map(AtItem::condition)
            .cloned()
            .collect()
    }
}

fn prepend_asserts(statement: CStatement, conditions: &[CExpression]) -> CStatement {
    conditions
        .iter()
        .rev()
        .fold(statement, |statement, condition| {
            c_seq(c_assert(condition.clone()), statement)
        })
}

fn append_asserts(statement: CStatement, conditions: &[CExpression]) -> CStatement {
    conditions.iter().fold(statement, |statement, condition| {
        c_seq(statement, c_assert(condition.clone()))
    })
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
    let valid_ranges: BTreeMap<&str, u32> = requires
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::ValidRange { name, bytes } => Some((name.as_str(), *bytes)),
            Requirement::Condition(_) => None,
        })
        .collect();
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

    for name in valid_ranges.keys() {
        if !parameters.iter().any(|parameter| parameter.name() == *name) {
            return Err(ClickError::new(format!(
                "`valid_range` names `{name}`, but `{}` has no such parameter",
                function_name
            )));
        }
    }

    memory = memory_with_symbolic_valid_range_cells(memory, &valid_ranges);
    let requirement_propositions = requirement_propositions(requires, parameters, &arguments)?;
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
) -> Result<Vec<Proposition>, ClickError> {
    requires
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::ValidRange { .. } => None,
            Requirement::Condition(condition) => {
                Some(condition_requirement_prop(parameters, arguments, condition))
            }
        })
        .collect()
}

fn condition_requirement_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    condition: &CExpression,
) -> Result<Proposition, ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;
    let (condition, value) = lower_condition_requirement(condition, &parameter_values)?;
    Ok(Proposition::ConditionIs(condition, value))
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

fn lower_condition_requirement(
    condition: &CExpression,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<(ConditionTerm, bool), ClickError> {
    match condition {
        CExpression::LessThan(left, right) => Ok((
            signed_less_than(
                lower_bitvector32_expression(left, parameter_values)?,
                lower_bitvector32_expression(right, parameter_values)?,
            ),
            true,
        )),
        CExpression::LessEqual(left, right) => Ok((
            signed_less_equal(
                lower_bitvector32_expression(left, parameter_values)?,
                lower_bitvector32_expression(right, parameter_values)?,
            ),
            true,
        )),
        CExpression::GreaterThan(left, right) => Ok((
            signed_greater_than(
                lower_bitvector32_expression(left, parameter_values)?,
                lower_bitvector32_expression(right, parameter_values)?,
            ),
            true,
        )),
        CExpression::GreaterEqual(left, right) => Ok((
            signed_greater_equal(
                lower_bitvector32_expression(left, parameter_values)?,
                lower_bitvector32_expression(right, parameter_values)?,
            ),
            true,
        )),
        CExpression::Equal(left, right) => Ok((
            bitvector32_equal(
                lower_bitvector32_expression(left, parameter_values)?,
                lower_bitvector32_expression(right, parameter_values)?,
            ),
            true,
        )),
        CExpression::NotEqual(left, right) => Ok((
            bitvector32_equal(
                lower_bitvector32_expression(left, parameter_values)?,
                lower_bitvector32_expression(right, parameter_values)?,
            ),
            false,
        )),
        _ => Err(ClickError::new(format!(
            "unsupported `requires` condition `{condition:?}`"
        ))),
    }
}

fn lower_bitvector32_expression(
    expression: &CExpression,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<Bitvector32Term, ClickError> {
    match expression {
        CExpression::Value(CValue::Int32(bits)) => Ok(bits.clone()),
        CExpression::Value(_) => Err(ClickError::new(format!(
            "expected int32 expression in contract, got `{expression:?}`"
        ))),
        CExpression::Variable(name) => match parameter_values.get(name) {
            Some(CValue::Int32(bits)) => Ok(bits.clone()),
            Some(_) => Err(ClickError::new(format!(
                "parameter `{name}` is not an int32 parameter"
            ))),
            None => Err(ClickError::new(format!(
                "contract expression references unknown parameter `{name}`"
            ))),
        },
        CExpression::Add(left, right) => Ok(bitvector32_add(
            lower_bitvector32_expression(left, parameter_values)?,
            lower_bitvector32_expression(right, parameter_values)?,
        )),
        CExpression::Subtract(left, right) => Ok(bitvector32_subtract(
            lower_bitvector32_expression(left, parameter_values)?,
            lower_bitvector32_expression(right, parameter_values)?,
        )),
        _ => Err(ClickError::new(format!(
            "unsupported int32 expression in contract: `{expression:?}`"
        ))),
    }
}

fn bitvector32_add(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_add(*right))
        }
        _ => Bitvector32Term::Add(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_subtract(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
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
    ensure_clause: &EnsureClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    match ensure_clause.ensure() {
        Ensure::Comparison {
            left,
            operator,
            right,
        } => match outcome {
            CFunctionOutcome::Return { value, state } => {
                let left_value =
                    evaluate_contract_expression(parameters, arguments, pre_state, state, value, left).map_err(
                        |message| {
                            ClickError::new(format!(
                                "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: could not evaluate left side: {message}"
                            ))
                        },
                    )?;
                let right_value =
                    evaluate_contract_expression(parameters, arguments, pre_state, state, value, right).map_err(
                        |message| {
                            ClickError::new(format!(
                                "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: could not evaluate right side: {message}"
                            ))
                        },
                    )?;
                prove_value_comparison(&left_value, *operator, &right_value, path_facts)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: left side evaluated to {left_value:?}, right side evaluated to {right_value:?}"
                        ))
                    })?;
            }
            other => {
                return Err(ClickError::new(format!(
                    "`ensures {left:?} {operator} {right:?}` failed for `{ensure_label}` path {path_index}: outcome was {other:?}"
                )));
            }
        },
    }

    Ok(())
}

fn prove_value_comparison(
    actual: &CValue,
    operator: ComparisonOperator,
    expected: &CValue,
    path_facts: &[crate::megakernel::PathFact],
) -> Option<()> {
    let CValue::Int32(actual) = actual else {
        return None;
    };
    let CValue::Int32(expected) = expected else {
        return None;
    };
    let (condition, value) = comparison_condition(actual.clone(), operator, expected.clone())?;
    let assumptions = path_facts
        .iter()
        .fold(Assumptions::new(), |assumptions, fact| {
            assumptions.assume_proposition(fact.proposition().clone())
        });
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
    expression: &ContractExpression,
) -> Result<CValue, String> {
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    evaluate_contract_expression_with_environment(
        &parameter_values,
        pre_state,
        post_state,
        result,
        expression,
    )
}

fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    expression: &ContractExpression,
) -> Result<CValue, String> {
    match expression {
        ContractExpression::Current(expression) => {
            evaluate_c_contract_expression(parameter_values, post_state, Some(result), expression)
        }
        ContractExpression::Old(expression) => {
            evaluate_c_contract_expression(parameter_values, pre_state, None, expression)
        }
        ContractExpression::Add(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                left,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
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
                left,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
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
                base,
            )?;
            let index = evaluate_contract_expression_with_environment(
                parameter_values,
                pre_state,
                post_state,
                result,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            match post_state.memory().load(&pointer) {
                crate::megakernel::CExpressionOutcome::Value(value) => Ok(value),
                outcome => Err(format!("load from {pointer:?} produced {outcome:?}")),
            }
        }
    }
}

fn evaluate_c_contract_expression(
    parameter_values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
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
            let left = evaluate_c_contract_expression(parameter_values, state, result, left)?;
            let right = evaluate_c_contract_expression(parameter_values, state, result, right)?;
            evaluate_postcondition_add(left, right)
        }
        CExpression::Subtract(left, right) => {
            let left = evaluate_c_contract_expression(parameter_values, state, result, left)?;
            let right = evaluate_c_contract_expression(parameter_values, state, result, right)?;
            evaluate_postcondition_sub(left, right)
        }
        CExpression::Index(base, index) => {
            let base = evaluate_c_contract_expression(parameter_values, state, result, base)?;
            let index = evaluate_c_contract_expression(parameter_values, state, result, index)?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            match state.memory().load(&pointer) {
                crate::megakernel::CExpressionOutcome::Value(value) => Ok(value),
                outcome => Err(format!("load from {pointer:?} produced {outcome:?}")),
            }
        }
        _ => Err(format!(
            "unsupported postcondition expression `{expression:?}`"
        )),
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
        let mut at_clauses = Vec::new();
        let mut ensures = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("requires") => requires.push(self.parse_requirement()?),
                Some("at") => at_clauses.push(self.parse_at_clause()?),
                Some("ensures") => ensures.push(self.parse_ensure_clause()?),
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `requires`, `at`, `ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `requires`, `at`, `ensures`, or `}}` in `{}`",
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
            at_clauses,
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

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        if self.peek_ident() != Some("valid_range") || self.peek_next() != Some(&Token::LParen) {
            let condition = self.parse_requirement_condition()?;
            self.expect(Token::Semicolon)?;
            return Ok(Requirement::Condition(condition.to_megakernel_expression()));
        }

        self.expect_ident_spelling("valid_range")?;
        self.expect(Token::LParen)?;
        let name = self.expect_ident("range base name")?;
        self.expect(Token::Comma)?;
        let bytes = self.expect_number("range byte size")?;
        self.expect(Token::RParen)?;
        self.expect(Token::Semicolon)?;

        Ok(Requirement::ValidRange { name, bytes })
    }

    fn parse_requirement_condition(&mut self) -> Result<C0Expression, ClickError> {
        let left = self.parse_ensure_expression()?;
        let operator = self.parse_comparison_operator("requires")?;
        let right = self.parse_ensure_expression()?;

        match operator {
            ComparisonOperator::LessThan => {
                Ok(C0Expression::LessThan(Box::new(left), Box::new(right)))
            }
            ComparisonOperator::LessEqual => {
                Ok(C0Expression::LessEqual(Box::new(left), Box::new(right)))
            }
            ComparisonOperator::GreaterThan => {
                Ok(C0Expression::GreaterThan(Box::new(left), Box::new(right)))
            }
            ComparisonOperator::GreaterEqual => {
                Ok(C0Expression::GreaterEqual(Box::new(left), Box::new(right)))
            }
            ComparisonOperator::Equal => Ok(C0Expression::Equal(Box::new(left), Box::new(right))),
            ComparisonOperator::NotEqual => {
                Ok(C0Expression::NotEqual(Box::new(left), Box::new(right)))
            }
        }
    }

    fn parse_at_clause(&mut self) -> Result<AtClause, ClickError> {
        self.expect_ident_spelling("at")?;
        let target = self.parse_at_target()?;
        self.expect(Token::LBrace)?;
        let mut items = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            items.push(self.parse_at_item()?);
        }
        self.expect(Token::RBrace)?;
        if items.is_empty() {
            return Err(self.error("`at` block must contain at least one item"));
        }
        Ok(AtClause { target, items })
    }

    fn parse_at_target(&mut self) -> Result<AtTarget, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "loop" => {
                Ok(AtTarget::Loop(self.expect_index("loop index")?))
            }
            Some(Token::Ident(kind)) if kind == "statement" => {
                Ok(AtTarget::Statement(self.expect_index("statement index")?))
            }
            Some(Token::Ident(kind)) => {
                Err(self.error(format!("expected `loop` or `statement`, got `{kind}`")))
            }
            Some(token) => {
                Err(self.error(format!("expected `loop` or `statement`, got {token:?}")))
            }
            None => Err(self.error("expected `loop` or `statement`, got end of input")),
        }
    }

    fn parse_at_item(&mut self) -> Result<AtItem, ClickError> {
        let kind = match self.next() {
            Some(Token::Ident(kind)) if kind == "invariant" => AtItemKind::Invariant,
            Some(Token::Ident(kind)) if kind == "assert" => AtItemKind::Assert,
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
        let condition = self
            .parse_requirement_condition()?
            .to_megakernel_expression();
        let proof = self.parse_by_clause()?;
        Ok(AtItem {
            kind,
            condition,
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
        let left = self.parse_contract_expression()?;
        let operator = self.parse_comparison_operator("ensures")?;
        let right = self.parse_contract_expression()?;

        Ok(Ensure::Comparison {
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
        let tactics = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let mut tactics = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                tactics.push(self.parse_tactic()?);
            }
            self.expect(Token::RBrace)?;
            tactics
        } else {
            vec![self.parse_tactic()?]
        };

        if tactics.is_empty() {
            return Err(self.error("`by` block must contain at least one tactic"));
        }

        Ok(Proof { tactics })
    }

    fn parse_ensure_expression(&mut self) -> Result<C0Expression, ClickError> {
        self.parse_ensure_add()
    }

    fn parse_contract_expression(&mut self) -> Result<ContractExpression, ClickError> {
        self.parse_contract_add()
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
                bytes: 12
            }]
        );
        assert_eq!(function.ensures().len(), 1);
        let ensure = &function.ensures()[0];
        assert_eq!(ensure.name(), Some("returns_second"));
        assert_eq!(
            ensure.ensure(),
            &Ensure::Comparison {
                left: current_var("result"),
                operator: ComparisonOperator::Equal,
                right: current_int(2)
            }
        );
        assert_eq!(ensure.proof().tactics(), &[Tactic::Auto]);
    }

    #[test]
    fn parses_block_by_clause() {
        let source = FILL3_CLICK.replace("by auto;", "by { auto; }");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(ensure.proof().tactics(), &[Tactic::Auto]);
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
            &Ensure::Comparison {
                left: current_var("result"),
                operator: ComparisonOperator::Equal,
                right: current_int(2)
            }
        );
    }

    #[test]
    fn parses_memory_postcondition() {
        let source = FILL3_CLICK.replace("result == 2", "p[2] == 2");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.ensure(),
            &Ensure::Comparison {
                left: current_index("p", 2),
                operator: ComparisonOperator::Equal,
                right: current_int(2)
            }
        );
    }

    #[test]
    fn parses_old_memory_postcondition() {
        let source = FILL3_CLICK.replace("result == 2", "p[0] == old(p[0])");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.ensure(),
            &Ensure::Comparison {
                left: current_index("p", 0),
                operator: ComparisonOperator::Equal,
                right: old_index("p", 0)
            }
        );
    }

    #[test]
    fn parses_at_loop_invariants_and_statement_asserts() {
        let source = r#"
            verifying "count.c";

            int32 count() {
                at statement 2 {
                    assert i == 0 by auto;
                }

                at loop 0 {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;
        let file = parse(source).expect("sidecar should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(function.at_clauses().len(), 2);
        assert_eq!(function.at_clauses()[0].target(), &AtTarget::Statement(2));
        assert_eq!(
            function.at_clauses()[0].items()[0].kind(),
            AtItemKind::Assert
        );
        assert_eq!(function.at_clauses()[1].target(), &AtTarget::Loop(0));
        assert_eq!(function.at_clauses()[1].items().len(), 2);
        assert_eq!(
            function.at_clauses()[1].items()[0].kind(),
            AtItemKind::Invariant
        );
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
            &Ensure::Comparison {
                left: current_var("result"),
                operator: ComparisonOperator::Equal,
                right: current_var("x")
            }
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
            &Ensure::Comparison {
                left: current_index("p", 2),
                operator: ComparisonOperator::Equal,
                right: current_int(2)
            }
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
            &Ensure::Comparison {
                left: current_index("p", 0),
                operator: ComparisonOperator::Equal,
                right: old_index("p", 0)
            }
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
                at statement 2 {
                    assert i == 0 by auto;
                }

                at loop 0 {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect("loop invariants and statement assert should verify");

        assert_eq!(verified.len(), 1);
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
                at loop 0 {
                    invariant i < 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("false loop invariant should fail");

        assert!(
            error.message().contains("left proof obligations"),
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
            verified.theorem.proposition(),
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
