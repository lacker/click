//! Tiny `.click` sidecar verifier for the C0 megakernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::BTreeMap;

use crate::lang::c::syntax::{self, C0Expr, C0Type};
use crate::megakernel::{
    Assumptions, Bv32Term, CExpr, CFunctionEnv, CFunctionOutcome, CFunctionSpec, CMemory, CState,
    CValue, ConditionTerm, Prop, Ptr, PtrOffsetTerm, Theorem, Var, c_function_spec, c_ptr_value,
    prove_c_function_satisfies_spec_with_env, prove_symbolic_c_function_execution_with_env,
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
    ensures: Vec<EnsureClause>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSignature {
    return_type: C0Type,
    name: String,
    params: Vec<FunctionParam>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionParam {
    ty: C0Type,
    name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    ValidRange { name: String, bytes: u32 },
    Condition(CExpr),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnsureClause {
    name: Option<String>,
    ensure: Ensure,
    proof: Proof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ensure {
    ResultEq(CExpr),
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
    pub spec: CFunctionSpec,
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

    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }
}

impl FunctionParam {
    pub fn ty(&self) -> C0Type {
        self.ty
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
    let function_env = function_env(&parsed_sources);
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

        for (ensure_index, ensure_clause) in function_block.ensures.iter().enumerate() {
            let ensure_label =
                ensure_label(function_block.signature.name(), ensure_clause, ensure_index);
            if ensure_clause.proof.tactics() != [Tactic::Auto] {
                return Err(ClickError::new(format!(
                    "`{ensure_label}` must use exactly `by auto;` in this first slice"
                )));
            }

            let (state, args, requirement_props) = initial_call(
                function_block.signature.name(),
                function_block.requires(),
                parsed_function.params(),
            )?;
            let assumptions = assumptions_from_props(&requirement_props);
            let function = parsed_function.to_megakernel_function();
            let execution = prove_symbolic_c_function_execution_with_env(
                state.clone(),
                function.clone(),
                args.clone(),
                assumptions,
                function_env.clone(),
            )
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`auto` could not prove a single complete execution path for `{ensure_label}`"
                ))
            })?;
            let outcome = match implication_body(execution.prop()) {
                Prop::CFunctionExecutes { outcome, .. } => outcome.clone(),
                prop => {
                    return Err(ClickError::new(format!(
                        "`auto` produced an unexpected theorem for `{ensure_label}`: {prop:?}"
                    )));
                }
            };

            check_ensure(
                &ensure_label,
                ensure_clause,
                parsed_function.params(),
                &args,
                &outcome,
            )?;
            let spec = c_function_spec(state, args, requirement_props, outcome.clone());
            let theorem = prove_c_function_satisfies_spec_with_env(
                function,
                spec.clone(),
                Assumptions::new(),
                function_env.clone(),
            )
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`auto` execution for `{ensure_label}` did not satisfy the packaged spec"
                ))
            })?;

            verified.push(VerifiedCTheorem {
                source_path: source_path.clone(),
                function_block: function_block.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                spec,
                theorem,
            });
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

fn function_env(parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>) -> CFunctionEnv {
    parsed_sources
        .values()
        .fold(CFunctionEnv::new(), |env, (_, function)| {
            env.with_function(function.to_megakernel_function())
        })
}

fn ensure_label(function_name: &str, ensure: &EnsureClause, index: usize) -> String {
    match ensure.name() {
        Some(name) => format!("{function_name}.{name}"),
        None => format!("{function_name}.ensures_{index}"),
    }
}

fn implication_body(prop: &Prop) -> &Prop {
    match prop {
        Prop::Implies(_, body) => implication_body(body),
        _ => prop,
    }
}

fn assumptions_from_props(props: &[Prop]) -> Assumptions {
    props
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_prop)
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

    if signature.params().len() != parsed_function.params().len() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click has {} parameters, C has {}",
            signature.name(),
            signature.params().len(),
            parsed_function.params().len()
        )));
    }

    for (index, (expected, actual)) in signature
        .params()
        .iter()
        .zip(parsed_function.params())
        .enumerate()
    {
        if expected.ty() != actual.ty() || expected.name() != actual.name() {
            return Err(ClickError::new(format!(
                "signature mismatch for `{}` parameter {} in `{source_path}`: .click has {:?} {}, C has {:?} {}",
                signature.name(),
                index + 1,
                expected.ty(),
                expected.name(),
                actual.ty(),
                actual.name()
            )));
        }
    }

    Ok(())
}

fn initial_call(
    function_name: &str,
    requires: &[Requirement],
    params: &[syntax::C0Param],
) -> Result<(CState, Vec<CExpr>, Vec<Prop>), ClickError> {
    let valid_ranges: BTreeMap<&str, u32> = requires
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::ValidRange { name, bytes } => Some((name.as_str(), *bytes)),
            Requirement::Condition(_) => None,
        })
        .collect();
    let mut memory = CMemory::new();
    let mut args = Vec::new();

    for param in params {
        match param.ty() {
            C0Type::Int32Ptr => {
                if let Some(bytes) = valid_ranges.get(param.name()) {
                    memory = memory.with_block(param.name(), *bytes);
                }
                args.push(c_ptr_value(Ptr {
                    block: param.name().to_string(),
                    offset: PtrOffsetTerm::Const(0),
                }));
            }
            C0Type::Int32 => {
                args.push(CExpr::Value(CValue::Int32(Bv32Term::Var(Var(
                    args.len() as u64
                )))));
            }
        }
    }

    for name in valid_ranges.keys() {
        if !params.iter().any(|param| param.name() == *name) {
            return Err(ClickError::new(format!(
                "`valid_range` names `{name}`, but `{}` has no such parameter",
                function_name
            )));
        }
    }

    let requirement_props = requirement_props(requires, params, &args)?;
    Ok((CState::new().with_memory(memory), args, requirement_props))
}

fn requirement_props(
    requires: &[Requirement],
    params: &[syntax::C0Param],
    args: &[CExpr],
) -> Result<Vec<Prop>, ClickError> {
    requires
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::ValidRange { .. } => None,
            Requirement::Condition(condition) => {
                Some(condition_requirement_prop(params, args, condition))
            }
        })
        .collect()
}

fn condition_requirement_prop(
    params: &[syntax::C0Param],
    args: &[CExpr],
    condition: &CExpr,
) -> Result<Prop, ClickError> {
    let parameter_values = parameter_values(params, args)?;
    let (condition, value) = lower_condition_requirement(condition, &parameter_values)?;
    Ok(Prop::ConditionIs(condition, value))
}

fn parameter_values(
    params: &[syntax::C0Param],
    args: &[CExpr],
) -> Result<BTreeMap<String, CValue>, ClickError> {
    params
        .iter()
        .zip(args)
        .map(|(param, arg)| {
            let CExpr::Value(value) = arg else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    param.name()
                )));
            };
            Ok((param.name().to_string(), value.clone()))
        })
        .collect()
}

fn lower_condition_requirement(
    condition: &CExpr,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<(ConditionTerm, bool), ClickError> {
    match condition {
        CExpr::Lt(left, right) => Ok((
            signed_lt(
                lower_bv32_expr(left, parameter_values)?,
                lower_bv32_expr(right, parameter_values)?,
            ),
            true,
        )),
        CExpr::Le(left, right) => Ok((
            signed_le(
                lower_bv32_expr(left, parameter_values)?,
                lower_bv32_expr(right, parameter_values)?,
            ),
            true,
        )),
        CExpr::Gt(left, right) => Ok((
            signed_gt(
                lower_bv32_expr(left, parameter_values)?,
                lower_bv32_expr(right, parameter_values)?,
            ),
            true,
        )),
        CExpr::Ge(left, right) => Ok((
            signed_ge(
                lower_bv32_expr(left, parameter_values)?,
                lower_bv32_expr(right, parameter_values)?,
            ),
            true,
        )),
        CExpr::Eq(left, right) => Ok((
            bv32_eq(
                lower_bv32_expr(left, parameter_values)?,
                lower_bv32_expr(right, parameter_values)?,
            ),
            true,
        )),
        CExpr::Ne(left, right) => Ok((
            bv32_eq(
                lower_bv32_expr(left, parameter_values)?,
                lower_bv32_expr(right, parameter_values)?,
            ),
            false,
        )),
        _ => Err(ClickError::new(format!(
            "unsupported `requires` condition `{condition:?}`"
        ))),
    }
}

fn lower_bv32_expr(
    expr: &CExpr,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<Bv32Term, ClickError> {
    match expr {
        CExpr::Value(CValue::Int32(bits)) => Ok(bits.clone()),
        CExpr::Value(_) => Err(ClickError::new(format!(
            "expected int32 expression in contract, got `{expr:?}`"
        ))),
        CExpr::Var(name) => match parameter_values.get(name) {
            Some(CValue::Int32(bits)) => Ok(bits.clone()),
            Some(_) => Err(ClickError::new(format!(
                "parameter `{name}` is not an int32 parameter"
            ))),
            None => Err(ClickError::new(format!(
                "contract expression references unknown parameter `{name}`"
            ))),
        },
        CExpr::Add(left, right) => Ok(bv32_add(
            lower_bv32_expr(left, parameter_values)?,
            lower_bv32_expr(right, parameter_values)?,
        )),
        CExpr::Sub(left, right) => Ok(bv32_sub(
            lower_bv32_expr(left, parameter_values)?,
            lower_bv32_expr(right, parameter_values)?,
        )),
        _ => Err(ClickError::new(format!(
            "unsupported int32 expression in contract: `{expr:?}`"
        ))),
    }
}

fn bv32_add(left: Bv32Term, right: Bv32Term) -> Bv32Term {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => {
            Bv32Term::Const(left.wrapping_add(*right))
        }
        _ => Bv32Term::Add(Box::new(left), Box::new(right)),
    }
}

fn bv32_sub(left: Bv32Term, right: Bv32Term) -> Bv32Term {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => {
            Bv32Term::Const(left.wrapping_sub(*right))
        }
        _ => Bv32Term::Sub(Box::new(left), Box::new(right)),
    }
}

fn signed_lt(left: Bv32Term, right: Bv32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => {
            ConditionTerm::Const((*left as i32) < (*right as i32))
        }
        _ => ConditionTerm::Bv32Slt(Box::new(left), Box::new(right)),
    }
}

fn signed_le(left: Bv32Term, right: Bv32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => {
            ConditionTerm::Const((*left as i32) <= (*right as i32))
        }
        _ => ConditionTerm::Bv32Sle(Box::new(left), Box::new(right)),
    }
}

fn signed_gt(left: Bv32Term, right: Bv32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => {
            ConditionTerm::Const((*left as i32) > (*right as i32))
        }
        _ => ConditionTerm::Bv32Sgt(Box::new(left), Box::new(right)),
    }
}

fn signed_ge(left: Bv32Term, right: Bv32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => {
            ConditionTerm::Const((*left as i32) >= (*right as i32))
        }
        _ => ConditionTerm::Bv32Sge(Box::new(left), Box::new(right)),
    }
}

fn bv32_eq(left: Bv32Term, right: Bv32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bv32Term::Const(left), Bv32Term::Const(right)) => ConditionTerm::Const(left == right),
        _ => ConditionTerm::Bv32Eq(Box::new(left), Box::new(right)),
    }
}

fn check_ensure(
    ensure_label: &str,
    ensure_clause: &EnsureClause,
    params: &[syntax::C0Param],
    args: &[CExpr],
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    match ensure_clause.ensure() {
        Ensure::ResultEq(expected) => match outcome {
            CFunctionOutcome::Return { value, state } => {
                let expected = evaluate_expected_result_expr(params, args, state, expected)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`ensures result == {expected:?}` failed for `{ensure_label}`: could not evaluate expected expression"
                        ))
                    })?;
                if &expected != value {
                    return Err(ClickError::new(format!(
                        "`ensures result == {expected:?}` failed for `{ensure_label}`: returned {value:?}"
                    )));
                }
            }
            other => {
                return Err(ClickError::new(format!(
                    "`ensures result == {expected:?}` failed for `{ensure_label}`: outcome was {other:?}"
                )));
            }
        },
    }

    Ok(())
}

fn evaluate_expected_result_expr(
    params: &[syntax::C0Param],
    args: &[CExpr],
    _state: &CState,
    expected: &CExpr,
) -> Option<CValue> {
    let parameter_values = parameter_values(params, args).ok()?;
    Some(CValue::Int32(
        lower_bv32_expr(expected, &parameter_values).ok()?,
    ))
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
    Colon,
    Comma,
    Semicolon,
    EqEq,
    BangEq,
    Lt,
    Le,
    Gt,
    Ge,
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
        let mut ensures = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("requires") => requires.push(self.parse_requirement()?),
                Some("ensures") => ensures.push(self.parse_ensure_clause()?),
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `requires`, `ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `requires`, `ensures`, or `}}` in `{}`",
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
            ensures,
        })
    }

    fn parse_function_signature(&mut self) -> Result<FunctionSignature, ClickError> {
        let return_type = self.parse_type()?;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let params = self.parse_params()?;
        self.expect(Token::RParen)?;

        Ok(FunctionSignature {
            return_type,
            name,
            params,
        })
    }

    fn parse_params(&mut self) -> Result<Vec<FunctionParam>, ClickError> {
        let mut params = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(params);
        }

        loop {
            let ty = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            params.push(FunctionParam { ty, name });

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => return Ok(params),
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
            Ok(C0Type::Int32Ptr)
        } else {
            Ok(C0Type::Int32)
        }
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        if self.peek_ident() != Some("valid_range") || self.peek_next() != Some(&Token::LParen) {
            let condition = self.parse_requirement_condition()?;
            self.expect(Token::Semicolon)?;
            return Ok(Requirement::Condition(condition.to_megakernel_expr()));
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

    fn parse_requirement_condition(&mut self) -> Result<C0Expr, ClickError> {
        let left = self.parse_ensure_expr()?;
        let operator = self.next().ok_or_else(|| {
            self.error("expected comparison operator in `requires`, got end of input")
        })?;
        let right = self.parse_ensure_expr()?;

        match operator {
            Token::Lt => Ok(C0Expr::Lt(Box::new(left), Box::new(right))),
            Token::Le => Ok(C0Expr::Le(Box::new(left), Box::new(right))),
            Token::Gt => Ok(C0Expr::Gt(Box::new(left), Box::new(right))),
            Token::Ge => Ok(C0Expr::Ge(Box::new(left), Box::new(right))),
            Token::EqEq => Ok(C0Expr::Eq(Box::new(left), Box::new(right))),
            Token::BangEq => Ok(C0Expr::Ne(Box::new(left), Box::new(right))),
            token => Err(self.error(format!(
                "expected comparison operator in `requires`, got {token:?}"
            ))),
        }
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
        self.expect_ident_spelling("result")?;
        self.expect(Token::EqEq)?;
        let expected = self.parse_ensure_expr()?;

        Ok(Ensure::ResultEq(expected.to_megakernel_expr()))
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

    fn parse_ensure_expr(&mut self) -> Result<C0Expr, ClickError> {
        self.parse_ensure_add()
    }

    fn parse_ensure_add(&mut self) -> Result<C0Expr, ClickError> {
        let mut expr = self.parse_ensure_primary()?;
        loop {
            expr = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_ensure_primary()?;
                    C0Expr::Add(Box::new(expr), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_ensure_primary()?;
                    C0Expr::Sub(Box::new(expr), Box::new(right))
                }
                _ => return Ok(expr),
            };
        }
    }

    fn parse_ensure_primary(&mut self) -> Result<C0Expr, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected result expression, got `by`"))
            }
            Some(Token::Ident(name)) => Ok(C0Expr::Var(name)),
            Some(Token::Number(value)) => Ok(C0Expr::Int32Literal(value)),
            Some(Token::LParen) => {
                let expr = self.parse_ensure_expr()?;
                self.expect(Token::RParen)?;
                Ok(expr)
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
                    tokens.push(Token::Le);
                    index += 2;
                } else {
                    tokens.push(Token::Lt);
                    index += 1;
                }
            }
            '>' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::Ge);
                    index += 2;
                } else {
                    tokens.push(Token::Gt);
                    index += 1;
                }
            }
            '!' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::BangEq);
                    index += 2;
                } else {
                    return Err(ClickError::new(format!(
                        "expected `!=`, got `!` at byte offset {index}"
                    )));
                }
            }
            '=' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::EqEq);
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

    #[test]
    fn parses_checked_signature_and_contract_clauses() {
        let file = parse(FILL3_CLICK).expect("sidecar should parse");

        assert_eq!(file.verifying_sources(), &["fill3.c".to_string()]);
        assert_eq!(file.function_blocks().len(), 1);
        let function = &file.function_blocks()[0];
        assert_eq!(function.signature().return_type(), C0Type::Int32);
        assert_eq!(function.signature().name(), "fill3");
        assert_eq!(
            function.signature().params(),
            &[FunctionParam {
                ty: C0Type::Int32Ptr,
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
        assert_eq!(ensure.ensure(), &Ensure::ResultEq(CExpr::Value(int32(2))));
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
        assert_eq!(ensure.ensure(), &Ensure::ResultEq(CExpr::Value(int32(2))));
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
            &Ensure::ResultEq(CExpr::Var("x".to_string()))
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
        assert_eq!(verified[0].spec.requires().len(), 1);
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
                .contains("could not prove a single complete execution path"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_fill3_c0_source_with_sidecar_spec() {
        let verified = verify_c0_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
            .expect("fill3 sidecar should verify");

        assert_eq!(verified.len(), 1);
        let verified = &verified[0];
        let base = Ptr {
            block: "p".to_string(),
            offset: PtrOffsetTerm::Const(0),
        };
        let first = Ptr {
            block: "p".to_string(),
            offset: PtrOffsetTerm::Const(0),
        };
        let second = Ptr {
            block: "p".to_string(),
            offset: PtrOffsetTerm::Const(4),
        };
        let third = Ptr {
            block: "p".to_string(),
            offset: PtrOffsetTerm::Const(8),
        };
        let local_i = Ptr {
            block: "local:i".to_string(),
            offset: PtrOffsetTerm::Const(0),
        };
        let final_memory = CMemory::new()
            .with_block("p", 12)
            .with_block("local:i", 4)
            .store(first, int32(0))
            .store(second, int32(1))
            .store(third, int32(2))
            .store(local_i, int32(3));

        assert_eq!(
            verified.spec.state(),
            &CState::new().with_memory(CMemory::new().with_block("p", 12))
        );
        assert_eq!(verified.spec.args(), &[c_ptr_value(base)]);
        assert_eq!(
            verified.spec.outcome(),
            &CFunctionOutcome::Return {
                value: int32(2),
                state: CState::new().with_memory(final_memory),
            }
        );
        assert_eq!(
            verified.theorem.prop(),
            &Prop::CFunctionSatisfiesSpec {
                function: syntax::parse_function(FILL3_C)
                    .expect("fill3 should parse")
                    .to_megakernel_function(),
                spec: verified.spec.clone(),
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
            error.message().contains("returned Int32(Const(2))"),
            "{}",
            error.message()
        );
    }
}
