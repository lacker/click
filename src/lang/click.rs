//! Tiny `.click` sidecar verifier for the C0 megakernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! proof language design open.

use std::collections::BTreeMap;

use crate::lang::c::syntax::{self, C0Type};
use crate::megakernel::{
    Assumptions, Bv32Term, CExpr, CFunctionOutcome, CFunctionSpec, CMemory, CState, CValue, Prop,
    Ptr, PtrOffsetTerm, Theorem, Var, c_function_spec, c_ptr_value,
    prove_c_function_satisfies_spec, prove_symbolic_c_function_execution,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFile {
    verifying_sources: Vec<String>,
    function_blocks: Vec<FunctionBlock>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionBlock {
    signature: FunctionSignature,
    theorem_blocks: Vec<TheoremBlock>,
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
pub struct TheoremBlock {
    name: String,
    requires: Vec<Requirement>,
    ensure: Ensure,
    proof: ProofScript,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    ValidRange { name: String, bytes: u32 },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ensure {
    ResultEqInt32(u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofScript {
    steps: Vec<ProofStep>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofStep {
    Auto,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedCTheorem {
    pub source_path: String,
    pub function_block: FunctionBlock,
    pub theorem_block: TheoremBlock,
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

    pub fn theorem_blocks(&self) -> &[TheoremBlock] {
        &self.theorem_blocks
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

impl TheoremBlock {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    pub fn ensure(&self) -> &Ensure {
        &self.ensure
    }

    pub fn proof(&self) -> &ProofScript {
        &self.proof
    }
}

impl ProofScript {
    pub fn steps(&self) -> &[ProofStep] {
        &self.steps
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

        for theorem_block in &function_block.theorem_blocks {
            if theorem_block.proof.steps() != [ProofStep::Auto] {
                return Err(ClickError::new(format!(
                    "`{}.{}` must use exactly `proof {{ auto; }}` in this first slice",
                    function_block.signature.name(),
                    theorem_block.name()
                )));
            }

            let (state, args) = initial_call(
                function_block.signature.name(),
                theorem_block,
                parsed_function.params(),
            )?;
            let function = parsed_function.to_megakernel_function();
            let execution = prove_symbolic_c_function_execution(
                state.clone(),
                function.clone(),
                args.clone(),
                Assumptions::new(),
            )
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`auto` could not prove a single complete execution path for `{}.{}`",
                    function_block.signature.name(),
                    theorem_block.name()
                ))
            })?;
            let outcome = match execution.prop() {
                Prop::CFunctionExecutes { outcome, .. } => outcome.clone(),
                prop => {
                    return Err(ClickError::new(format!(
                        "`auto` produced an unexpected theorem for `{}.{}`: {prop:?}",
                        function_block.signature.name(),
                        theorem_block.name()
                    )));
                }
            };

            check_ensure(function_block.signature.name(), theorem_block, &outcome)?;
            let spec = c_function_spec(state, args, Vec::new(), outcome);
            let theorem =
                prove_c_function_satisfies_spec(function, spec.clone(), Assumptions::new())
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`auto` execution for `{}.{}` did not satisfy the packaged spec",
                            function_block.signature.name(),
                            theorem_block.name()
                        ))
                    })?;

            verified.push(VerifiedCTheorem {
                source_path: source_path.clone(),
                function_block: function_block.clone(),
                theorem_block: theorem_block.clone(),
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
    theorem: &TheoremBlock,
    params: &[syntax::C0Param],
) -> Result<(CState, Vec<CExpr>), ClickError> {
    let valid_ranges: BTreeMap<&str, u32> = theorem
        .requires()
        .iter()
        .map(|requirement| match requirement {
            Requirement::ValidRange { name, bytes } => (name.as_str(), *bytes),
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

    Ok((CState::new().with_memory(memory), args))
}

fn check_ensure(
    function_name: &str,
    theorem: &TheoremBlock,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    match theorem.ensure() {
        Ensure::ResultEqInt32(expected) => match outcome {
            CFunctionOutcome::Return {
                value: CValue::Int32(Bv32Term::Const(actual)),
                ..
            } if actual == expected => {}
            CFunctionOutcome::Return { value, .. } => {
                return Err(ClickError::new(format!(
                    "`ensures result == {expected};` failed for `{function_name}.{}`: returned {value:?}",
                    theorem.name()
                )));
            }
            other => {
                return Err(ClickError::new(format!(
                    "`ensures result == {expected};` failed for `{function_name}.{}`: outcome was {other:?}",
                    theorem.name()
                )));
            }
        },
    }

    Ok(())
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
    Comma,
    Semicolon,
    EqEq,
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

        let mut theorem_blocks = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error(format!(
                    "expected theorem block or `}}` in `{}`",
                    signature.name()
                )));
            }
            theorem_blocks.push(self.parse_theorem_block()?);
        }
        self.expect(Token::RBrace)?;

        if theorem_blocks.is_empty() {
            return Err(self.error(format!(
                "`{}` must contain at least one theorem block",
                signature.name()
            )));
        }

        Ok(FunctionBlock {
            signature,
            theorem_blocks,
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

    fn parse_theorem_block(&mut self) -> Result<TheoremBlock, ClickError> {
        let name = self.expect_ident("theorem name")?;
        self.expect(Token::LBrace)?;

        let mut requires = Vec::new();
        let mut ensure = None;
        let mut proof = None;
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("requires") => requires.push(self.parse_requirement()?),
                Some("ensures") => {
                    if ensure.is_some() {
                        return Err(
                            self.error(format!("theorem `{name}` has more than one `ensures`"))
                        );
                    }
                    ensure = Some(self.parse_ensure()?);
                }
                Some("proof") => {
                    if proof.is_some() {
                        return Err(
                            self.error(format!("theorem `{name}` has more than one proof block"))
                        );
                    }
                    proof = Some(self.parse_proof()?);
                }
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `requires`, `ensures`, or `proof`, got `{keyword}`"
                    )));
                }
                None => {
                    return Err(self.error("expected `requires`, `ensures`, `proof`, or `}`"));
                }
            }
        }
        self.expect(Token::RBrace)?;

        let Some(ensure) = ensure else {
            return Err(self.error(format!("theorem `{name}` is missing an `ensures` clause")));
        };
        let Some(proof) = proof else {
            return Err(self.error(format!("theorem `{name}` is missing a `proof` block")));
        };

        Ok(TheoremBlock {
            name,
            requires,
            ensure,
            proof,
        })
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        self.expect_ident_spelling("valid_range")?;
        self.expect(Token::LParen)?;
        let name = self.expect_ident("range base name")?;
        self.expect(Token::Comma)?;
        let bytes = self.expect_number("range byte size")?;
        self.expect(Token::RParen)?;
        self.expect(Token::Semicolon)?;

        Ok(Requirement::ValidRange { name, bytes })
    }

    fn parse_ensure(&mut self) -> Result<Ensure, ClickError> {
        self.expect_ident_spelling("ensures")?;
        self.expect_ident_spelling("result")?;
        self.expect(Token::EqEq)?;
        let expected = self.expect_number("expected int32 result")?;
        self.expect(Token::Semicolon)?;

        Ok(Ensure::ResultEqInt32(expected))
    }

    fn parse_proof(&mut self) -> Result<ProofScript, ClickError> {
        self.expect_ident_spelling("proof")?;
        self.expect(Token::LBrace)?;
        let mut steps = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("auto") => {
                    self.position += 1;
                    self.expect(Token::Semicolon)?;
                    steps.push(ProofStep::Auto);
                }
                Some(keyword) => {
                    return Err(self.error(format!("expected proof step, got `{keyword}`")));
                }
                None => {
                    return Err(self.error("expected proof step or `}`"));
                }
            }
        }
        self.expect(Token::RBrace)?;

        Ok(ProofScript { steps })
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
            ',' => {
                tokens.push(Token::Comma);
                index += 1;
            }
            ';' => {
                tokens.push(Token::Semicolon);
                index += 1;
            }
            '*' => {
                tokens.push(Token::Star);
                index += 1;
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
                *(p + i) = i;
                i = i + 1;
            }
            return *(p + 2);
        }
    "#;

    const FILL3_CLICK: &str = r#"
        verifying "fill3.c";

        int32 fill3(int32* p) {
            returns_second {
                requires valid_range(p, 12);
                ensures result == 2;

                proof {
                    auto;
                }
            }
        }
    "#;

    #[test]
    fn parses_checked_signature_and_theorem_block() {
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
        assert_eq!(function.theorem_blocks().len(), 1);
        let theorem = &function.theorem_blocks()[0];
        assert_eq!(theorem.name(), "returns_second");
        assert_eq!(
            theorem.requires(),
            &[Requirement::ValidRange {
                name: "p".to_string(),
                bytes: 12
            }]
        );
        assert_eq!(theorem.ensure(), &Ensure::ResultEqInt32(2));
        assert_eq!(theorem.proof().steps(), &[ProofStep::Auto]);
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
        let source = FILL3_CLICK.replace("ensures result == 2;", "ensures result == 3;");
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong result should fail");

        assert!(
            error.message().contains("returned Int32(Const(2))"),
            "{}",
            error.message()
        );
    }
}
