//! Tiny `.click` sidecar verifier for the C0 megakernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! proof language design open.

use std::collections::BTreeMap;

use crate::lang::c::syntax::{self, C0Type};
use crate::megakernel::{
    Assumptions, Bv32Term, CExpr, CFunctionOutcome, CFunctionSpec, CMemory, CState, CValue, Prop,
    Ptr, PtrOffsetTerm, Theorem, c_function_spec, c_ptr_value, prove_c_function_satisfies_spec,
    prove_symbolic_c_function_execution,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFile {
    verify_blocks: Vec<VerifyBlock>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifyBlock {
    function_name: String,
    source_path: String,
    requires: Vec<Requirement>,
    ensures: Vec<Ensure>,
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
pub struct VerifiedCFunction {
    pub block: VerifyBlock,
    pub spec: CFunctionSpec,
    pub theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickError {
    message: String,
}

impl ClickFile {
    pub fn verify_blocks(&self) -> &[VerifyBlock] {
        &self.verify_blocks
    }
}

impl VerifyBlock {
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    pub fn source_path(&self) -> &str {
        &self.source_path
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    pub fn ensures(&self) -> &[Ensure] {
        &self.ensures
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
) -> Result<Vec<VerifiedCFunction>, ClickError> {
    let file = parse(click_source)?;
    let c_sources: BTreeMap<&str, &str> = c_sources.iter().copied().collect();
    let mut verified = Vec::new();

    for block in file.verify_blocks {
        let c_source = *c_sources.get(block.source_path()).ok_or_else(|| {
            ClickError::new(format!(
                "verify `{}` refers to missing C source `{}`",
                block.function_name(),
                block.source_path()
            ))
        })?;
        let parsed_function = syntax::parse_function(c_source).map_err(|error| {
            ClickError::new(format!(
                "failed to parse C source `{}`: {}",
                block.source_path(),
                error.message()
            ))
        })?;

        if parsed_function.name() != block.function_name() {
            return Err(ClickError::new(format!(
                "verify block names `{}`, but `{}` defines `{}`",
                block.function_name(),
                block.source_path(),
                parsed_function.name()
            )));
        }

        if block.proof.steps() != [ProofStep::Auto] {
            return Err(ClickError::new(format!(
                "verify `{}` must use exactly `proof {{ auto; }}` in this first slice",
                block.function_name()
            )));
        }

        let (state, args) = initial_call(&block, parsed_function.params())?;
        let function = parsed_function.to_megakernel_function();
        let execution = prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            args.clone(),
            Assumptions::new(),
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`auto` could not prove a single complete execution path for `{}`",
                block.function_name()
            ))
        })?;
        let outcome = match execution.prop() {
            Prop::CFunctionExecutes { outcome, .. } => outcome.clone(),
            prop => {
                return Err(ClickError::new(format!(
                    "`auto` produced an unexpected theorem for `{}`: {prop:?}",
                    block.function_name()
                )));
            }
        };

        check_ensures(&block, &outcome)?;
        let spec = c_function_spec(state, args, Vec::new(), outcome);
        let theorem = prove_c_function_satisfies_spec(function, spec.clone(), Assumptions::new())
            .ok_or_else(|| {
            ClickError::new(format!(
                "`auto` execution for `{}` did not satisfy the packaged spec",
                block.function_name()
            ))
        })?;

        verified.push(VerifiedCFunction {
            block,
            spec,
            theorem,
        });
    }

    Ok(verified)
}

fn initial_call(
    block: &VerifyBlock,
    params: &[syntax::C0Param],
) -> Result<(CState, Vec<CExpr>), ClickError> {
    let valid_ranges: BTreeMap<&str, u32> = block
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
                let bytes = *valid_ranges.get(param.name()).ok_or_else(|| {
                    ClickError::new(format!(
                        "pointer parameter `{}` needs `requires valid_range({}, bytes);`",
                        param.name(),
                        param.name()
                    ))
                })?;
                memory = memory.with_block(param.name(), bytes);
                args.push(c_ptr_value(Ptr {
                    block: param.name().to_string(),
                    offset: PtrOffsetTerm::Const(0),
                }));
            }
            C0Type::Int32 => {
                return Err(ClickError::new(format!(
                    "parameter `{}` is `int32`; this first `.click` verifier slice only supports pointer parameters with `valid_range` requirements",
                    param.name()
                )));
            }
        }
    }

    for name in valid_ranges.keys() {
        if !params.iter().any(|param| param.name() == *name) {
            return Err(ClickError::new(format!(
                "`valid_range` names `{name}`, but `{}` has no such parameter",
                block.function_name()
            )));
        }
    }

    Ok((CState::new().with_memory(memory), args))
}

fn check_ensures(block: &VerifyBlock, outcome: &CFunctionOutcome) -> Result<(), ClickError> {
    for ensure in block.ensures() {
        match ensure {
            Ensure::ResultEqInt32(expected) => match outcome {
                CFunctionOutcome::Return {
                    value: CValue::Int32(Bv32Term::Const(actual)),
                    ..
                } if actual == expected => {}
                CFunctionOutcome::Return { value, .. } => {
                    return Err(ClickError::new(format!(
                        "`ensures result == {expected};` failed for `{}`: returned {value:?}",
                        block.function_name()
                    )));
                }
                other => {
                    return Err(ClickError::new(format!(
                        "`ensures result == {expected};` failed for `{}`: outcome was {other:?}",
                        block.function_name()
                    )));
                }
            },
        }
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
        let mut verify_blocks = Vec::new();

        while self.peek().is_some() {
            verify_blocks.push(self.parse_verify_block()?);
        }

        Ok(ClickFile { verify_blocks })
    }

    fn parse_verify_block(&mut self) -> Result<VerifyBlock, ClickError> {
        self.expect_ident_spelling("verify")?;
        let function_name = self.expect_ident("function name")?;
        self.expect_ident_spelling("in")?;
        let source_path = self.expect_string("C source path")?;
        self.expect(Token::LBrace)?;

        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut proof = None;
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("requires") => requires.push(self.parse_requirement()?),
                Some("ensures") => ensures.push(self.parse_ensure()?),
                Some("proof") => {
                    if proof.is_some() {
                        return Err(self.error("verify block has more than one proof block"));
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

        let Some(proof) = proof else {
            return Err(self.error(format!(
                "verify `{function_name}` is missing a `proof` block"
            )));
        };

        Ok(VerifyBlock {
            function_name,
            source_path,
            requires,
            ensures,
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
        verify fill3 in "fill3.c" {
            requires valid_range(p, 12);
            ensures result == 2;

            proof {
                auto;
            }
        }
    "#;

    #[test]
    fn parses_verify_block() {
        let file = parse(FILL3_CLICK).expect("sidecar should parse");

        assert_eq!(file.verify_blocks().len(), 1);
        let block = &file.verify_blocks()[0];
        assert_eq!(block.function_name(), "fill3");
        assert_eq!(block.source_path(), "fill3.c");
        assert_eq!(
            block.requires(),
            &[Requirement::ValidRange {
                name: "p".to_string(),
                bytes: 12
            }]
        );
        assert_eq!(block.ensures(), &[Ensure::ResultEqInt32(2)]);
        assert_eq!(block.proof().steps(), &[ProofStep::Auto]);
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
