mod tokenizer;

use tokenizer::tokenize;

use super::*;

/// Click's recursive-descent proposition and contract-expression parsers use
/// the native stack once per syntactically nested parenthesis. Keep the
/// supported surface depth explicit and reject deeper input before recursive
/// parsing begins.
pub(super) const PARENTHESIS_NESTING_LIMIT: usize = 16;

pub(super) fn parse(source: &str) -> Result<ClickFile, ClickError> {
    Parser::new(source)?.parse_file()
}

pub(super) fn parse_with_struct_layouts(
    source: &str,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
) -> Result<ClickFile, ClickError> {
    Parser::new_with_struct_layouts(source, struct_layouts)?.parse_file()
}

pub(super) fn parse_file_items(source: &str) -> Result<ClickFile, ClickError> {
    let mut parser = Parser::new(source)?;
    parser.parse_file_items()
}

fn is_tactic_name(name: &str) -> bool {
    matches!(name, "auto" | "frame" | "simp")
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(u32),
    UInt8Number(u8),
    CharLiteral(u8),
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
    Dot,
    DotDot,
    Arrow,
    Equal,
    EqualEqual,
    BangEqual,
    LessThan,
    LessEqual,
    ShiftLeft,
    GreaterThan,
    GreaterEqual,
    ShiftRight,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Caret,
    Tilde,
    Pipe,
}

impl Token {
    /// A human-readable rendering for diagnostics, such as `` identifier `x` ``
    /// or `` `;` ``.
    fn describe(&self) -> String {
        match self {
            Self::Ident(name) => format!("identifier `{name}`"),
            Self::Number(value) => format!("number `{value}`"),
            Self::UInt8Number(value) => format!("uint8 number `{value}u8`"),
            Self::CharLiteral(value) => {
                format!("character literal `{}`", (*value as char).escape_default())
            }
            Self::String(value) => format!("string literal `\"{value}\"`"),
            other => format!("`{}`", other.spelling()),
        }
    }

    fn spelling(&self) -> &'static str {
        match self {
            Self::Ident(_)
            | Self::Number(_)
            | Self::UInt8Number(_)
            | Self::CharLiteral(_)
            | Self::String(_) => "",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::Colon => ":",
            Self::Comma => ",",
            Self::Semicolon => ";",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::Arrow => "->",
            Self::Equal => "=",
            Self::EqualEqual => "==",
            Self::BangEqual => "!=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::ShiftLeft => "<<",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
            Self::ShiftRight => ">>",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::Amp => "&",
            Self::Caret => "^",
            Self::Tilde => "~",
            Self::Pipe => "|",
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    matching_parentheses: Vec<Option<usize>>,
    position: usize,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    current_struct_params: BTreeMap<String, String>,
    current_struct_array_params: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
    struct_pointer: bool,
}

fn is_c_type_keyword(name: &str) -> bool {
    matches!(
        name,
        "void"
            | "struct"
            | "int32"
            | "int"
            | "int32_t"
            | "uint8"
            | "uint8_t"
            | "unsigned"
            | "signed"
            | "char"
            | "short"
            | "long"
            | "size_t"
            | "int16_t"
            | "int64_t"
            | "uint16_t"
            | "uint32_t"
            | "uint64_t"
            | "float"
            | "double"
            | "volatile"
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedParameter {
    parameter: FunctionParameter,
    struct_name: Option<String>,
    declared_bytes: Option<u32>,
    struct_array: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedParameters {
    parameters: Vec<FunctionParameter>,
    struct_params: BTreeMap<String, String>,
    struct_array_params: BTreeSet<String>,
    declared_loadable_bytes: Vec<(String, u32)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedFunctionSignature {
    signature: FunctionSignature,
    struct_params: BTreeMap<String, String>,
    struct_array_params: BTreeSet<String>,
    return_struct_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedField {
    c_type: C0Type,
    struct_name: Option<String>,
    offset_bytes: u32,
    byte_width: u32,
    slot_end_bytes: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ContractLetBinding {
    pub(super) name: String,
    pub(super) c_type: Option<C0Type>,
    kind: ContractLetBindingKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ContractLetBindingKind {
    Value(ContractExpression),
    Where(ClickProposition),
}

impl ContractLetBinding {
    pub(super) fn value(&self) -> Option<&ContractExpression> {
        match &self.kind {
            ContractLetBindingKind::Value(value) => Some(value),
            ContractLetBindingKind::Where(_) => None,
        }
    }

    pub(super) fn where_condition(&self) -> Option<&ClickProposition> {
        match &self.kind {
            ContractLetBindingKind::Value(_) => None,
            ContractLetBindingKind::Where(condition) => Some(condition),
        }
    }
}

impl Parser {
    fn new(source: &str) -> Result<Self, ClickError> {
        Self::new_with_struct_layouts(source, BTreeMap::new())
    }

    fn new_with_struct_layouts(
        source: &str,
        struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    ) -> Result<Self, ClickError> {
        let (tokens, positions) = tokenize(source)?;
        let matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
        Ok(Self {
            tokens,
            positions,
            matching_parentheses,
            position: 0,
            struct_layouts,
            current_struct_params: BTreeMap::new(),
            current_struct_array_params: BTreeSet::new(),
        })
    }

    fn parse_file(mut self) -> Result<ClickFile, ClickError> {
        let file = super::validation::expand_declared_resource_clauses(self.parse_file_items()?)?;
        super::validation::validate_click_definitions(&file)?;
        Ok(file)
    }

    fn parse_file_items(&mut self) -> Result<ClickFile, ClickError> {
        let mut verifying_sources = Vec::new();
        let mut predicate_definitions = Vec::new();
        let mut click_function_definitions = Vec::new();
        let mut resource_definitions = Vec::new();
        let mut theorem_definitions = Vec::new();
        let mut function_blocks = Vec::new();

        while self.peek().is_some() {
            if self.peek_ident() == Some("verifying") {
                verifying_sources.push(self.parse_verifying_source()?);
            } else if self.peek_ident() == Some("predicate") {
                predicate_definitions.push(self.parse_predicate_definition()?);
            } else if self.peek_ident() == Some("function") {
                click_function_definitions.push(self.parse_click_function_definition()?);
            } else if self.peek_ident() == Some("theorem") {
                theorem_definitions.push(self.parse_theorem_definition()?);
            } else if self.peek_ident() == Some("abstract") {
                resource_definitions.push(self.parse_resource_definition(true)?);
            } else if self.peek_ident() == Some("resource") {
                resource_definitions.push(self.parse_resource_definition(false)?);
            } else if self.peek_ident() == Some("counted") {
                return Err(self
                    .error("`counted resource` has been removed; declare an ordinary `resource`"));
            } else {
                function_blocks.push(self.parse_function_block()?);
            }
        }

        let file = ClickFile {
            verifying_sources,
            predicate_definitions,
            click_function_definitions,
            resource_definitions,
            theorem_definitions,
            function_blocks,
        };
        Ok(file)
    }

    fn parse_verifying_source(&mut self) -> Result<String, ClickError> {
        self.expect_ident_spelling("verifying")?;
        let source_path = self.expect_string("C source path")?;
        self.expect(Token::Semicolon)?;
        Ok(source_path)
    }

    fn parse_predicate_definition(&mut self) -> Result<PredicateDefinition, ClickError> {
        self.expect_ident_spelling("predicate")?;
        let name = self.expect_ident("predicate name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = std::mem::replace(
            &mut self.current_struct_array_params,
            parsed_parameters.struct_array_params,
        );
        let body = self.parse_proposition()?;
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;
        self.expect(Token::RBrace)?;
        Ok(PredicateDefinition {
            name,
            parameters: parsed_parameters.parameters,
            body,
        })
    }

    fn parse_click_function_definition(&mut self) -> Result<ClickFunctionDefinition, ClickError> {
        self.expect_ident_spelling("function")?;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Arrow)?;
        let parsed_return_type = self.parse_type()?;
        if parsed_return_type.struct_name.is_some() && !parsed_return_type.struct_pointer {
            return Err(self.error("only pointer-to-struct types are supported"));
        }
        let return_type = parsed_return_type.c_type;
        if return_type == C0Type::Void {
            return Err(self.error("pure Click functions must return a value"));
        }
        let decreases = if self.peek_ident() == Some("decreases") {
            self.position += 1;
            Some(self.parse_contract_expression()?)
        } else {
            None
        };
        self.expect(Token::LBrace)?;
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = std::mem::replace(
            &mut self.current_struct_array_params,
            parsed_parameters.struct_array_params,
        );
        let body = self.parse_contract_expression()?;
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;
        self.expect(Token::RBrace)?;
        Ok(ClickFunctionDefinition {
            name,
            parameters: parsed_parameters.parameters,
            return_type,
            decreases,
            body,
        })
    }

    fn parse_resource_definition(
        &mut self,
        is_abstract: bool,
    ) -> Result<ResourceDefinition, ClickError> {
        if is_abstract {
            self.expect_ident_spelling("abstract")?;
        }
        self.expect_ident_spelling("resource")?;
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = std::mem::replace(
            &mut self.current_struct_array_params,
            parsed_parameters.struct_array_params,
        );
        let composite_body = match self.peek() {
            Some(Token::Semicolon) if is_abstract => {
                self.position += 1;
                None
            }
            Some(Token::Semicolon) => {
                return Err(self
                    .error("a resource without a body must be declared with `abstract resource`"));
            }
            Some(Token::LBrace) if !is_abstract => Some(self.parse_composite_resource_body()?),
            Some(Token::LBrace) => {
                return Err(self.error("an `abstract resource` cannot have a body"));
            }
            Some(token) => {
                return Err(self.error(format!("expected resource body, got {token:?}")));
            }
            None => {
                return Err(self.error("expected resource body, got end of input"));
            }
        };
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;
        Ok(ResourceDefinition {
            name,
            parameters: parsed_parameters.parameters,
            composite_body,
        })
    }

    fn parse_composite_resource_body(&mut self) -> Result<CompositeResourceBody, ClickError> {
        self.expect(Token::LBrace)?;
        let condition = if self.peek_ident() == Some("if") {
            self.position += 1;
            let condition = self.parse_proposition()?;
            self.expect(Token::LBrace)?;
            Some(condition)
        } else {
            None
        };
        let mut contains = Vec::new();
        let mut facts = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("contains") => {
                    self.position += 1;
                    contains.push(self.parse_composite_resource_contains_clause()?);
                    self.expect(Token::Semicolon)?;
                }
                Some("owns") => {
                    self.position += 1;
                    contains.push(self.parse_resource_target(ResourceAccessMode::Own)?);
                    self.expect(Token::Semicolon)?;
                }
                Some("views") => {
                    self.position += 1;
                    contains.push(self.parse_resource_target(ResourceAccessMode::View)?);
                    self.expect(Token::Semicolon)?;
                }
                Some("fact") => {
                    self.position += 1;
                    facts.push(self.parse_proposition()?);
                    self.expect(Token::Semicolon)?;
                }
                Some(name) => {
                    return Err(self.error(format!(
                        "expected `contains`, `owns`, `views`, or `fact` in resource body, got `{name}`"
                    )));
                }
                None => {
                    return Err(self.error(
                        "expected `contains`, `owns`, `views`, or `fact` in resource body, got end of input",
                    ));
                }
            }
        }
        self.expect(Token::RBrace)?;
        if condition.is_some() {
            self.expect(Token::RBrace)?;
        }
        Ok(CompositeResourceBody {
            condition,
            contains,
            facts,
        })
    }

    fn parse_composite_resource_contains_clause(&mut self) -> Result<ResourceClause, ClickError> {
        self.parse_declared_resource_call()
    }

    fn parse_click_parameters(&mut self) -> Result<ParsedParameters, ClickError> {
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        let mut struct_array_params = BTreeSet::new();
        let mut declared_loadable_bytes = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(ParsedParameters {
                parameters,
                struct_params,
                struct_array_params,
                declared_loadable_bytes,
            });
        }

        loop {
            let name = self.expect_ident("Click parameter name")?;
            if is_c_type_keyword(&name) {
                return Err(
                    self.error("Click-native binders use `name: type`, for example `value: int32`")
                );
            }
            self.expect(Token::Colon)?;
            let parsed_type = self.parse_type()?;
            let parsed_parameter = self.parse_parameter_array_suffix(name, parsed_type)?;
            if let Some(struct_name) = parsed_parameter.struct_name {
                struct_params.insert(parsed_parameter.parameter.name.clone(), struct_name);
            }
            if parsed_parameter.struct_array {
                struct_array_params.insert(parsed_parameter.parameter.name.clone());
            }
            if let Some(bytes) = parsed_parameter.declared_bytes {
                declared_loadable_bytes.push((parsed_parameter.parameter.name.clone(), bytes));
            }
            parameters.push(parsed_parameter.parameter);

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => {
                    return Ok(ParsedParameters {
                        parameters,
                        struct_params,
                        struct_array_params,
                        declared_loadable_bytes,
                    });
                }
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    fn parse_theorem_definition(&mut self) -> Result<TheoremDefinition, ClickError> {
        self.expect_ident_spelling("theorem")?;
        let name = self.expect_ident("theorem name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;

        let parameter_names = parsed_parameters
            .parameters
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<BTreeSet<_>>();
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = std::mem::replace(
            &mut self.current_struct_array_params,
            parsed_parameters.struct_array_params,
        );
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("let") => {
                    let binding = self.parse_contract_let_binding()?;
                    if parameter_names.contains(binding.name.as_str()) {
                        return Err(self.error(format!(
                            "theorem `let` `{}` conflicts with a parameter in `{name}`",
                            binding.name
                        )));
                    }
                    if !contract_let_names.insert(binding.name.clone()) {
                        return Err(self.error(format!(
                            "duplicate theorem `let` `{}` in `{name}`",
                            binding.name
                        )));
                    }
                    let substitutions = contract_let_substitutions(&contract_lets);
                    let kind = match binding.kind {
                        ContractLetBindingKind::Value(value) => ContractLetBindingKind::Value(
                            substitute_contract_expression(&value, &substitutions)
                                .map_err(|message| self.error(message))?,
                        ),
                        ContractLetBindingKind::Where(condition) => {
                            ContractLetBindingKind::Where(condition)
                        }
                    };
                    contract_lets.push(ContractLetBinding { kind, ..binding });
                }
                Some("requires") => {
                    let requirement = self.parse_requirement()?;
                    requires.push(
                        apply_contract_lets_to_requirement(requirement, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("owns") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    let proof = self.parse_proof_clause_or_default()?;
                    requires.push(
                        apply_contract_lets_to_requirement(
                            Requirement::Resource(resource.clone()),
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                name: None,
                                ensure: Ensure::Resource(resource),
                                proof,
                            },
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("views") => {
                    self.position += 1;
                    let resource = self.parse_resource_target(ResourceAccessMode::View)?;
                    self.expect(Token::Semicolon)?;
                    requires.push(
                        apply_contract_lets_to_requirement(
                            Requirement::Resource(resource),
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("consumes") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    self.expect(Token::Semicolon)?;
                    requires.push(
                        apply_contract_lets_to_requirement(
                            Requirement::Resource(resource),
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("produces") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    let proof = self.parse_proof_clause_or_default()?;
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                name: None,
                                ensure: Ensure::Resource(resource),
                                proof,
                            },
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("ensures") => {
                    let ensure = self.parse_ensure_clause()?;
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(ensure, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `ensures`, or `}}` in theorem `{name}`, got `{keyword}`"
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `ensures`, or `}}` in theorem `{name}`"
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;

        Ok(TheoremDefinition {
            name,
            parameters: parsed_parameters.parameters,
            requires,
            ensures,
        })
    }

    fn parse_function_block(&mut self) -> Result<FunctionBlock, ClickError> {
        let ParsedFunctionSignature {
            signature,
            mut struct_params,
            struct_array_params,
            return_struct_name,
        } = self.parse_function_signature()?;
        if let Some(struct_name) = return_struct_name {
            struct_params.insert("result".to_string(), struct_name);
        }
        self.expect(Token::LBrace)?;

        let parameter_names = signature
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<BTreeSet<_>>();
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut decreases = None;
        let mut effects = Vec::new();
        let mut constructs = Vec::new();
        let mut ensures = Vec::new();
        let previous_struct_params =
            std::mem::replace(&mut self.current_struct_params, struct_params);
        let previous_struct_array_params =
            std::mem::replace(&mut self.current_struct_array_params, struct_array_params);
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("let") => {
                    let binding = self.parse_contract_let_binding()?;
                    if parameter_names.contains(binding.name.as_str()) {
                        return Err(self.error(format!(
                            "contract `let` `{}` conflicts with a C parameter in `{}`",
                            binding.name,
                            signature.name()
                        )));
                    }
                    if !contract_let_names.insert(binding.name.clone()) {
                        return Err(self.error(format!(
                            "duplicate contract `let` `{}` in `{}`",
                            binding.name,
                            signature.name()
                        )));
                    }
                    let substitutions = contract_let_substitutions(&contract_lets);
                    let kind = match binding.kind {
                        ContractLetBindingKind::Value(value) => ContractLetBindingKind::Value(
                            substitute_contract_expression(&value, &substitutions)
                                .map_err(|message| self.error(message))?,
                        ),
                        ContractLetBindingKind::Where(condition) => {
                            ContractLetBindingKind::Where(condition)
                        }
                    };
                    contract_lets.push(ContractLetBinding { kind, ..binding });
                }
                Some("requires") => {
                    let requirement = self.parse_requirement()?;
                    requires.push(
                        apply_contract_lets_to_requirement(requirement, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("decreases") => {
                    self.position += 1;
                    if decreases.is_some() {
                        return Err(self.error(format!(
                            "duplicate `decreases` clause in `{}`",
                            signature.name()
                        )));
                    }
                    decreases = Some(if self.peek_ident() == Some("resource") {
                        self.position += 1;
                        let resource = self.parse_resource_target(ResourceAccessMode::View)?;
                        self.expect(Token::Semicolon)?;
                        CFunctionDecrease::Resource(
                            apply_contract_lets_to_resource_clause(resource, &contract_lets)
                                .map_err(|message| self.error(message))?,
                        )
                    } else {
                        let measure = self.parse_contract_expression()?;
                        self.expect(Token::Semicolon)?;
                        CFunctionDecrease::Numeric(
                            substitute_contract_expression(
                                &measure,
                                &contract_let_substitutions(&contract_lets),
                            )
                            .map_err(|message| self.error(message))?,
                        )
                    });
                }
                Some("owns") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    let proof = self.parse_proof_clause_or_default()?;
                    requires.push(
                        apply_contract_lets_to_requirement(
                            Requirement::Resource(resource.clone()),
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                name: None,
                                ensure: Ensure::Resource(resource),
                                proof,
                            },
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("views") => {
                    self.position += 1;
                    let resource = self.parse_resource_target(ResourceAccessMode::View)?;
                    self.expect(Token::Semicolon)?;
                    requires.push(
                        apply_contract_lets_to_requirement(
                            Requirement::Resource(resource),
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("consumes") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    self.expect(Token::Semicolon)?;
                    requires.push(
                        apply_contract_lets_to_requirement(
                            Requirement::Resource(resource),
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("produces") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    let proof = self.parse_proof_clause_or_default()?;
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                name: None,
                                ensure: Ensure::Resource(resource),
                                proof,
                            },
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("immutable" | "mutable") => {
                    let effect = self.parse_effect_clause()?;
                    effects.push(
                        apply_contract_lets_to_effect_clause(effect, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("constructs") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    self.expect(Token::Semicolon)?;
                    constructs.push(
                        apply_contract_lets_to_resource_clause(resource, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("ensures") => {
                    let ensure = self.parse_ensure_clause()?;
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(ensure, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `decreases`, `owns`, `views`, `consumes`, `produces`, `constructs`, `immutable`, `mutable`, `ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `decreases`, `owns`, `views`, `consumes`, `produces`, `constructs`, `immutable`, `mutable`, `ensures`, or `}}` in `{}`",
                        signature.name()
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let grouped_proof = if self.peek_ident() == Some("by") {
            let proof = self.parse_by_clause()?;
            if effects
                .iter()
                .any(|clause| !matches!(clause.proof(), SourceProof::Default))
                || ensures
                    .iter()
                    .any(|clause| !matches!(clause.proof(), SourceProof::Default))
            {
                return Err(self.error(
                    "a grouped function proof cannot be combined with individual claim proofs",
                ));
            }
            Some(proof)
        } else {
            None
        };
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;

        let requirement_label_indices = requires
            .iter()
            .enumerate()
            .filter_map(|(index, requirement)| {
                requirement.label().map(|label| (label.to_string(), index))
            })
            .collect();

        Ok(FunctionBlock {
            signature,
            requires,
            requirement_label_indices,
            decreases,
            structural_clauses: Vec::new(),
            effects,
            constructs,
            ensures,
            grouped_proof,
        })
    }

    fn parse_contract_let_binding(&mut self) -> Result<ContractLetBinding, ClickError> {
        self.expect_ident_spelling("let")?;
        let name = self.expect_ident("let binding name")?;
        let c_type = if self.peek() == Some(&Token::Colon) {
            self.position += 1;
            let parsed_type = self.parse_type()?;
            if parsed_type.struct_name.is_some() && !parsed_type.struct_pointer {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            Some(parsed_type.c_type)
        } else {
            None
        };
        let kind = if self.peek() == Some(&Token::Equal) {
            self.position += 1;
            ContractLetBindingKind::Value(self.parse_contract_expression()?)
        } else if self.peek_ident() == Some("where") {
            self.position += 1;
            if c_type.is_none() {
                return Err(self.error("`let ... where` requires an explicit type annotation"));
            }
            ContractLetBindingKind::Where(self.parse_proposition()?)
        } else {
            return Err(self.error("expected `=` or `where` in `let` binding"));
        };
        self.expect(Token::Semicolon)?;
        Ok(ContractLetBinding { name, c_type, kind })
    }

    fn parse_function_signature(&mut self) -> Result<ParsedFunctionSignature, ClickError> {
        let parsed_return_type = self.parse_type()?;
        if parsed_return_type.struct_name.is_some() && !parsed_return_type.struct_pointer {
            return Err(self.error("only pointer-to-struct types are supported"));
        }
        let return_type = parsed_return_type.c_type;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let struct_params = parsed_parameters.struct_params;
        let struct_array_params = parsed_parameters.struct_array_params;

        Ok(ParsedFunctionSignature {
            signature: FunctionSignature {
                return_type,
                name,
                parameters: parsed_parameters.parameters,
                declared_loadable_bytes: parsed_parameters.declared_loadable_bytes,
            },
            struct_params,
            struct_array_params,
            return_struct_name: parsed_return_type.struct_name,
        })
    }

    fn parse_parameters(&mut self) -> Result<ParsedParameters, ClickError> {
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        let mut struct_array_params = BTreeSet::new();
        let mut declared_loadable_bytes = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(ParsedParameters {
                parameters,
                struct_params,
                struct_array_params,
                declared_loadable_bytes,
            });
        }

        loop {
            let parsed_type = self.parse_type()?;
            let parsed_parameter = if self.peek() == Some(&Token::LParen) {
                let (name, c_type) = self.parse_function_pointer_declarator(parsed_type.c_type)?;
                ParsedParameter {
                    parameter: FunctionParameter {
                        c_type,
                        name,
                        struct_name: None,
                    },
                    struct_name: None,
                    declared_bytes: None,
                    struct_array: false,
                }
            } else {
                let name = self.expect_ident("parameter name")?;
                self.parse_parameter_array_suffix(name, parsed_type)?
            };
            if let Some(struct_name) = parsed_parameter.struct_name {
                struct_params.insert(parsed_parameter.parameter.name.clone(), struct_name);
            }
            if parsed_parameter.struct_array {
                struct_array_params.insert(parsed_parameter.parameter.name.clone());
            }
            if let Some(bytes) = parsed_parameter.declared_bytes {
                declared_loadable_bytes.push((parsed_parameter.parameter.name.clone(), bytes));
            }
            parameters.push(parsed_parameter.parameter);

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => {
                    return Ok(ParsedParameters {
                        parameters,
                        struct_params,
                        struct_array_params,
                        declared_loadable_bytes,
                    });
                }
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    fn parse_type(&mut self) -> Result<ParsedType, ClickError> {
        let spelling = self.expect_ident("type")?;
        if spelling == "struct" {
            let struct_name = self.expect_ident("struct name")?;
            if self.peek() == Some(&Token::Star) {
                self.position += 1;
                return Ok(ParsedType {
                    c_type: C0Type::Int32Pointer,
                    struct_name: Some(struct_name),
                    struct_pointer: true,
                });
            }
            return Ok(ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(struct_name),
                struct_pointer: false,
            });
        }

        let scalar_type = match spelling.as_str() {
            "void" => C0Type::Void,
            "int32" | "int" | "int32_t" => C0Type::Int32,
            "uint8" | "uint8_t" => C0Type::UInt8,
            "unsigned" => {
                if self.peek_ident() == Some("char") {
                    self.position += 1;
                    C0Type::UInt8
                } else {
                    return Err(self.error(
                        "unsupported integer width `unsigned`; only `unsigned char` is modeled",
                    ));
                }
            }
            "signed" => {
                if self.peek_ident() == Some("char") {
                    self.position += 1;
                    return Err(self.error(
                        "unsupported C type `signed char`: signed char is not modeled; use `unsigned char` or `uint8_t`",
                    ));
                }
                return Err(self.error(
                    "unsupported integer width `signed`: signed integer widths are not modeled",
                ));
            }
            "char" => {
                return Err(self.error(
                    "unsupported C type `char`: signed char is not modeled; use `unsigned char` or `uint8_t`",
                ));
            }
            "short" | "long" | "size_t" | "int16_t" | "int64_t" | "uint16_t" | "uint32_t"
            | "uint64_t" => {
                return Err(self.error(format!(
                    "unsupported integer width `{spelling}`: see the integer-types issue"
                )));
            }
            "float" | "double" => {
                return Err(self.error(format!(
                    "unsupported C type `{spelling}`: floating-point values are not modeled in C0"
                )));
            }
            "volatile" => {
                return Err(self.error("the `volatile` qualifier is not supported in C0"));
            }
            _ => {
                return Err(self.error(format!(
                    "unknown C type `{spelling}`; expected a supported standard spelling or `struct`"
                )));
            }
        };
        let mut c_type = scalar_type;
        while self.peek() == Some(&Token::Star) {
            self.position += 1;
            c_type = match c_type {
                C0Type::Void => return Err(self.error("`void *` is not supported yet")),
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::UInt8 => C0Type::UInt8Pointer,
                C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
                _ => return Err(self.error("pointer depth beyond `**` is not supported")),
            };
        }
        Ok(ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
        })
    }

    fn parse_function_pointer_declarator(
        &mut self,
        return_type: C0Type,
    ) -> Result<(String, C0Type), ClickError> {
        self.expect(Token::LParen)?;
        self.expect(Token::Star)?;
        let name = self.expect_ident("function-pointer parameter name")?;
        self.expect(Token::RParen)?;
        self.expect(Token::LParen)?;
        let mut parameter_types = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                let parsed_type = self.parse_type()?;
                if parsed_type.struct_name.is_some() || parsed_type.c_type == C0Type::Void {
                    return Err(
                        self.error("function-pointer parameters must use modeled non-struct types")
                    );
                }
                let mut parameter_type = parsed_type.c_type;
                if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    if matches!(self.peek(), Some(Token::Number(_))) {
                        self.position += 1;
                    }
                    self.expect(Token::RBracket)?;
                    parameter_type = match parameter_type {
                        C0Type::Int32 => C0Type::Int32Pointer,
                        C0Type::UInt8 => C0Type::UInt8Pointer,
                        C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                        C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
                        _ => return Err(self.error("only modeled array parameters are supported")),
                    };
                }
                parameter_types.push(parameter_type);
                if matches!(self.peek(), Some(Token::Ident(_))) {
                    self.position += 1;
                }
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::RParen) => break,
                    Some(token) => {
                        return Err(self.error(format!(
                            "expected `,` or `)` in function-pointer parameter list, got {token:?}"
                        )));
                    }
                    None => return Err(self.error(
                        "expected `,` or `)` in function-pointer parameter list, got end of input",
                    )),
                }
            }
        }
        self.expect(Token::RParen)?;
        if parameter_types.len() > 13 {
            return Err(self.error("function-pointer signatures support at most 13 parameters"));
        }
        let parameter_types = parameter_types
            .into_iter()
            .map(C0Type::to_kernel_type)
            .collect::<Vec<_>>();
        let signature = crate::kernel::CType::function_pointer_signature(
            return_type.to_kernel_type(),
            &parameter_types,
        );
        if signature == 0 {
            return Err(self.error("function-pointer signature uses an unsupported modeled type"));
        }
        Ok((name, C0Type::FunctionPointer(signature)))
    }

    fn parse_parameter_array_suffix(
        &mut self,
        name: String,
        parsed_type: ParsedType,
    ) -> Result<ParsedParameter, ClickError> {
        if parsed_type.c_type == C0Type::Void {
            return Err(self.error("parameters cannot have type `void`"));
        }
        if self.peek() != Some(&Token::LBracket) {
            let struct_name = parsed_type.struct_name;
            if struct_name.is_some() && !parsed_type.struct_pointer {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            return Ok(ParsedParameter {
                parameter: FunctionParameter {
                    c_type: parsed_type.c_type,
                    name,
                    struct_name: struct_name.clone(),
                },
                struct_name,
                declared_bytes: None,
                struct_array: false,
            });
        }
        let struct_name = parsed_type.struct_name.clone();
        if struct_name.is_some() {
            if parsed_type.struct_pointer {
                return Err(self.error("only arrays of struct values are supported"));
            }
            self.position += 1;
            if matches!(self.peek(), Some(Token::Number(_))) {
                self.position += 1;
            }
            self.expect(Token::RBracket)?;
            return Ok(ParsedParameter {
                parameter: FunctionParameter {
                    c_type: C0Type::Int32Pointer,
                    name,
                    struct_name: struct_name.clone(),
                },
                struct_name,
                declared_bytes: None,
                struct_array: true,
            });
        }
        let (pointer_type, element_width) = match parsed_type.c_type {
            C0Type::Int32 => (C0Type::Int32Pointer, 4),
            C0Type::UInt8 => (C0Type::UInt8Pointer, 1),
            C0Type::Int32Pointer => (C0Type::Int32PointerPointer, 8),
            C0Type::UInt8Pointer => (C0Type::UInt8PointerPointer, 8),
            _ => return Err(self.error("only scalar array parameters are supported")),
        };

        self.position += 1;
        let mut declared_bytes = None;
        if let Some(Token::Number(length)) = self.peek() {
            declared_bytes = length.checked_mul(element_width);
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(ParsedParameter {
            parameter: FunctionParameter {
                c_type: pointer_type,
                name,
                struct_name: None,
            },
            struct_name: None,
            declared_bytes,
            struct_array: false,
        })
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        let label = if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next() == Some(&Token::Colon)
        {
            let label = self.expect_ident("requirement label")?;
            self.expect(Token::Colon)?;
            Some(label)
        } else {
            None
        };
        let requirement = match (self.peek_ident(), self.peek_next()) {
            (Some("loadable"), Some(Token::LParen)) => self.parse_loadable_requirement()?,
            _ => {
                let proposition = self.parse_proposition()?;
                self.expect(Token::Semicolon)?;
                Requirement::Proposition(proposition)
            }
        };
        if !matches!(requirement, Requirement::Proposition(_)) {
            self.expect(Token::Semicolon)?;
        }
        Ok(if let Some(label) = label {
            Requirement::Labeled {
                label,
                requirement: Box::new(requirement),
            }
        } else {
            requirement
        })
    }

    fn parse_loadable_requirement(&mut self) -> Result<Requirement, ClickError> {
        match self.peek_ident() {
            Some("loadable") => {
                self.position += 1;
            }
            _ => return Err(self.error("expected `loadable` requirement")),
        }
        self.expect(Token::LParen)?;
        let segment = self.parse_current_contract_segment()?;
        self.expect(Token::RParen)?;
        Ok(Requirement::LoadableSegment { segment })
    }

    fn parse_resource_subject_pair(
        &mut self,
        relation: &str,
    ) -> Result<(ResourceSubject, ResourceSubject), ClickError> {
        self.expect_ident_spelling(relation)?;
        self.expect(Token::LParen)?;
        let left = self.parse_resource_subject()?;
        self.expect(Token::Comma)?;
        let right = self.parse_resource_subject()?;
        self.expect(Token::RParen)?;
        Ok((left, right))
    }

    fn parse_resource_subject(&mut self) -> Result<ResourceSubject, ClickError> {
        if self.peek_ident() == Some("memory") && self.peek_next() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::LParen)?;
            let segment = self.parse_current_contract_segment()?;
            self.expect(Token::RParen)?;
            return Ok(ResourceSubject::Memory(segment));
        }

        let (name, arguments) = self.parse_call_arguments("resource subject name")?;
        Ok(ResourceSubject::Declared {
            kind: ResourceKind::Token,
            name,
            arguments,
            parameter_types: Vec::new(),
        })
    }

    fn parse_resource_target(
        &mut self,
        access: ResourceAccessMode,
    ) -> Result<ResourceClause, ClickError> {
        if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_ident() != Some("object")
            && self.peek_next() == Some(&Token::LParen)
        {
            return self.parse_declared_resource_call_with_access(access);
        }
        let segment = self.parse_current_contract_segment()?;
        Ok(match access {
            ResourceAccessMode::Own => ResourceClause::OwnMemory(segment),
            ResourceAccessMode::View => ResourceClause::ViewMemory(segment),
        })
    }

    fn parse_owned_resource_target(&mut self) -> Result<ResourceClause, ClickError> {
        let start = self.position;
        if let Ok(quantity) = self.parse_contract_expression()
            && self.peek_ident() == Some("of")
        {
            self.position += 1;
            let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
            return Ok(ResourceClause::Quantified {
                quantity,
                resource: Box::new(resource),
            });
        }
        self.position = start;
        self.parse_resource_target(ResourceAccessMode::Own)
    }

    fn parse_region_proof_items(&mut self) -> Result<Vec<StructuralItem>, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "invariant" => {
                let proposition = self.parse_proposition()?;
                if self.peek_ident() == Some("by") {
                    return Err(self.error(
                        "invariant proofs belong to the loop; use `initialize by ...` and `preserve by ...`",
                    ));
                }
                self.expect(Token::Semicolon)?;
                Ok(vec![StructuralItem {
                    kind: StructuralItemKind::Invariant,
                    claim: StructuralItemClaim::Proposition(proposition),
                    proof: SourceProof::Tactic(SmartTactic::Auto),
                }])
            }
            Some(Token::Ident(kind)) if kind == "immutable" || kind == "mutable" => {
                let effect = self.parse_effect_after_keyword(kind)?;
                let proof = self.parse_proof_clause_or_default()?;
                Ok(vec![StructuralItem {
                    kind: StructuralItemKind::Effect,
                    claim: StructuralItemClaim::Effect(effect),
                    proof,
                }])
            }
            Some(Token::Ident(kind)) if kind == "step" => {
                self.expect(Token::LBrace)?;
                let mut items = Vec::new();
                while self.peek() != Some(&Token::RBrace) {
                    let effect_kind = self.expect_ident("step effect")?;
                    if effect_kind != "immutable" && effect_kind != "mutable" {
                        return Err(self.error(format!(
                            "expected `immutable` or `mutable` inside `step`, got `{effect_kind}`"
                        )));
                    }
                    let effect = self.parse_effect_after_keyword(effect_kind)?;
                    let proof = self.parse_proof_clause_or_default()?;
                    items.push(StructuralItem {
                        kind: StructuralItemKind::StepEffect,
                        claim: StructuralItemClaim::Effect(effect),
                        proof,
                    });
                }
                self.expect(Token::RBrace)?;
                if items.is_empty() {
                    return Err(self.error("`step` block must contain at least one effect"));
                }
                Ok(items)
            }
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected `invariant`, `immutable`, `mutable`, or `step`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected `invariant`, `immutable`, `mutable`, or `step`, got {token:?}"
            ))),
            None => Err(self.error(
                "expected `invariant`, `immutable`, `mutable`, or `step`, got end of input",
            )),
        }
    }

    fn parse_effect_clause(&mut self) -> Result<EffectClause, ClickError> {
        let effect = match self.next() {
            Some(Token::Ident(kind)) if kind == "immutable" || kind == "mutable" => {
                self.parse_effect_after_keyword(kind)?
            }
            Some(Token::Ident(kind)) => {
                return Err(self.error(format!("expected `immutable` or `mutable`, got `{kind}`")));
            }
            Some(token) => {
                return Err(self.error(format!("expected `immutable` or `mutable`, got {token:?}")));
            }
            None => {
                return Err(self.error("expected `immutable` or `mutable`, got end of input"));
            }
        };
        let proof = self.parse_proof_clause_or_default()?;
        Ok(EffectClause { effect, proof })
    }

    fn parse_effect_after_keyword(&mut self, kind: String) -> Result<Effect, ClickError> {
        if kind == "immutable" {
            return Ok(Effect::Immutable);
        }

        let mut segments = vec![self.parse_contract_segment()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            segments.push(self.parse_contract_segment()?);
        }
        Ok(Effect::Mutable(segments))
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
        let proof = self.parse_proof_clause_or_default()?;

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
        if self.peek_ident() == Some("let") {
            let start = self.position;
            let binding = self.parse_contract_let_binding()?;
            let ContractLetBindingKind::Where(condition) = binding.kind else {
                self.position = start;
                return self.parse_proposition_comparison();
            };
            let Some(c_type) = binding.c_type else {
                unreachable!("`let ... where` parser requires an explicit type")
            };
            let body = self.parse_proposition()?;
            return Ok(ClickProposition::Exists {
                c_type,
                name: binding.name,
                body: Box::new(ClickProposition::And(Box::new(condition), Box::new(body))),
            });
        }

        if self.peek_ident() == Some("forall") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let name = self.expect_ident("forall variable name")?;
            if is_c_type_keyword(&name) {
                return Err(self.error(
                    "Click-native binders use `name: type`, for example `forall (k: int32)`",
                ));
            }
            self.expect(Token::Colon)?;
            let parsed_type = self.parse_type()?;
            if parsed_type.struct_name.is_some() && !parsed_type.struct_pointer {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            let c_type = parsed_type.c_type;
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

        if self.peek_ident() == Some("exists") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let name = self.expect_ident("exists variable name")?;
            if is_c_type_keyword(&name) {
                return Err(self.error(
                    "Click-native binders use `name: type`, for example `exists (k: int32)`",
                ));
            }
            self.expect(Token::Colon)?;
            let parsed_type = self.parse_type()?;
            if parsed_type.struct_name.is_some() && !parsed_type.struct_pointer {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            let c_type = parsed_type.c_type;
            self.expect(Token::RParen)?;
            self.expect(Token::LBrace)?;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            return Ok(ClickProposition::Exists {
                c_type,
                name,
                body: Box::new(body),
            });
        }

        if self.peek() == Some(&Token::LParen) && self.looks_like_range_proposition_method() {
            return self.parse_range_proposition_method();
        }

        if self.peek() == Some(&Token::LParen)
            && !self.parenthesized_atom_continues_as_contract_expression()
        {
            self.position += 1;
            let proposition = self.parse_proposition()?;
            self.expect(Token::RParen)?;
            return Ok(proposition);
        }

        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            let start = self.position;
            self.position += 2;
            let proposition_at_snapshot = self.parse_snapshot_selector().and_then(|selector| {
                self.expect(Token::Comma)?;
                let proposition = self.parse_proposition()?;
                self.expect(Token::RParen)?;
                Ok(ClickProposition::At {
                    selector,
                    proposition: Box::new(proposition),
                })
            });
            if proposition_at_snapshot.is_ok() {
                return proposition_at_snapshot;
            }
            self.position = start;
        }

        if self.peek_ident() == Some("separate") && self.peek_next() == Some(&Token::LParen) {
            let (left, right) = self.parse_resource_subject_pair("separate")?;
            return Ok(ClickProposition::Separate { left, right });
        }

        if self.peek_ident() == Some("contains") && self.peek_next() == Some(&Token::LParen) {
            let (parent, child) = self.parse_resource_subject_pair("contains")?;
            return Ok(ClickProposition::Contains { parent, child });
        }

        if self.peek_ident() == Some("loadable") && self.peek_next() == Some(&Token::LParen) {
            let segment = self.parse_loadable_segment()?;
            return Ok(ClickProposition::Loadable { segment });
        }

        if self.peek_ident() == Some("defined") && self.peek_next() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::LParen)?;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(ClickProposition::Defined { expression });
        }

        if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_ident() != Some("old")
            && self.peek_ident() != Some("at")
            && self.peek_ident() != Some("c")
            && !(self.peek_ident() == Some("count")
                && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_)))
                && self.tokens.get(self.position + 3) == Some(&Token::LParen))
            && !matches!(
                self.peek_ident(),
                Some("load_int32" | "load_uint8" | "load_int32_pointer" | "load_uint8_pointer")
            )
            && self.peek_next() == Some(&Token::LParen)
        {
            let start = self.position;
            let (name, arguments) = self.parse_call_arguments("predicate or function name")?;
            match self.peek() {
                Some(
                    Token::EqualEqual
                    | Token::BangEqual
                    | Token::LessThan
                    | Token::LessEqual
                    | Token::GreaterThan
                    | Token::GreaterEqual,
                ) => {
                    let operator = self.parse_comparison_operator("proposition")?;
                    let right = self.parse_contract_expression()?;
                    return Ok(ClickProposition::Comparison {
                        left: ContractExpression::Call { name, arguments },
                        operator,
                        right,
                    });
                }
                Some(
                    Token::Plus
                    | Token::Minus
                    | Token::Star
                    | Token::Slash
                    | Token::Percent
                    | Token::ShiftLeft
                    | Token::ShiftRight
                    | Token::Amp
                    | Token::Pipe
                    | Token::Caret
                    | Token::LBracket,
                ) => {
                    self.position = start;
                    return self.parse_proposition_comparison();
                }
                _ => return Ok(ClickProposition::PredicateCall { name, arguments }),
            }
        }

        self.parse_proposition_comparison()
    }

    fn parse_range_proposition_method(&mut self) -> Result<ClickProposition, ClickError> {
        self.expect(Token::LParen)?;
        let start = self.parse_contract_expression()?;
        self.expect(Token::DotDot)?;
        let end = self.parse_contract_expression()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Dot)?;
        let method = self.expect_ident("range proposition method")?;
        if method != "all" && method != "any" {
            return Err(self.error(format!(
                "unsupported range proposition method `{method}`; expected `all` or `any`"
            )));
        }

        self.expect(Token::LParen)?;
        self.expect(Token::Pipe)?;
        let item = self.expect_ident("range item name")?;
        self.expect(Token::Pipe)?;
        let body = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            body
        } else {
            self.parse_proposition()?
        };
        self.expect(Token::RParen)?;

        match method.as_str() {
            "all" => Ok(ClickProposition::RangeAll {
                start,
                end,
                item,
                body: Box::new(body),
            }),
            "any" => Ok(ClickProposition::RangeAny {
                start,
                end,
                item,
                body: Box::new(body),
            }),
            _ => unreachable!("range proposition method checked above"),
        }
    }

    fn parse_call_arguments(
        &mut self,
        expected_name: &str,
    ) -> Result<(String, Vec<ContractExpression>), ClickError> {
        let name = self.expect_ident(expected_name)?;
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                arguments.push(self.parse_contract_expression()?);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                    }
                    Some(Token::RParen) => break,
                    Some(token) => {
                        return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                    }
                    None => return Err(self.error("expected `,` or `)`, got end of input")),
                }
            }
        }
        self.expect(Token::RParen)?;
        Ok((name, arguments))
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

    fn parse_by_clause(&mut self) -> Result<SourceProof, ClickError> {
        self.expect_ident_spelling("by")?;
        if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let proof = match self.peek() {
                Some(Token::Ident(name))
                    if is_tactic_name(name) && self.peek_next() == Some(&Token::Semicolon) =>
                {
                    let tactic = self.parse_tactic()?;
                    self.expect(Token::RBrace)?;
                    SourceProof::Tactic(tactic)
                }
                Some(Token::RBrace) => {
                    return Err(self.error("`by` block must contain at least one tactic"));
                }
                Some(_) => {
                    let mut tactics = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        tactics.push(self.parse_proof_tactic()?);
                    }
                    self.expect(Token::RBrace)?;
                    SourceProof::Script(tactics)
                }
                None => return Err(self.error("expected tactic, got end of input")),
            };
            return Ok(proof);
        }

        Ok(SourceProof::Tactic(self.parse_tactic()?))
    }

    fn parse_proof_clause_or_default(&mut self) -> Result<SourceProof, ClickError> {
        if self.peek_ident() == Some("by") {
            self.parse_by_clause()
        } else {
            self.expect(Token::Semicolon)?;
            Ok(SourceProof::Default)
        }
    }

    fn parse_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let name = self.expect_ident("tactic")?;
        if let Some(replacement) = match name.as_str() {
            "conjunction" => Some("`conjunction()` was renamed to `split()`"),
            "apply_loop_summary" | "summarize" => Some(
                "detached loop summaries were removed; use a frontier-local `loop { ... }` tactic",
            ),
            "execute_rest" | "symbolic_execute" => Some("this tactic was renamed to `execute()`"),
            "execute_step" => Some("`execute_step()` was replaced by smart `step()`"),
            "execute_then_step" | "execute_else_step" => Some(
                "branch-specific execution tactics were removed; use smart `step()` or proof-level `if`",
            ),
            "bounded_execute" => Some(
                "`bounded_execute()` was removed; use `execute()` or `by auto;` and configure the tool budget",
            ),
            "calculate" => Some("use `simp() using { ... }` to constrain simplification"),
            "double_negation" => {
                Some("`double_negation()` was removed; use `intro(); contradiction(P);`")
            }
            "vacuous" => Some("`vacuous()` was removed; use `intro(); contradiction(antecedent);`"),
            _ => None,
        } {
            return Err(self.error(replacement));
        }
        if name == "have" {
            let proposition = self.parse_proposition()?;
            let proof = self.parse_by_clause()?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Have(ProofHave { proposition, proof }));
        }
        if name == "mark" {
            let mark = self.expect_ident("mark name")?;
            self.expect(Token::Semicolon)?;
            return Ok(ProofTactic::Mark(mark));
        }
        if name == "open" {
            self.expect(Token::LParen)?;
            let resource = self.parse_declared_resource_call()?;
            self.expect(Token::RParen)?;
            let tactics = self.parse_possibly_empty_tactic_block()?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Open(ProofOpen { resource, tactics }));
        }
        if name == "if" {
            let condition = self.parse_proposition()?;
            // A proof `if` branch may be empty: it contributes only its case
            // split, and every path goal is still owed at path end. Pure
            // case-split certificates expand to exactly this shape (owner
            // decision 2026-07-31).
            let then_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect_ident_spelling("else")?;
            let else_tactics = self.parse_possibly_empty_tactic_block()?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::If(ProofIf {
                condition,
                then_tactics,
                else_tactics,
            }));
        }
        if name == "cases" {
            self.expect(Token::LParen)?;
            let disjunction = self.parse_proposition()?;
            self.expect(Token::RParen)?;
            // Each branch proves the goal under exactly its assumed disjunct.
            // Both branches are always spelled; there is no implicit side.
            let left_tactics = self.parse_possibly_empty_tactic_block()?;
            let right_tactics = self.parse_possibly_empty_tactic_block()?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Cases(ProofCases {
                disjunction,
                left_tactics,
                right_tactics,
            }));
        }
        if name == "branch" {
            self.expect(Token::LBrace)?;
            let ensuring = if self.peek_ident() == Some("ensuring") {
                self.position += 1;
                self.expect(Token::LBrace)?;
                let mut assertions = Vec::new();
                while self.peek() != Some(&Token::RBrace) {
                    let kind = self.expect_ident("branch assertion kind")?;
                    let assertion = match kind.as_str() {
                        "fact" => ProofAssertion::Fact(self.parse_proposition()?),
                        "owns" => ProofAssertion::Resource(
                            self.parse_resource_target(ResourceAccessMode::Own)?,
                        ),
                        "views" => ProofAssertion::Resource(
                            self.parse_resource_target(ResourceAccessMode::View)?,
                        ),
                        _ => {
                            return Err(self.error(format!(
                                "expected branch assertion `fact`, `owns`, or `views`, got `{kind}`"
                            )));
                        }
                    };
                    self.expect(Token::Semicolon)?;
                    assertions.push(assertion);
                }
                if assertions.is_empty() {
                    return Err(self.error("`ensuring` block must contain at least one assertion"));
                }
                self.expect(Token::RBrace)?;
                Some(assertions)
            } else {
                None
            };
            self.expect_ident_spelling("then")?;
            let then_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect_ident_spelling("else")?;
            let else_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect(Token::RBrace)?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Branch(ProofBranch {
                ensuring,
                then_tactics,
                else_tactics,
            }));
        }
        if name == "loop" {
            let label = if self.peek_ident() == Some("as") {
                self.position += 1;
                Some(self.expect_ident("loop label")?)
            } else {
                None
            };
            self.expect(Token::LBrace)?;
            let mut items = Vec::new();
            let mut decreases = None;
            let mut initialize_proof = None;
            let mut preserve_proof = None;
            while self.peek() != Some(&Token::RBrace) {
                if self.peek_ident() == Some("decreases") {
                    self.position += 1;
                    if decreases.is_some() {
                        return Err(self.error("duplicate loop `decreases` clause"));
                    }
                    decreases = Some(self.parse_contract_expression()?);
                    self.expect(Token::Semicolon)?;
                    continue;
                }
                if self.peek_ident() == Some("initialize") {
                    self.position += 1;
                    if initialize_proof.is_some() {
                        return Err(self.error("duplicate `initialize` proof"));
                    }
                    initialize_proof = Some(self.parse_by_clause()?);
                    continue;
                }
                if self.peek_ident() == Some("preserve") {
                    self.position += 1;
                    if preserve_proof.is_some() {
                        return Err(self.error("duplicate `preserve` proof"));
                    }
                    preserve_proof = Some(self.parse_by_clause()?);
                    continue;
                }
                items.extend(self.parse_region_proof_items()?);
            }
            self.expect(Token::RBrace)?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            if items.is_empty() && decreases.is_none() {
                return Err(self
                    .error("`loop` block must contain at least one item or a `decreases` clause"));
            }
            return Ok(ProofTactic::Loop(StructuralClause {
                // The actual loop identity is bound from the execution
                // frontier during check.  This sentinel is never lowered.
                region: CodeRegion::Loop(usize::MAX),
                label,
                decreases,
                items,
                initialize_proof,
                preserve_proof,
            }));
        }
        let tactic = match name.as_str() {
            "step" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Step
            }
            "close_invariants" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::CloseInvariants
            }
            "execute" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::SmartExecute
            }
            "execute_until" => {
                self.expect(Token::LParen)?;
                let region_ref = self.parse_code_region_ref()?;
                self.expect(Token::RParen)?;
                ProofTactic::ExecuteUntil(region_ref)
            }
            "frame" => {
                self.expect(Token::LParen)?;
                let region_ref = if self.peek() == Some(&Token::RParen) {
                    None
                } else {
                    Some(self.parse_code_region_ref()?)
                };
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    ProofTactic::SmartFrame(region_ref)
                } else {
                    let premises = self.parse_exact_premises()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::FrameUsing {
                        region: region_ref,
                        premises,
                    });
                }
            }
            "unfold" => {
                self.expect(Token::LParen)?;
                let tactic = if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let (name, arguments) =
                        self.parse_call_arguments("function or resource name")?;
                    ProofTactic::UnfoldFunction(ClickFunctionApplication { name, arguments })
                } else {
                    let predicate = self.expect_ident("predicate name")?;
                    ProofTactic::UnfoldPredicate(predicate)
                };
                self.expect(Token::RParen)?;
                tactic
            }
            "apply" => {
                self.expect(Token::LParen)?;
                let application = self.parse_theorem_application()?;
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    ProofTactic::ApplyTheorem(application)
                } else {
                    let premises = self.parse_exact_premises()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::ApplyTheoremUsing {
                        application,
                        premises,
                    });
                }
            }
            "observe" => {
                self.expect(Token::LParen)?;
                let start = self.position;
                let resource = if let Ok(quantity) = self.parse_contract_expression()
                    && self.peek_ident() == Some("of")
                {
                    self.position += 1;
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
                    ResourceClause::Quantified {
                        quantity,
                        resource: Box::new(resource),
                    }
                } else {
                    self.position = start;
                    self.parse_declared_resource_call_with_access(ResourceAccessMode::View)?
                };
                self.expect(Token::RParen)?;
                ProofTactic::ObserveResource(resource)
            }
            "witness" => {
                self.expect(Token::LParen)?;
                let name = self.expect_ident("witness variable name")?;
                self.expect(Token::Equal)?;
                let value = self.parse_contract_expression()?;
                self.expect(Token::RParen)?;
                ProofTactic::Witness(ProofWitness { name, value })
            }
            "choose" => {
                self.expect(Token::LParen)?;
                let name = self.expect_ident("chosen variable name")?;
                self.expect_ident_spelling("from")?;
                let source = self.parse_proof_fact_source()?;
                self.expect(Token::RParen)?;
                ProofTactic::Choose(ProofChoice { name, source })
            }
            "assumption" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Assumption
            }
            "extract" => {
                self.expect(Token::LParen)?;
                let proposition = self.parse_proposition()?;
                self.expect(Token::RParen)?;
                ProofTactic::Extract(proposition)
            }
            "normalize" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Normalize
            }
            "arithmetic" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::ArithmeticUsing(premises));
                }
                ProofTactic::ArithmeticUsing(Vec::new())
            }
            "intro" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Intro
            }
            "split" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Split
            }
            "left" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Left
            }
            "right" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Right
            }
            "enumerate" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Enumerate
            }
            "contradiction" => {
                self.expect(Token::LParen)?;
                let proposition = self.parse_proposition()?;
                self.expect(Token::RParen)?;
                ProofTactic::Contradiction(proposition)
            }
            "rewrite" => {
                self.expect(Token::LParen)?;
                let equality = self.parse_proposition()?;
                self.expect(Token::RParen)?;
                ProofTactic::Rewrite(equality)
            }
            "transport" => {
                self.expect(Token::LParen)?;
                let source = self.parse_proposition()?;
                self.expect(Token::Comma)?;
                let target = self.parse_proposition()?;
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    ProofTactic::Transport { source, target }
                } else {
                    let premises = self.parse_exact_premises()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::TransportUsing {
                        source,
                        target,
                        premises,
                    });
                }
            }
            "instantiate" => {
                self.expect(Token::LParen)?;
                let quantified = self.parse_proposition()?;
                self.expect(Token::Comma)?;
                let argument = self.parse_contract_expression()?;
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    return Err(self.error(
                        "`instantiate` requires explicit evidence: `instantiate(F, value) using { ... }`",
                    ));
                }
                let premises = self.parse_exact_premises()?;
                if self.peek() == Some(&Token::Semicolon) {
                    self.position += 1;
                }
                return Ok(ProofTactic::InstantiateUsing {
                    quantified,
                    argument,
                    premises,
                });
            }
            "simp" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    if premises.is_empty() {
                        return Err(self.error(
                            "`simp() using` requires at least one explicit premise; use `simp()` for ambient simplification",
                        ));
                    }
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::SimpUsing(ProofSimpUsing { premises }));
                }
                ProofTactic::Simp
            }
            "fold" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_owned_resource_target()?;
                self.expect(Token::RParen)?;
                ProofTactic::FoldResource(resource)
            }
            "construct" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_owned_resource_target()?;
                self.expect(Token::RParen)?;
                ProofTactic::ConstructResource(resource)
            }
            "induct" => {
                self.expect(Token::LParen)?;
                let parameter = self.expect_ident("induction parameter")?;
                self.expect(Token::RParen)?;
                self.expect_ident_spelling("as")?;
                let hypothesis = self.expect_ident("induction hypothesis name")?;
                ProofTactic::Induct {
                    parameter,
                    hypothesis,
                }
            }
            _ if is_tactic_name(&name) => {
                return Err(self.error(format!(
                    "`{name}` is only available as a standalone smart tactic; use `by {name};`"
                )));
            }
            _ => return Err(self.error(format!("unknown tactic `{name}`"))),
        };
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    fn parse_possibly_empty_tactic_block(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        self.expect(Token::LBrace)?;
        let mut tactics = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            tactics.push(self.parse_proof_tactic()?);
        }
        self.expect(Token::RBrace)?;
        Ok(tactics)
    }

    fn parse_theorem_application(&mut self) -> Result<TheoremApplication, ClickError> {
        let (name, arguments) = self.parse_call_arguments("theorem name")?;
        Ok(TheoremApplication { name, arguments })
    }

    fn parse_declared_resource_call(&mut self) -> Result<ResourceClause, ClickError> {
        self.parse_declared_resource_call_with_access(ResourceAccessMode::Own)
    }

    fn parse_resource_count_pattern(&mut self) -> Result<ResourceClause, ClickError> {
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                if self.peek_ident() == Some("_") {
                    self.position += 1;
                    arguments.push(ContractExpression::ResourceWildcard);
                } else {
                    arguments.push(self.parse_contract_expression()?);
                }
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::RParen) => break,
                    Some(token) => {
                        return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                    }
                    None => return Err(self.error("expected `,` or `)`, got end of input")),
                }
            }
        }
        self.expect(Token::RParen)?;
        Ok(ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Token,
            name,
            arguments,
            parameter_types: Vec::new(),
        })
    }

    fn parse_declared_resource_call_with_access(
        &mut self,
        access: ResourceAccessMode,
    ) -> Result<ResourceClause, ClickError> {
        let (name, arguments) = self.parse_call_arguments("resource name")?;
        Ok(ResourceClause::Declared {
            access,
            kind: ResourceKind::Token,
            name,
            arguments,
            parameter_types: Vec::new(),
        })
    }

    fn expect_empty_tactic_args(&mut self, name: &str) -> Result<(), ClickError> {
        self.expect(Token::LParen)?;
        if self.peek() != Some(&Token::RParen) {
            return Err(self.error(format!("`{name}` expects no arguments")));
        }
        self.expect(Token::RParen)
    }

    fn parse_exact_premises(&mut self) -> Result<Vec<ClickProposition>, ClickError> {
        self.expect_ident_spelling("using")?;
        self.expect(Token::LBrace)?;
        let mut premises = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek_ident() == Some("fact") {
                return Err(self.error(
                    "`fact` is redundant in a tactic `using` block; list the proposition directly",
                ));
            }
            premises.push(self.parse_proposition()?);
            self.expect(Token::Semicolon)?;
        }
        self.expect(Token::RBrace)?;
        Ok(premises)
    }

    fn parse_proof_fact_source(&mut self) -> Result<ProofFactSource, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "requirement" => match self.next() {
                Some(Token::Number(index)) => {
                    let index = usize::try_from(index)
                        .map_err(|_| self.error("requirement index does not fit in usize"))?;
                    Ok(ProofFactSource::Requirement(index))
                }
                Some(Token::Ident(label)) => Ok(ProofFactSource::RequirementLabel(label)),
                Some(token) => Err(self.error(format!(
                    "expected requirement index or label, got {token:?}"
                ))),
                None => Err(self.error("expected requirement index or label, got end of input")),
            },
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected proof fact source `requirement N` or `requirement name`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected proof fact source `requirement N` or `requirement name`, got {token:?}"
            ))),
            None => Err(self.error("expected proof fact source `requirement N`, got end of input")),
        }
    }

    fn parse_code_region_ref(&mut self) -> Result<CodeRegionRef, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "function" => Ok(CodeRegionRef::Function),
            Some(Token::Ident(kind)) if kind == "loop" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("loop index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Loop(index))
            }
            Some(Token::Ident(kind)) if kind == "statement" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("statement index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Statement(index))
            }
            Some(Token::Ident(label)) => Ok(CodeRegionRef::Label(label)),
            Some(token) => Err(self.error(format!(
                "expected code region `function`, `loop(N)`, `statement(N)`, or label, got {token:?}"
            ))),
            None => Err(self.error(
                "expected code region `function`, `loop(N)`, `statement(N)`, or label, got end of input",
            )),
        }
    }

    fn parse_tactic(&mut self) -> Result<SmartTactic, ClickError> {
        let tactic = match self.next() {
            Some(Token::Ident(name)) if name == "auto" => SmartTactic::Auto,
            Some(Token::Ident(name)) if name == "frame" => SmartTactic::Frame,
            Some(Token::Ident(name)) if name == "simp" => SmartTactic::Simp,
            Some(Token::Ident(name)) => {
                return Err(self.error(format!("expected tactic, got `{name}`")));
            }
            Some(token) => {
                return Err(self.error(format!("expected tactic, got {token:?}")));
            }
            None => return Err(self.error("expected tactic, got end of input")),
        };
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    fn parse_ensure_expression(&mut self) -> Result<C0Expression, ClickError> {
        self.parse_ensure_bitwise_or()
    }

    fn parse_contract_expression(&mut self) -> Result<ContractExpression, ClickError> {
        self.parse_contract_bitwise_or()
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

    fn parse_loadable_segment(&mut self) -> Result<ContractSegment, ClickError> {
        self.expect_ident_spelling("loadable")?;
        self.expect(Token::LParen)?;
        let segment = self.parse_contract_segment()?;
        self.expect(Token::RParen)?;
        Ok(segment)
    }

    fn parse_current_contract_segment(&mut self) -> Result<ContractSegment, ClickError> {
        if self.peek_ident() == Some("object") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            let base = contract_expression_as_c_fragment(&expression).ok_or_else(|| {
                self.error("`object(...)` expects a current C struct pointer expression")
            })?;
            let CExpression::Variable(base_name) = &base else {
                return Err(self
                    .error("`object(...)` currently expects a named C struct pointer parameter"));
            };
            let struct_name = self.current_struct_params.get(base_name).ok_or_else(|| {
                self.error(format!(
                    "`object({base_name})` requires `{base_name}` to be a C struct pointer"
                ))
            })?;
            let layout = self.struct_layouts.get(struct_name).ok_or_else(|| {
                self.error(format!(
                    "`object({base_name})` has no imported layout for `struct {struct_name}`"
                ))
            })?;
            if layout.size_bytes() % 4 != 0 {
                return Err(self.error(format!(
                    "`object({base_name})` cannot represent the {}-byte `struct {struct_name}` as an int32-aligned memory segment",
                    layout.size_bytes()
                )));
            }
            return Ok(ContractSegment {
                state: ContractSegmentState::Current,
                base,
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(layout.size_bytes() / 4)),
                surface: ContractSegmentSurface::Object(struct_name.clone()),
            });
        }
        let (mut surface_base, mut base) = if matches!(
            self.peek_ident(),
            Some("load_int32" | "load_uint8" | "load_int32_pointer" | "load_uint8_pointer")
        ) && self.peek_next() == Some(&Token::LParen)
        {
            let expression = self.parse_contract_primary()?;
            let base = contract_expression_as_c_fragment(&expression).ok_or_else(|| {
                self.error("memory segment base must be a current C pointer expression")
            })?;
            (expression, base)
        } else if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            let base = contract_expression_as_c_fragment(&expression).ok_or_else(|| {
                self.error("memory segment base must be a current C pointer expression")
            })?;
            (expression, base)
        } else {
            let expression = self.parse_ensure_primary()?;
            let base = expression.to_kernel_expression();
            (ContractExpression::CFragment(base.clone()), base)
        };
        let mut struct_name = match &surface_base {
            ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.current_struct_params.get(name).cloned()
            }
            _ => None,
        };
        while self.peek() == Some(&Token::Arrow) {
            self.position += 1;
            let field_name = self.expect_ident("field name")?;
            if !matches!(self.peek(), Some(Token::Arrow | Token::LBracket)) {
                if let Some(base_struct_name) = &struct_name
                    && self.struct_layouts.contains_key(base_struct_name)
                {
                    let field =
                        self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                    self.validate_field_place(&field)?;
                    return Ok(Self::field_segment_from_metadata(base, &field_name, &field));
                }
                return self.resolve_field_segment(base, &field_name);
            }
            let (lowered, next_struct_name) = if let Some(base_struct_name) = &struct_name
                && self.struct_layouts.contains_key(base_struct_name)
            {
                let field = self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                let pointer = self.offset_field_pointer(base, field.offset_bytes);
                (
                    CExpression::TypedLoad {
                        pointer: Box::new(pointer),
                        value_type: field.c_type.to_kernel_type(),
                    },
                    field.struct_name,
                )
            } else {
                (self.resolve_field_load(base, &field_name)?, None)
            };
            surface_base = ContractExpression::Field {
                base: Box::new(surface_base),
                field: field_name,
                lowered: lowered.clone(),
            };
            base = lowered;
            struct_name = next_struct_name;
        }
        self.expect(Token::LBracket)?;
        let start_expression = self.parse_contract_expression()?;
        let start = contract_expression_as_c_fragment(&start_expression)
            .ok_or_else(|| self.error("memory segment start must be a current C expression"))?;
        self.expect(Token::DotDot)?;
        let end_expression = self.parse_contract_expression()?;
        let end = contract_expression_as_c_fragment(&end_expression)
            .ok_or_else(|| self.error("memory segment end must be a current C expression"))?;
        self.expect(Token::RBracket)?;
        Ok(ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start,
            end,
            surface: ContractSegmentSurface::Range {
                base: surface_base,
                start: start_expression,
                end: end_expression,
            },
        })
    }

    fn resolve_field_segment(
        &self,
        base: CExpression,
        field_name: &str,
    ) -> Result<ContractSegment, ClickError> {
        let Some(field) = self.resolve_field_metadata(&base, field_name)? else {
            return Ok(ContractSegment {
                state: ContractSegmentState::Current,
                base,
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Field(field_name.to_string()),
            });
        };
        self.validate_field_place(&field)?;
        Ok(Self::field_segment_from_metadata(base, field_name, &field))
    }

    fn field_segment_from_metadata(
        base: CExpression,
        field_name: &str,
        field: &ResolvedField,
    ) -> ContractSegment {
        if let C0Type::Int32Array(_) | C0Type::UInt8Array(_) = field.c_type {
            let element_width = match field.c_type {
                C0Type::Int32Array(_) => 4,
                C0Type::UInt8Array(_) => 1,
                _ => unreachable!("validated inline array field"),
            };
            let field_base = crate::kernel::c_pointer_offset_bytes(base, field.offset_bytes);
            return ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::TypedLoad {
                    pointer: Box::new(field_base),
                    value_type: field.c_type.to_kernel_type(),
                },
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(
                    (field.slot_end_bytes - field.offset_bytes) / element_width,
                )),
                surface: ContractSegmentSurface::Field(field_name.to_string()),
            };
        }
        ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start: CExpression::Value(int32(field.offset_bytes / 4)),
            end: CExpression::Value(int32(field.slot_end_bytes / 4)),
            surface: ContractSegmentSurface::Field(field_name.to_string()),
        }
    }

    fn resolve_field_load(
        &self,
        base: CExpression,
        field_name: &str,
    ) -> Result<CExpression, ClickError> {
        let Some(field) = self.resolve_field_metadata(&base, field_name)? else {
            return Ok(CExpression::Load(Box::new(base)));
        };
        Ok(CExpression::TypedLoad {
            pointer: Box::new(self.offset_field_pointer(base, field.offset_bytes)),
            value_type: field.c_type.to_kernel_type(),
        })
    }

    fn resolve_c0_field_load(
        &self,
        base: C0Expression,
        field_name: &str,
    ) -> Result<Option<C0Expression>, ClickError> {
        let struct_name = match &base {
            C0Expression::Variable(base_name) => self.current_struct_params.get(base_name),
            C0Expression::Field {
                field_struct_name, ..
            } => field_struct_name.as_ref(),
            _ => None,
        };
        let Some(struct_name) = struct_name else {
            return Ok(None);
        };
        let field = self.resolve_struct_field_metadata(struct_name, field_name)?;
        Ok(Some(C0Expression::Field {
            pointer: Box::new(self.offset_c0_field_pointer(base, field.offset_bytes)),
            field_type: field.c_type,
            field_struct_name: field.struct_name,
        }))
    }

    fn resolve_field_metadata(
        &self,
        base: &CExpression,
        field_name: &str,
    ) -> Result<Option<ResolvedField>, ClickError> {
        let CExpression::Variable(base_name) = base else {
            return Ok(None);
        };
        let Some(struct_name) = self.current_struct_params.get(base_name) else {
            return Ok(None);
        };
        if !self.struct_layouts.contains_key(struct_name) {
            return Ok(None);
        }
        self.resolve_struct_field_metadata(struct_name, field_name)
            .map(Some)
    }

    fn resolve_struct_field_metadata(
        &self,
        struct_name: &str,
        field_name: &str,
    ) -> Result<ResolvedField, ClickError> {
        let Some(layout) = self.struct_layouts.get(struct_name) else {
            return Err(self.error(format!("unknown struct declaration `{struct_name}`")));
        };
        let Some(field) = layout.field(field_name) else {
            return Err(self.error(format!(
                "struct `{struct_name}` has no field `{field_name}`"
            )));
        };
        // A field's resource slot runs to the next field's offset (or the
        // struct's end), so ownership covers trailing alignment padding:
        // padding belongs to the object and no one else can own it.
        let slot_end_bytes = layout
            .fields()
            .values()
            .map(syntax::C0StructField::offset_bytes)
            .filter(|offset| *offset > field.offset_bytes())
            .min()
            .unwrap_or_else(|| layout.size_bytes());
        Ok(ResolvedField {
            c_type: field.c_type(),
            struct_name: field.struct_name().map(str::to_string),
            offset_bytes: field.offset_bytes(),
            byte_width: field.byte_width(),
            slot_end_bytes,
        })
    }

    fn validate_field_place(&self, field: &ResolvedField) -> Result<(), ClickError> {
        if matches!(field.c_type, C0Type::Int32Array(_) | C0Type::UInt8Array(_)) {
            if field.slot_end_bytes < field.offset_bytes
                || (matches!(field.c_type, C0Type::Int32Array(_))
                    && (field.slot_end_bytes - field.offset_bytes) % 4 != 0)
            {
                return Err(self.error("inline array field has an invalid resource extent"));
            }
            return Ok(());
        }
        if field.offset_bytes % 4 != 0 || field.byte_width % 4 != 0 || field.slot_end_bytes % 4 != 0
        {
            return Err(
                self.error("field places currently require int32-aligned offsets and widths")
            );
        }
        Ok(())
    }

    fn offset_field_pointer(&self, base: CExpression, offset_bytes: u32) -> CExpression {
        crate::kernel::c_pointer_offset_bytes(base, offset_bytes)
    }

    fn offset_c0_field_pointer(&self, base: C0Expression, offset_bytes: u32) -> C0Expression {
        if offset_bytes == 0 {
            base
        } else {
            C0Expression::PointerOffsetBytes {
                pointer: Box::new(base),
                bytes: offset_bytes,
            }
        }
    }

    fn parse_contract_bitwise_or(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_contract_bitwise_xor()?;
            expression = ContractExpression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_bitwise_xor(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_contract_bitwise_and()?;
            expression = ContractExpression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_bitwise_and(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_shift()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_contract_shift()?;
            expression = ContractExpression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_shift(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_contract_add()?;
                    ContractExpression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_contract_add()?;
                    ContractExpression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_contract_add(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_contract_multiply()?;
                    ContractExpression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_contract_multiply()?;
                    ContractExpression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_contract_multiply(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_unary()?;
        loop {
            let Some(operator) = self.peek() else {
                break;
            };
            let constructor = match operator {
                Token::Star => ContractExpression::Multiply,
                Token::Slash => ContractExpression::Divide,
                Token::Percent => ContractExpression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_contract_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_unary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.peek() == Some(&Token::Minus) {
            if let Some(Token::Number(value)) = self.peek_next().cloned()
                && value <= i32::MAX as u32 + 1
            {
                self.position += 2;
                return Ok(ContractExpression::CFragment(CExpression::Value(int32(
                    0u32.wrapping_sub(value),
                ))));
            }
            self.position += 1;
            return Ok(ContractExpression::Subtract(
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(0)))),
                Box::new(self.parse_contract_unary()?),
            ));
        }
        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(ContractExpression::BitwiseNot(Box::new(
                self.parse_contract_unary()?,
            )));
        }
        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            let pointer = self.parse_contract_unary()?;
            let Some(pointer) = contract_expression_as_c_fragment(&pointer) else {
                return Err(
                    self.error("pointer dereference is only supported on current C fragments")
                );
            };
            return Ok(ContractExpression::CFragment(CExpression::Load(Box::new(
                pointer,
            ))));
        }

        self.parse_contract_postfix()
    }

    fn parse_contract_postfix(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_primary()?;
        let mut struct_name = match &expression {
            ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.current_struct_params.get(name).cloned()
            }
            _ => None,
        };
        let mut struct_array = match &expression {
            ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.current_struct_array_params.contains(name)
            }
            _ => false,
        };
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_contract_expression()?;
                    self.expect(Token::RBracket)?;
                    if struct_array
                        && let Some(base_struct_name) = &struct_name
                        && let Some(layout) = self.struct_layouts.get(base_struct_name)
                    {
                        let base = contract_expression_as_c_fragment(&expression)
                            .ok_or_else(|| {
                                self.error(
                                    "struct array indexing is only supported on current C fragments",
                                )
                            })?;
                        let index = contract_expression_as_c_fragment(&index).ok_or_else(|| {
                            self.error("struct array indices must be current C expressions")
                        })?;
                        let stride = CExpression::Multiply(
                            Box::new(index),
                            Box::new(CExpression::Value(int32(layout.size_bytes()))),
                        );
                        expression = ContractExpression::CFragment(CExpression::Add(
                            Box::new(base),
                            Box::new(stride),
                        ));
                        struct_array = false;
                    } else {
                        expression =
                            ContractExpression::Index(Box::new(expression), Box::new(index));
                        struct_name = None;
                        struct_array = false;
                    }
                }
                Some(Token::Arrow | Token::Dot) => {
                    self.position += 1;
                    let field_name = self.expect_ident("field name")?;
                    let surface_base = expression.clone();
                    let Some(base) = contract_expression_as_c_fragment(&expression) else {
                        return Err(
                            self.error("field access is only supported on current C fragments")
                        );
                    };
                    if let Some(base_struct_name) = &struct_name
                        && self.struct_layouts.contains_key(base_struct_name)
                    {
                        let field =
                            self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                        let pointer = self.offset_field_pointer(base, field.offset_bytes);
                        struct_name = field.struct_name;
                        struct_array = false;
                        expression = ContractExpression::Field {
                            base: Box::new(surface_base),
                            field: field_name,
                            lowered: CExpression::TypedLoad {
                                pointer: Box::new(pointer),
                                value_type: field.c_type.to_kernel_type(),
                            },
                        };
                    } else {
                        expression = ContractExpression::Field {
                            base: Box::new(surface_base),
                            field: field_name.clone(),
                            lowered: self.resolve_field_load(base, &field_name)?,
                        };
                    }
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_contract_primary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.peek_ident() == Some("sizeof") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let bytes = if self.peek_ident() == Some("struct") {
                self.position += 1;
                let name = self.expect_ident("struct name")?;
                self.expect(Token::RParen)?;
                self.struct_layouts
                    .get(&name)
                    .ok_or_else(|| self.error(format!("unknown struct declaration `{name}`")))?
                    .size_bytes()
            } else {
                let parsed_type = self.parse_type()?;
                self.expect(Token::RParen)?;
                if parsed_type.c_type == C0Type::Void {
                    return Err(self.error("`sizeof(void)` is not supported"));
                }
                parsed_type.c_type.abi_size_bytes()
            };
            return Ok(ContractExpression::CFragment(CExpression::Value(int32(
                bytes,
            ))));
        }
        if self.peek_ident() == Some("let") {
            let binding = self.parse_contract_let_binding()?;
            let ContractLetBindingKind::Value(value) = binding.kind else {
                return Err(
                    self.error("`let ... where` is a proposition binding, not an expression")
                );
            };
            let body = self.parse_contract_expression()?;
            return Ok(ContractExpression::Let {
                name: binding.name,
                c_type: binding.c_type,
                value: Box::new(value),
                body: Box::new(body),
            });
        }

        if self.peek_ident() == Some("if") {
            self.position += 1;
            let condition = self.parse_proposition()?;
            self.expect(Token::LBrace)?;
            let then_branch = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            if self.peek_ident() != Some("else") {
                return Err(self.error("expected `else` in `if` expression"));
            }
            self.position += 1;
            self.expect(Token::LBrace)?;
            let else_branch = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            return Ok(ContractExpression::If {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            });
        }

        if self.peek_ident() == Some("old") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::Old(Box::new(expression)));
        }

        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let selector = self.parse_snapshot_selector()?;
            self.expect(Token::Comma)?;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::At {
                selector,
                expression: Box::new(expression),
            });
        }

        if self.peek_ident() == Some("c") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let name = self.expect_ident("C binding name")?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::CBinding(name));
        }

        if self.peek_ident() == Some("byte_offset") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let pointer = self.parse_contract_expression()?;
            let Some(pointer) = contract_expression_as_c_fragment(&pointer) else {
                return Err(self.error("byte offset expects a current C pointer expression"));
            };
            self.expect(Token::Comma)?;
            let bytes = match self.next() {
                Some(Token::Number(bytes)) => bytes,
                Some(token) => {
                    return Err(self.error(format!(
                        "byte offset expects a nonnegative byte count, got {token:?}"
                    )));
                }
                None => {
                    return Err(self
                        .error("byte offset expects a nonnegative byte count, got end of input"));
                }
            };
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::CFragment(
                CExpression::PointerOffsetBytes {
                    pointer: Box::new(pointer),
                    bytes,
                },
            ));
        }

        let typed_load = match self.peek_ident() {
            Some("load_int32") => Some(CType::Int32),
            Some("load_uint8") => Some(CType::UInt8),
            Some("load_int32_pointer") => Some(CType::Int32Pointer),
            Some("load_uint8_pointer") => Some(CType::UInt8Pointer),
            Some("load_int32_pointer_pointer") => Some(CType::Int32PointerPointer),
            Some("load_uint8_pointer_pointer") => Some(CType::UInt8PointerPointer),
            _ => None,
        };
        if self.peek_next() == Some(&Token::LParen)
            && let Some(value_type) = typed_load
        {
            self.position += 2;
            let pointer = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            let Some(pointer) = contract_expression_as_c_fragment(&pointer) else {
                return Err(self.error("typed load expects a current C pointer expression"));
            };
            return Ok(ContractExpression::CFragment(CExpression::TypedLoad {
                pointer: Box::new(pointer),
                value_type,
            }));
        }

        // `count(resource(args))` is the declared-resource population operator.
        // Keep the existing pure `count(array, lo, hi, value)` function
        // unambiguous by recognizing the operator only when its first token is
        // itself visibly a resource call.
        if self.peek_ident() == Some("count")
            && self.peek_next() == Some(&Token::LParen)
            && self.looks_like_resource_count()
        {
            self.position += 2;
            let resource = self.parse_resource_count_pattern()?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::ResourceCount(Box::new(resource)));
        }

        if matches!(self.peek(), Some(Token::Ident(_))) && self.peek_next() == Some(&Token::LParen)
        {
            let (name, arguments) = self.parse_call_arguments("function name")?;
            return Ok(ContractExpression::Call { name, arguments });
        }

        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected contract expression, got `by`"))
            }
            Some(Token::Ident(name)) => {
                Ok(ContractExpression::CFragment(CExpression::Variable(name)))
            }
            Some(Token::Number(value)) => Ok(ContractExpression::CFragment(CExpression::Value(
                CValue::Int32(Bitvector32Term::Constant(value)),
            ))),
            Some(Token::UInt8Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt8(Bitvector32Term::Constant(u32::from(value)))),
            )),
            Some(Token::CharLiteral(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt8(Bitvector32Term::Constant(u32::from(value)))),
            )),
            Some(Token::LParen) => {
                let expression = self.parse_contract_expression()?;
                if self.peek() == Some(&Token::DotDot) {
                    self.position += 1;
                    let end = self.parse_contract_expression()?;
                    self.expect(Token::RParen)?;
                    return self.parse_range_fold(expression, end);
                }
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected contract expression, got {token:?}"))),
            None => Err(self.error("expected contract expression, got end of input")),
        }
    }

    fn parse_snapshot_selector(&mut self) -> Result<SnapshotSelector, ClickError> {
        if let (Some(Token::Ident(name)), Some(Token::Comma)) = (self.peek(), self.peek_next()) {
            let name = name.clone();
            self.position += 1;
            return Ok(SnapshotSelector::Mark(name));
        }
        Ok(SnapshotSelector::ProgramPoint(
            self.parse_program_point_ref()?,
        ))
    }

    fn parse_program_point_ref(&mut self) -> Result<ProgramPointRef, ClickError> {
        let region = self.parse_code_region_ref()?;
        self.expect(Token::Dot)?;
        let kind = match self.expect_ident("program point kind")?.as_str() {
            "entry" => ProgramPointKind::Entry,
            "exit" => ProgramPointKind::Exit,
            kind => {
                return Err(self.error(format!(
                    "expected program point kind `entry` or `exit`, got `{kind}`"
                )));
            }
        };
        Ok(ProgramPointRef { region, kind })
    }

    fn parse_range_fold(
        &mut self,
        start: ContractExpression,
        end: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        self.expect(Token::Dot)?;
        let method = self.expect_ident("range method")?;
        if method != "fold" {
            return Err(self.error(format!(
                "unsupported range method `{method}`; expected `fold`"
            )));
        }

        self.expect(Token::LParen)?;
        let initial = self.parse_contract_expression()?;
        self.expect(Token::Comma)?;
        self.expect(Token::Pipe)?;
        let accumulator = self.expect_ident("fold accumulator name")?;
        self.expect(Token::Comma)?;
        let item = self.expect_ident("fold item name")?;
        self.expect(Token::Pipe)?;
        let body = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let body = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            body
        } else {
            self.parse_contract_expression()?
        };
        self.expect(Token::RParen)?;

        Ok(ContractExpression::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        })
    }

    fn parse_ensure_bitwise_or(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_ensure_bitwise_xor()?;
            expression = C0Expression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_xor(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_ensure_bitwise_and()?;
            expression = C0Expression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_and(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_shift()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_ensure_shift()?;
            expression = C0Expression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_shift(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    C0Expression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    C0Expression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_add(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    C0Expression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    C0Expression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_multiply(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_unary()?;
        loop {
            let Some(operator) = self.peek() else {
                break;
            };
            let constructor = match operator {
                Token::Star => C0Expression::Multiply,
                Token::Slash => C0Expression::Divide,
                Token::Percent => C0Expression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_ensure_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_unary(&mut self) -> Result<C0Expression, ClickError> {
        if self.peek() == Some(&Token::Minus) {
            if let Some(Token::Number(value)) = self.peek_next().cloned()
                && value <= i32::MAX as u32 + 1
            {
                self.position += 2;
                return Ok(C0Expression::Int32Literal(0u32.wrapping_sub(value)));
            }
            self.position += 1;
            return Ok(C0Expression::Subtract(
                Box::new(C0Expression::Int32Literal(0)),
                Box::new(self.parse_ensure_unary()?),
            ));
        }
        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(C0Expression::BitwiseNot(Box::new(
                self.parse_ensure_unary()?,
            )));
        }

        self.parse_ensure_postfix()
    }

    fn parse_ensure_postfix(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_primary()?;
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_ensure_expression()?;
                    self.expect(Token::RBracket)?;
                    expression = C0Expression::Index(Box::new(expression), Box::new(index));
                }
                Some(Token::Arrow) => {
                    self.position += 1;
                    let field_name = self.expect_ident("field name")?;
                    let base = expression;
                    expression = self
                        .resolve_c0_field_load(base.clone(), &field_name)?
                        .unwrap_or_else(|| C0Expression::Load(Box::new(base)));
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_ensure_primary(&mut self) -> Result<C0Expression, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected result expression, got `by`"))
            }
            Some(Token::Ident(name)) => Ok(C0Expression::Variable(name)),
            Some(Token::Number(value)) => Ok(C0Expression::Int32Literal(value)),
            Some(Token::UInt8Number(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::CharLiteral(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::LParen) => {
                let expression = self.parse_ensure_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected result expression, got {token:?}"))),
            None => Err(self.error("expected result expression, got end of input")),
        }
    }

    fn expect_ident(&mut self, expected: &str) -> Result<String, ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => {
                Err(self.error_at(at, format!("expected {expected}, got {}", token.describe())))
            }
            None => Err(self.error_at(at, format!("expected {expected}, got end of input"))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) if name == expected => Ok(()),
            Some(token) => Err(self.error_at(
                at,
                format!("expected `{expected}`, got {}", token.describe()),
            )),
            None => Err(self.error_at(at, format!("expected `{expected}`, got end of input"))),
        }
    }

    fn expect_number(&mut self, expected: &str) -> Result<u32, ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Number(value)) => Ok(value),
            Some(token) => {
                Err(self.error_at(at, format!("expected {expected}, got {}", token.describe())))
            }
            None => Err(self.error_at(at, format!("expected {expected}, got end of input"))),
        }
    }

    fn expect_index(&mut self, expected: &str) -> Result<usize, ClickError> {
        usize::try_from(self.expect_number(expected)?)
            .map_err(|_| self.error(format!("{expected} does not fit in usize")))
    }

    fn expect_string(&mut self, expected: &str) -> Result<String, ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::String(value)) => Ok(value),
            Some(token) => {
                Err(self.error_at(at, format!("expected {expected}, got {}", token.describe())))
            }
            None => Err(self.error_at(at, format!("expected {expected}, got end of input"))),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(self.error_at(
                at,
                format!("expected {}, got {}", expected.describe(), token.describe()),
            )),
            None => Err(self.error_at(
                at,
                format!("expected {}, got end of input", expected.describe()),
            )),
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned()?;
        crate::instrumentation::record_deterministic_work(1);
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

    fn looks_like_resource_count(&self) -> bool {
        if !matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_)))
            || self.tokens.get(self.position + 3) != Some(&Token::LParen)
        {
            return false;
        }
        let mut depth = 0usize;
        for index in (self.position + 3)..self.tokens.len() {
            match self.tokens.get(index) {
                Some(Token::LParen) => depth += 1,
                Some(Token::RParen) => {
                    depth -= 1;
                    if depth == 0 {
                        return self.tokens.get(index + 1) == Some(&Token::RParen);
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn looks_like_range_proposition_method(&self) -> bool {
        let Some(close) = self
            .matching_parentheses
            .get(self.position)
            .copied()
            .flatten()
        else {
            return false;
        };
        self.tokens.get(close + 1) == Some(&Token::Dot)
            && matches!(
                self.tokens.get(close + 2),
                Some(Token::Ident(method)) if matches!(method.as_str(), "all" | "any")
            )
    }

    fn parenthesized_atom_continues_as_contract_expression(&self) -> bool {
        let Some(close) = self
            .matching_parentheses
            .get(self.position)
            .copied()
            .flatten()
        else {
            return false;
        };
        matches!(
            self.tokens.get(close + 1),
            Some(
                Token::EqualEqual
                    | Token::BangEqual
                    | Token::LessThan
                    | Token::LessEqual
                    | Token::GreaterThan
                    | Token::GreaterEqual
                    | Token::Plus
                    | Token::Minus
                    | Token::Star
                    | Token::Slash
                    | Token::Percent
                    | Token::ShiftLeft
                    | Token::ShiftRight
                    | Token::Amp
                    | Token::Pipe
                    | Token::Caret
                    | Token::LBracket
                    | Token::Arrow
                    | Token::Dot
            )
        )
    }

    /// The source position of the next unconsumed token, or of the last
    /// token when every token has been consumed.
    fn here(&self) -> Option<SourcePosition> {
        self.positions
            .get(self.position)
            .or_else(|| self.positions.last())
            .copied()
    }

    /// Captures the position of the next unconsumed token so an error can
    /// still point at it after the token is consumed.
    fn error_context(&self) -> Option<SourcePosition> {
        self.here()
    }

    fn error_at(&self, at: Option<SourcePosition>, message: impl Into<String>) -> ClickError {
        match at {
            Some(position) => ClickError::new(format!("{position}: {}", message.into())),
            None => ClickError::new(message),
        }
    }

    fn error(&self, message: impl Into<String>) -> ClickError {
        self.error_at(self.here(), message)
    }
}

fn validate_parenthesis_nesting(
    tokens: &[Token],
    positions: &[SourcePosition],
) -> Result<Vec<Option<usize>>, ClickError> {
    let mut openings = Vec::new();
    let mut matching = vec![None; tokens.len()];
    for (index, token) in tokens.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        match token {
            Token::LParen => {
                openings.push(index);
                if openings.len() > PARENTHESIS_NESTING_LIMIT {
                    let message = format!(
                        "parenthesis nesting exceeds Click's supported depth of {PARENTHESIS_NESTING_LIMIT}"
                    );
                    return Err(match positions.get(index) {
                        Some(position) => ClickError::new(format!("{position}: {message}")),
                        None => ClickError::new(message),
                    });
                }
            }
            Token::RParen => {
                if let Some(open) = openings.pop() {
                    matching[open] = Some(index);
                    matching[index] = Some(open);
                }
            }
            _ => {}
        }
    }
    Ok(matching)
}
