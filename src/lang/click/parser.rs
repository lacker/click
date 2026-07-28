use super::*;

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

struct Parser {
    tokens: Vec<Token>,
    position: usize,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    current_struct_params: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedParameter {
    parameter: FunctionParameter,
    struct_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedParameters {
    parameters: Vec<FunctionParameter>,
    struct_params: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedField {
    c_type: C0Type,
    struct_name: Option<String>,
    offset_bytes: u32,
    byte_width: u32,
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
        Ok(Self {
            tokens: tokenize(source)?,
            position: 0,
            struct_layouts,
            current_struct_params: BTreeMap::new(),
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
            } else if self.peek_ident() == Some("resource") {
                resource_definitions.push(self.parse_resource_definition()?);
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
        let parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let body = self.parse_proposition()?;
        self.current_struct_params = previous_struct_params;
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
        let parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Arrow)?;
        let return_type = self.parse_type()?.c_type;
        self.expect(Token::LBrace)?;
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let body = self.parse_contract_expression()?;
        self.current_struct_params = previous_struct_params;
        self.expect(Token::RBrace)?;
        Ok(ClickFunctionDefinition {
            name,
            parameters: parsed_parameters.parameters,
            return_type,
            body,
        })
    }

    fn parse_resource_definition(&mut self) -> Result<ResourceDefinition, ClickError> {
        self.expect_ident_spelling("resource")?;
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_resource_parameters()?;
        self.expect(Token::RParen)?;
        let previous_struct_params = std::mem::replace(
            &mut self.current_struct_params,
            parsed_parameters.struct_params,
        );
        let composite_body = match self.peek() {
            Some(Token::Semicolon) => {
                self.position += 1;
                None
            }
            Some(Token::LBrace) => Some(self.parse_composite_resource_body()?),
            Some(token) => {
                return Err(self.error(format!(
                    "expected `;` or composite resource body, got {token:?}"
                )));
            }
            None => {
                return Err(self.error("expected `;` or composite resource body, got end of input"));
            }
        };
        self.current_struct_params = previous_struct_params;
        Ok(ResourceDefinition {
            name,
            parameters: parsed_parameters.parameters,
            composite_body,
        })
    }

    fn parse_composite_resource_body(&mut self) -> Result<CompositeResourceBody, ClickError> {
        self.expect(Token::LBrace)?;
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
        Ok(CompositeResourceBody { contains, facts })
    }

    fn parse_composite_resource_contains_clause(&mut self) -> Result<ResourceClause, ClickError> {
        if matches!(self.peek_ident(), Some("read" | "write")) {
            return self.parse_resource_clause();
        }
        self.parse_declared_resource_call()
    }

    fn parse_resource_parameters(&mut self) -> Result<ParsedParameters, ClickError> {
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(ParsedParameters {
                parameters,
                struct_params,
            });
        }

        loop {
            let name = self.expect_ident("resource parameter name")?;
            self.expect(Token::Colon)?;
            let parsed_type = self.parse_type()?;
            let parsed_parameter = self.parse_parameter_array_suffix(name, parsed_type)?;
            if let Some(struct_name) = parsed_parameter.struct_name {
                struct_params.insert(parsed_parameter.parameter.name.clone(), struct_name);
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
        let parsed_parameters = self.parse_resource_parameters()?;
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
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
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
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
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
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
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

        Ok(TheoremDefinition {
            name,
            parameters: parsed_parameters.parameters,
            requires,
            ensures,
        })
    }

    fn parse_function_block(&mut self) -> Result<FunctionBlock, ClickError> {
        let (signature, struct_params) = self.parse_function_signature()?;
        self.expect(Token::LBrace)?;

        let parameter_names = signature
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<BTreeSet<_>>();
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut structural_clauses = Vec::new();
        let mut structural_labels = BTreeSet::new();
        let mut effects = Vec::new();
        let mut ensures = Vec::new();
        let previous_struct_params =
            std::mem::replace(&mut self.current_struct_params, struct_params);
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
                Some("owns") => {
                    self.position += 1;
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
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
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
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
                    let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
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
                Some("for") => {
                    let clause = self.parse_region_proof_clause()?;
                    if let Some(label) = clause.label() {
                        if matches!(label, "function" | "loop" | "statement") {
                            return Err(self.error(format!(
                                "`{label}` is reserved and cannot be used as a code region label"
                            )));
                        }
                        if !structural_labels.insert(label.to_string()) {
                            return Err(self.error(format!(
                                "duplicate code region label `{label}` in `{}`",
                                signature.name()
                            )));
                        }
                    }
                    structural_clauses.push(
                        apply_contract_lets_to_structural_clause(clause, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("immutable" | "mutable" | "mutable_field") => {
                    let effect = self.parse_effect_clause()?;
                    effects.push(
                        apply_contract_lets_to_effect_clause(effect, &contract_lets)
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
                        "expected `let`, `requires`, `owns`, `views`, `consumes`, `produces`, `immutable`, `mutable`, `mutable_field`, `for`, `ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `owns`, `views`, `consumes`, `produces`, `immutable`, `mutable`, `mutable_field`, `for`, `ensures`, or `}}` in `{}`",
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
                .any(|clause| !matches!(clause.proof(), Proof::Default))
                || ensures
                    .iter()
                    .any(|clause| !matches!(clause.proof(), Proof::Default))
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

        Ok(FunctionBlock {
            signature,
            requires,
            structural_clauses,
            effects,
            ensures,
            grouped_proof,
        })
    }

    fn parse_contract_let_binding(&mut self) -> Result<ContractLetBinding, ClickError> {
        self.expect_ident_spelling("let")?;
        let name = self.expect_ident("let binding name")?;
        let c_type = if self.peek() == Some(&Token::Colon) {
            self.position += 1;
            Some(self.parse_type()?.c_type)
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

    fn parse_function_signature(
        &mut self,
    ) -> Result<(FunctionSignature, BTreeMap<String, String>), ClickError> {
        let return_type = self.parse_type()?.c_type;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let struct_params = parsed_parameters.struct_params;

        Ok((
            FunctionSignature {
                return_type,
                name,
                parameters: parsed_parameters.parameters,
            },
            struct_params,
        ))
    }

    fn parse_parameters(&mut self) -> Result<ParsedParameters, ClickError> {
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(ParsedParameters {
                parameters,
                struct_params,
            });
        }

        loop {
            let parsed_type = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            let parsed_parameter = self.parse_parameter_array_suffix(name, parsed_type)?;
            if let Some(struct_name) = parsed_parameter.struct_name {
                struct_params.insert(parsed_parameter.parameter.name.clone(), struct_name);
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
                });
            }
            return Err(self.error("only pointer-to-struct types are supported"));
        }

        let scalar_type = match spelling.as_str() {
            "int32" => C0Type::Int32,
            "uint8" => C0Type::UInt8,
            _ => {
                return Err(self.error(format!(
                    "expected type `int32` or `uint8`, got `{spelling}`"
                )));
            }
        };
        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            Ok(ParsedType {
                c_type: match scalar_type {
                    C0Type::Int32 => C0Type::Int32Pointer,
                    C0Type::UInt8 => C0Type::UInt8Pointer,
                    _ => unreachable!("scalar type should not be aggregate"),
                },
                struct_name: None,
            })
        } else {
            Ok(ParsedType {
                c_type: scalar_type,
                struct_name: None,
            })
        }
    }

    fn parse_parameter_array_suffix(
        &mut self,
        name: String,
        parsed_type: ParsedType,
    ) -> Result<ParsedParameter, ClickError> {
        if self.peek() != Some(&Token::LBracket) {
            let struct_name = parsed_type.struct_name;
            return Ok(ParsedParameter {
                parameter: FunctionParameter {
                    c_type: parsed_type.c_type,
                    name,
                    struct_name: struct_name.clone(),
                },
                struct_name,
            });
        }
        if parsed_type.struct_name.is_some() {
            return Err(self.error("array parameters of struct type are not supported"));
        }
        let pointer_type = match parsed_type.c_type {
            C0Type::Int32 => C0Type::Int32Pointer,
            C0Type::UInt8 => C0Type::UInt8Pointer,
            _ => return Err(self.error("only scalar array parameters are supported")),
        };

        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
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
            (Some("read"), Some(Token::LParen)) => return Err(self.error(
                "`requires` accepts pure propositions only; use `views` for read access",
            )),
            (Some("write"), Some(Token::LParen)) => return Err(self.error(
                "`requires` accepts pure propositions only; use `owns` or `consumes` for owned access",
            )),
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
        let requirement = if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next() == Some(&Token::Comma)
        {
            let name = self.expect_ident("range base name")?;
            self.expect(Token::Comma)?;
            let bytes = self.parse_range_bytes()?;
            Requirement::LoadableBytes { name, bytes }
        } else {
            let segment = self.parse_current_contract_segment()?;
            Requirement::LoadableSegment { segment }
        };
        self.expect(Token::RParen)?;
        Ok(requirement)
    }

    fn parse_resource_clause(&mut self) -> Result<ResourceClause, ClickError> {
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let segment = self.parse_current_contract_segment()?;
        self.expect(Token::RParen)?;
        match name.as_str() {
            "read" => Ok(ResourceClause::Read(segment)),
            "write" => Ok(ResourceClause::Write(segment)),
            _ => Err(self.error(format!("unknown resource `{name}`"))),
        }
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
        if matches!(self.peek_ident(), Some("read" | "write"))
            && self.peek_next() == Some(&Token::LParen)
        {
            return self.parse_resource_clause();
        }
        if matches!(self.peek(), Some(Token::Ident(_))) && self.peek_next() == Some(&Token::LParen)
        {
            return self.parse_declared_resource_call_with_access(access);
        }
        let segment = self.parse_current_contract_segment()?;
        Ok(match access {
            ResourceAccessMode::Own => ResourceClause::Write(segment),
            ResourceAccessMode::View => ResourceClause::Read(segment),
        })
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
            Some(token) => {
                Err(self.error(format!("expected loadable byte expression, got {token:?}")))
            }
            None => Err(self.error("expected loadable byte expression, got end of input")),
        }
    }

    fn parse_region_proof_clause(&mut self) -> Result<StructuralClause, ClickError> {
        self.expect_ident_spelling("for")?;
        let region = self.parse_region_proof_code_region()?;
        let label = if self.peek_ident() == Some("as") {
            self.position += 1;
            Some(self.expect_ident("code region label")?)
        } else {
            None
        };
        self.expect(Token::LBrace)?;
        let mut items = Vec::new();
        let mut initialize_proof = None;
        let mut preserve_proof = None;
        while self.peek() != Some(&Token::RBrace) {
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
        if items.is_empty() {
            return Err(self.error("region proof block must contain at least one item"));
        }
        Ok(StructuralClause {
            region,
            label,
            items,
            initialize_proof,
            preserve_proof,
        })
    }

    fn parse_region_proof_code_region(&mut self) -> Result<CodeRegion, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "loop" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("loop index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegion::Loop(index))
            }
            Some(Token::Ident(kind)) if kind == "statement" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("statement index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegion::Statement(index))
            }
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected `loop(N)` or `statement(N)`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected `loop(N)` or `statement(N)`, got {token:?}"
            ))),
            None => Err(self.error("expected `loop(N)` or `statement(N)`, got end of input")),
        }
    }

    fn parse_region_proof_items(&mut self) -> Result<Vec<StructuralItem>, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "invariant" || kind == "assert" => {
                let item_kind = if kind == "invariant" {
                    StructuralItemKind::Invariant
                } else {
                    StructuralItemKind::Assert
                };
                let proposition = self.parse_proposition()?;
                let proof = if item_kind == StructuralItemKind::Invariant {
                    if self.peek_ident() == Some("by") {
                        return Err(self.error(
                            "invariant proofs belong to the loop; use `initialize by ...` and `preserve by ...`",
                        ));
                    }
                    self.expect(Token::Semicolon)?;
                    Proof::Tactic(SmartTactic::Auto)
                } else {
                    self.parse_proof_clause_or_default()?
                };
                Ok(vec![StructuralItem {
                    kind: item_kind,
                    claim: StructuralItemClaim::Proposition(proposition),
                    proof,
                }])
            }
            Some(Token::Ident(kind))
                if kind == "immutable" || kind == "mutable" || kind == "mutable_field" =>
            {
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
                    if effect_kind != "immutable"
                        && effect_kind != "mutable"
                        && effect_kind != "mutable_field"
                    {
                        return Err(self.error(format!(
                            "expected `immutable`, `mutable`, or `mutable_field` inside `step`, got `{effect_kind}`"
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
                "expected `invariant`, `assert`, `immutable`, `mutable`, `mutable_field`, or `step`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected `invariant`, `assert`, `immutable`, `mutable`, `mutable_field`, or `step`, got {token:?}"
            ))),
            None => Err(self.error(
                "expected `invariant`, `assert`, `immutable`, `mutable`, `mutable_field`, or `step`, got end of input",
            )),
        }
    }

    fn parse_effect_clause(&mut self) -> Result<EffectClause, ClickError> {
        let effect = match self.next() {
            Some(Token::Ident(kind))
                if kind == "immutable" || kind == "mutable" || kind == "mutable_field" =>
            {
                self.parse_effect_after_keyword(kind)?
            }
            Some(Token::Ident(kind)) => {
                return Err(self.error(format!(
                    "expected `immutable`, `mutable`, or `mutable_field`, got `{kind}`"
                )));
            }
            Some(token) => {
                return Err(self.error(format!(
                    "expected `immutable`, `mutable`, or `mutable_field`, got {token:?}"
                )));
            }
            None => {
                return Err(self.error(
                    "expected `immutable`, `mutable`, or `mutable_field`, got end of input",
                ));
            }
        };
        let proof = self.parse_proof_clause_or_default()?;
        Ok(EffectClause { effect, proof })
    }

    fn parse_effect_after_keyword(&mut self, kind: String) -> Result<Effect, ClickError> {
        if kind == "immutable" {
            return Ok(Effect::Immutable);
        }

        if kind == "mutable_field" {
            return self.parse_mutable_field_effect();
        }

        let mut segments = vec![self.parse_contract_segment()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            segments.push(self.parse_contract_segment()?);
        }
        Ok(Effect::Mutable(segments))
    }

    fn parse_mutable_field_effect(&mut self) -> Result<Effect, ClickError> {
        let mut segments = vec![self.parse_current_field_segment()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            segments.push(self.parse_current_field_segment()?);
        }
        Ok(Effect::Mutable(segments))
    }

    fn parse_current_field_segment(&mut self) -> Result<ContractSegment, ClickError> {
        self.expect(Token::LParen)?;
        let base = self.parse_ensure_primary()?.to_kernel_expression();
        self.expect(Token::Arrow)?;
        let field_name = self.expect_ident("field name")?;
        self.expect(Token::RParen)?;
        self.resolve_field_segment(base, &field_name)
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
        if self.peek_next() == Some(&Token::LParen) {
            match self.peek_ident() {
                Some("read") => {
                    return Err(self.error(
                        "`ensures` accepts pure propositions only; use `views` to retain read access",
                    ));
                }
                Some("write") => {
                    return Err(self.error(
                        "`ensures` accepts pure propositions only; use `owns` or `produces` for owned output",
                    ));
                }
                _ => {}
            }
        }
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
            let c_type = self.parse_type()?.c_type;
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

        if self.peek_ident() == Some("exists") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let c_type = self.parse_type()?.c_type;
            let name = self.expect_ident("exists variable name")?;
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

        if self.peek() == Some(&Token::LParen) {
            let start = self.position;
            match self.parse_range_proposition_method() {
                Ok(proposition) => return Ok(proposition),
                Err(_) => {
                    self.position = start;
                }
            }
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

        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            let start = self.position;
            self.position += 2;
            let proposition_at_point = self.parse_visit_selector().and_then(|selector| {
                self.expect(Token::Comma)?;
                let proposition = self.parse_proposition()?;
                self.expect(Token::RParen)?;
                Ok(ClickProposition::At {
                    selector,
                    proposition: Box::new(proposition),
                })
            });
            if proposition_at_point.is_ok() {
                return proposition_at_point;
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

    fn parse_by_clause(&mut self) -> Result<Proof, ClickError> {
        self.expect_ident_spelling("by")?;
        if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let proof = match self.peek() {
                Some(Token::Ident(name))
                    if is_tactic_name(name) && self.peek_next() == Some(&Token::Semicolon) =>
                {
                    let tactic = self.parse_tactic()?;
                    self.expect(Token::RBrace)?;
                    Proof::Tactic(tactic)
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
                    Proof::Script(tactics)
                }
                None => return Err(self.error("expected tactic, got end of input")),
            };
            return Ok(proof);
        }

        Ok(Proof::Tactic(self.parse_tactic()?))
    }

    fn parse_proof_clause_or_default(&mut self) -> Result<Proof, ClickError> {
        if self.peek_ident() == Some("by") {
            self.parse_by_clause()
        } else {
            self.expect(Token::Semicolon)?;
            Ok(Proof::Default)
        }
    }

    fn parse_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let name = self.expect_ident("tactic")?;
        if name == "have" {
            let proposition = self.parse_proposition()?;
            let proof = self.parse_by_clause()?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Have(ProofHave { proposition, proof }));
        }
        if name == "if" {
            let condition = self.parse_proposition()?;
            let then_tactics = self.parse_tactic_block("`if` branch")?;
            self.expect_ident_spelling("else")?;
            let else_tactics = self.parse_tactic_block("`else` branch")?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::If(ProofIf {
                condition,
                then_tactics,
                else_tactics,
            }));
        }
        if name == "advance" {
            self.expect(Token::LParen)?;
            let target = self.parse_program_point_ref()?;
            self.expect(Token::RParen)?;
            self.expect_ident_spelling("ensuring")?;
            self.expect(Token::LBrace)?;
            let mut assertions = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                let kind = self.expect_ident("advance assertion kind")?;
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
                            "expected advance assertion `fact`, `owns`, or `views`, got `{kind}`"
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
            self.expect_ident_spelling("by")?;
            let tactics = self.parse_tactic_block("`advance` proof")?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Advance(ProofAdvance {
                target,
                assertions,
                tactics,
            }));
        }
        if matches!(name.as_str(), "derive" | "calculate") {
            self.expect(Token::LParen)?;
            let proposition = self.parse_proposition()?;
            self.expect(Token::RParen)?;
            self.expect_ident_spelling("using")?;
            self.expect(Token::LBrace)?;
            let mut premises = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                self.expect_ident_spelling("fact")?;
                premises.push(self.parse_proposition()?);
                self.expect(Token::Semicolon)?;
            }
            self.expect(Token::RBrace)?;
            if premises.is_empty() {
                return Err(self.error(format!(
                    "`{name}` requires at least one explicit premise; use `normalize()` for a context-free goal"
                )));
            }
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            let derivation = ProofDerive {
                proposition,
                premises,
            };
            return Ok(if name == "derive" {
                ProofTactic::Derive(derivation)
            } else {
                ProofTactic::Calculate(derivation)
            });
        }
        let tactic = match name.as_str() {
            "step" => {
                if self.peek() == Some(&Token::LParen) {
                    self.expect_empty_tactic_args(&name)?;
                    ProofTactic::Step
                } else {
                    self.expect_ident_spelling("using")?;
                    self.expect(Token::LBrace)?;
                    let mut premises = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        self.expect_ident_spelling("fact")?;
                        premises.push(self.parse_proposition()?);
                        self.expect(Token::Semicolon)?;
                    }
                    self.expect(Token::RBrace)?;
                    if premises.is_empty() {
                        return Err(self.error(
                            "`step using` requires at least one explicit premise; use `step()` without premises",
                        ));
                    }
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::StepUsing(premises));
                }
            }
            "close_invariants" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::CloseInvariants
            }
            "apply_loop_summary" => {
                self.expect(Token::LParen)?;
                let region_ref = self.parse_code_region_ref()?;
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    ProofTactic::ApplyLoopSummary(region_ref)
                } else {
                    self.position += 1;
                    self.expect(Token::LBrace)?;
                    let mut premises = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        self.expect_ident_spelling("fact")?;
                        premises.push(self.parse_proposition()?);
                        self.expect(Token::Semicolon)?;
                    }
                    self.expect(Token::RBrace)?;
                    if premises.is_empty() {
                        return Err(self.error(
                            "`apply_loop_summary using` requires at least one explicit premise",
                        ));
                    }
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::ApplyLoopSummaryUsing {
                        region: region_ref,
                        premises,
                    });
                }
            }
            "symbolic_execute" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::ExecuteRest
            }
            "execute_step" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::ExecuteStep
            }
            "execute_then_step" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::ExecuteThenStep
            }
            "execute_else_step" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::ExecuteElseStep
            }
            "execute_rest" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::ExecuteRest
            }
            "execute_until" => {
                self.expect(Token::LParen)?;
                let region_ref = self.parse_code_region_ref()?;
                self.expect(Token::RParen)?;
                ProofTactic::ExecuteUntil(region_ref)
            }
            "bounded_execute" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::BoundedExecute
            }
            "frame" => {
                self.expect(Token::LParen)?;
                let region_ref = if self.peek() == Some(&Token::RParen) {
                    None
                } else {
                    Some(self.parse_code_region_ref()?)
                };
                self.expect(Token::RParen)?;
                ProofTactic::Frame(region_ref)
            }
            "unfold" => {
                self.expect(Token::LParen)?;
                let tactic = if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    ProofTactic::UnfoldResource(self.parse_declared_resource_call()?)
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
                    self.position += 1;
                    self.expect(Token::LBrace)?;
                    let mut premises = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        self.expect_ident_spelling("fact")?;
                        premises.push(self.parse_proposition()?);
                        self.expect(Token::Semicolon)?;
                    }
                    self.expect(Token::RBrace)?;
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
                let resource =
                    self.parse_declared_resource_call_with_access(ResourceAccessMode::View)?;
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
            "normalize" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Normalize
            }
            "intro" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Intro
            }
            "conjunction" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Conjunction
            }
            "left" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Left
            }
            "right" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Right
            }
            "double_negation" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::DoubleNegation
            }
            "vacuous" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Vacuous
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
                    self.position += 1;
                    self.expect(Token::LBrace)?;
                    let mut premises = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        self.expect_ident_spelling("fact")?;
                        premises.push(self.parse_proposition()?);
                        self.expect(Token::Semicolon)?;
                    }
                    self.expect(Token::RBrace)?;
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
            "simp" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Simp
            }
            "fold" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_declared_resource_call()?;
                self.expect(Token::RParen)?;
                ProofTactic::FoldResource(resource)
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

    fn parse_tactic_block(&mut self, context: &str) -> Result<Vec<ProofTactic>, ClickError> {
        self.expect(Token::LBrace)?;
        if self.peek() == Some(&Token::RBrace) {
            return Err(self.error(format!("{context} must contain at least one tactic")));
        }
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
        let base = if matches!(
            self.peek_ident(),
            Some("load_int32" | "load_uint8" | "load_int32_pointer" | "load_uint8_pointer")
        ) && self.peek_next() == Some(&Token::LParen)
        {
            let expression = self.parse_contract_primary()?;
            contract_expression_as_c_fragment(&expression).ok_or_else(|| {
                self.error("memory segment base must be a current C pointer expression")
            })?
        } else if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            contract_expression_as_c_fragment(&expression).ok_or_else(|| {
                self.error("memory segment base must be a current C pointer expression")
            })?
        } else {
            self.parse_ensure_primary()?.to_kernel_expression()
        };
        if self.peek() == Some(&Token::Arrow) {
            self.position += 1;
            let field_name = self.expect_ident("field name")?;
            return self.resolve_field_segment(base, &field_name);
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
            });
        };
        Ok(ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start: CExpression::Value(int32(field.offset_bytes / 4)),
            end: CExpression::Value(int32((field.offset_bytes + field.byte_width) / 4)),
        })
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
        if field.offset_bytes() % 4 != 0 || field.byte_width() % 4 != 0 {
            return Err(
                self.error("field places currently require int32-aligned offsets and widths")
            );
        }
        Ok(ResolvedField {
            c_type: field.c_type(),
            struct_name: field.struct_name().map(str::to_string),
            offset_bytes: field.offset_bytes(),
            byte_width: field.byte_width(),
        })
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
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_contract_expression()?;
                    self.expect(Token::RBracket)?;
                    expression = ContractExpression::Index(Box::new(expression), Box::new(index));
                    struct_name = None;
                }
                Some(Token::Arrow) => {
                    self.position += 1;
                    let field_name = self.expect_ident("field name")?;
                    let Some(base) = contract_expression_as_c_fragment(&expression) else {
                        return Err(
                            self.error("field access is only supported on current C fragments")
                        );
                    };
                    if let Some(base_struct_name) = &struct_name {
                        let field =
                            self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                        let pointer = self.offset_field_pointer(base, field.offset_bytes);
                        struct_name = field.struct_name;
                        expression = ContractExpression::CFragment(CExpression::TypedLoad {
                            pointer: Box::new(pointer),
                            value_type: field.c_type.to_kernel_type(),
                        });
                    } else {
                        expression = ContractExpression::CFragment(
                            self.resolve_field_load(base, &field_name)?,
                        );
                    }
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_contract_primary(&mut self) -> Result<ContractExpression, ClickError> {
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
            let selector = self.parse_visit_selector()?;
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

    fn parse_visit_selector(&mut self) -> Result<VisitSelector, ClickError> {
        Ok(VisitSelector::ProgramPoint(self.parse_program_point_ref()?))
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
                    tokens.push(Token::Dot);
                    index += 1;
                }
            }
            '+' => {
                tokens.push(Token::Plus);
                index += 1;
            }
            '-' => {
                if chars.get(index + 1) == Some(&'>') {
                    tokens.push(Token::Arrow);
                    index += 2;
                } else {
                    tokens.push(Token::Minus);
                    index += 1;
                }
            }
            '*' => {
                tokens.push(Token::Star);
                index += 1;
            }
            '/' => {
                tokens.push(Token::Slash);
                index += 1;
            }
            '%' => {
                tokens.push(Token::Percent);
                index += 1;
            }
            '&' => {
                tokens.push(Token::Amp);
                index += 1;
            }
            '|' => {
                tokens.push(Token::Pipe);
                index += 1;
            }
            '^' => {
                tokens.push(Token::Caret);
                index += 1;
            }
            '~' => {
                tokens.push(Token::Tilde);
                index += 1;
            }
            '<' => {
                if chars.get(index + 1) == Some(&'<') {
                    tokens.push(Token::ShiftLeft);
                    index += 2;
                } else if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::LessEqual);
                    index += 2;
                } else {
                    tokens.push(Token::LessThan);
                    index += 1;
                }
            }
            '>' => {
                if chars.get(index + 1) == Some(&'>') {
                    tokens.push(Token::ShiftRight);
                    index += 2;
                } else if chars.get(index + 1) == Some(&'=') {
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
                    tokens.push(Token::Equal);
                    index += 1;
                }
            }
            '"' => {
                let (value, next_index) = tokenize_string(&chars, index)?;
                tokens.push(Token::String(value));
                index = next_index;
            }
            '\'' => {
                let (value, next_index) = tokenize_char_literal(&chars, index)?;
                tokens.push(Token::CharLiteral(value));
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

fn tokenize_char_literal(chars: &[char], start: usize) -> Result<(u8, usize), ClickError> {
    let Some(first) = chars.get(start + 1).copied() else {
        return Err(ClickError::new("unterminated character literal"));
    };
    let (value, end) = if first == '\\' {
        let Some(escaped) = chars.get(start + 2).copied() else {
            return Err(ClickError::new("unterminated character literal"));
        };
        let value = match escaped {
            'n' => b'\n',
            'r' => b'\r',
            't' => b'\t',
            '0' => b'\0',
            '\\' => b'\\',
            '\'' => b'\'',
            '"' => b'"',
            other => {
                return Err(ClickError::new(format!(
                    "unsupported character escape `\\{other}`"
                )));
            }
        };
        (value, start + 3)
    } else {
        if !first.is_ascii() {
            return Err(ClickError::new(
                "only ASCII character literals are supported",
            ));
        }
        (first as u8, start + 2)
    };

    if chars.get(end) != Some(&'\'') {
        return Err(ClickError::new(
            "character literals must contain exactly one byte",
        ));
    }

    Ok((value, end + 1))
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
