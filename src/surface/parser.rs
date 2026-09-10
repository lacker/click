mod tokenizer;

use tokenizer::tokenize;

use super::*;

#[derive(Clone, Debug)]
pub(super) struct QualifiedCObject {
    pub expression: CExpression,
    pub address: Option<CExpression>,
    pub struct_name: Option<String>,
    pub array_shape: Option<Vec<u32>>,
    pub ambiguous: bool,
}

/// Click's recursive-descent proposition and contract-expression parsers use
/// the native stack once per syntactically nested parenthesis. Keep the
/// supported surface depth explicit and reject deeper input before recursive
/// parsing begins.
pub(super) const PARENTHESIS_NESTING_LIMIT: usize = 16;
pub(super) const MATCH_NESTING_LIMIT: usize = 16;

/// The index shape and scalar element type of a C global or static array
/// visible to one function's contract. Resource lowering only knows parameter
/// types, so the element type travels with the name to give a byte or
/// halfword slice its physical element width instead of the `int32` default.
#[derive(Clone, Debug)]
pub(super) struct GlobalArrayShape {
    pub(super) shape: Vec<u32>,
    pub(super) element_type: CType,
}

pub(super) fn parse(source: &str) -> Result<ClickFile, ClickError> {
    Parser::new(source)?.parse_file()
}

pub(super) fn parse_with_layouts_and_aggregate_objects(
    source: &str,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    qualified_objects: BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>,
) -> Result<ClickFile, ClickError> {
    let mut parser = Parser::new_with_layouts_and_aggregate_objects(
        source,
        struct_layouts,
        union_layouts,
        aggregate_objects_by_function,
        aggregate_array_objects_by_function,
        global_array_shapes_by_function,
    )?;
    parser.qualified_objects = Some(qualified_objects);
    parser.parse_file()
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
    UInt32Number(u32),
    Int64Number(i64),
    UInt64Number(u64),
    CharLiteral(u8),
    String(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    ColonColon,
    Comma,
    Semicolon,
    Dot,
    DotDot,
    Arrow,
    Equal,
    FatArrow,
    EqualEqual,
    BangEqual,
    LessThan,
    LessEqual,
    ShiftLeft,
    GreaterThan,
    GreaterEqual,
    ShiftRight,
    Plus,
    PlusPlus,
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
            Self::UInt32Number(value) => format!("uint32 number `{value}u32`"),
            Self::Int64Number(value) => format!("int64 number `{value}i64`"),
            Self::UInt64Number(value) => format!("uint64 number `{value}u64`"),
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
            | Self::UInt32Number(_)
            | Self::Int64Number(_)
            | Self::UInt64Number(_)
            | Self::CharLiteral(_)
            | Self::String(_) => "",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::Colon => ":",
            Self::ColonColon => "::",
            Self::Comma => ",",
            Self::Semicolon => ";",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::Arrow => "->",
            Self::Equal => "=",
            Self::FatArrow => "=>",
            Self::EqualEqual => "==",
            Self::BangEqual => "!=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::ShiftLeft => "<<",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
            Self::ShiftRight => ">>",
            Self::Plus => "+",
            Self::PlusPlus => "++",
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
    source_aliases: BTreeMap<String, String>,
    qualified_objects: Option<BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>>,
    pending_contract_name: Option<String>,
    contract_resource_parameters: BTreeMap<String, ResourceClause>,
    contract_proof_bindings: BTreeMap<String, Vec<(String, Variable, String)>>,
    next_resource_identity: u64,
    current_resource_bindings: BTreeMap<String, (Variable, String)>,
    current_resource_fields: BTreeMap<String, ResourceFieldAccess>,
    current_resource_targets: BTreeMap<String, ResourceClause>,
    match_nesting: usize,
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    matching_parentheses: Vec<Option<usize>>,
    position: usize,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    current_struct_params: BTreeMap<String, String>,
    aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    current_aggregate_objects: BTreeMap<String, String>,
    current_struct_array_params: BTreeSet<String>,
    current_global_array_shapes: BTreeMap<String, GlobalArrayShape>,
    current_algebraic_params: BTreeMap<String, (AlgebraicTypeApplication, usize)>,
    current_click_type_parameters: BTreeSet<String>,
    current_contract_bindings: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
    struct_pointer: bool,
    constant: bool,
    pointee_constant: bool,
}

pub(super) fn is_c_type_keyword(name: &str) -> bool {
    matches!(
        name,
        "void"
            | "struct"
            | "int32"
            | "int"
            | "int32_t"
            | "int16"
            | "int64"
            | "uint8"
            | "uint8_t"
            | "uint32"
            | "uint32_t"
            | "uint16"
            | "uint64"
            | "unsigned"
            | "signed"
            | "char"
            | "short"
            | "long"
            | "size_t"
            | "ssize_t"
            | "int16_t"
            | "int64_t"
            | "uint16_t"
            | "uint64_t"
            | "float"
            | "double"
            | "const"
            | "volatile"
    )
}

pub(in crate::surface) fn algebraic_field_c_type_supported(c_type: C0Type) -> bool {
    !matches!(
        c_type,
        C0Type::Void
            | C0Type::FunctionPointer(_)
            | C0Type::Int16Array(_)
            | C0Type::Int32Array(_)
            | C0Type::CharArray(_)
            | C0Type::UInt8Array(_)
            | C0Type::UInt16Array(_)
            | C0Type::UInt32Array(_)
            | C0Type::Int64Array(_)
            | C0Type::UInt64Array(_)
            | C0Type::Float32Array(_)
            | C0Type::Float64Array(_)
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

fn algebraic_parameter_types(
    parameters: &[FunctionParameter],
) -> BTreeMap<String, (AlgebraicTypeApplication, usize)> {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| match parameter.click_type() {
            ClickType::Algebraic(application) => {
                Some((parameter.name().to_string(), (application.clone(), index)))
            }
            ClickType::Parameter(_) | ClickType::C(_) => None,
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedField {
    c_type: C0Type,
    struct_name: Option<String>,
    union_name: Option<String>,
    function_pointer_signature: Option<syntax::C0FunctionPointerSignature>,
    array_element_width: Option<u32>,
    array_shape: Option<Vec<u32>>,
    offset_bytes: u32,
    byte_width: u32,
    slot_end_bytes: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ContractLetBinding {
    pub(super) name: String,
    pub(super) click_type: Option<ClickType>,
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
        Self::new_with_layouts(source, BTreeMap::new(), BTreeMap::new())
    }

    fn new_with_layouts(
        source: &str,
        struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
        union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    ) -> Result<Self, ClickError> {
        Self::new_with_layouts_and_aggregate_objects(
            source,
            struct_layouts,
            union_layouts,
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeMap::new(),
        )
    }

    fn new_with_layouts_and_aggregate_objects(
        source: &str,
        struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
        union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
        aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
        aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
        global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    ) -> Result<Self, ClickError> {
        let (tokens, positions) = tokenize(source)?;
        let matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
        Ok(Self {
            source_aliases: BTreeMap::new(),
            qualified_objects: None,
            pending_contract_name: None,
            contract_resource_parameters: BTreeMap::new(),
            contract_proof_bindings: BTreeMap::new(),
            next_resource_identity: 0,
            current_resource_bindings: BTreeMap::new(),
            current_resource_fields: BTreeMap::new(),
            current_resource_targets: BTreeMap::new(),
            tokens,
            positions,
            matching_parentheses,
            match_nesting: 0,
            position: 0,
            struct_layouts,
            union_layouts,
            current_struct_params: BTreeMap::new(),
            aggregate_objects_by_function,
            aggregate_array_objects_by_function,
            global_array_shapes_by_function,
            current_aggregate_objects: BTreeMap::new(),
            current_struct_array_params: BTreeSet::new(),
            current_global_array_shapes: BTreeMap::new(),
            current_algebraic_params: BTreeMap::new(),
            current_click_type_parameters: BTreeSet::new(),
            current_contract_bindings: BTreeSet::new(),
        })
    }

    fn parse_file(mut self) -> Result<ClickFile, ClickError> {
        let mut file =
            super::validation::expand_declared_resource_clauses(self.parse_file_items()?)?;
        super::validation::validate_click_definitions(&file)?;
        super::lowering::check_resource_field_schemas(&mut file)?;
        Ok(file)
    }

    fn parse_file_items(&mut self) -> Result<ClickFile, ClickError> {
        let mut verifying_sources = Vec::new();
        let mut algebraic_type_definitions = Vec::new();
        let mut predicate_definitions = Vec::new();
        let mut click_function_definitions = Vec::new();
        let mut resource_definitions = Vec::new();
        let mut theorem_definitions = Vec::new();
        let mut deferred_theorems = Vec::new();
        let mut contract_definitions = Vec::new();
        let mut function_blocks = Vec::new();

        while self.peek().is_some() {
            if self.peek_ident() == Some("verifying") {
                verifying_sources.push(self.parse_verifying_source()?);
            } else if self.peek_ident() == Some("spec") {
                algebraic_type_definitions.push(self.parse_algebraic_type_definition()?);
            } else if self.peek_ident() == Some("predicate") {
                predicate_definitions.push(self.parse_predicate_definition()?);
            } else if self.peek_ident() == Some("function") {
                click_function_definitions.push(self.parse_click_function_definition()?);
            } else if self.peek_ident() == Some("theorem") {
                // Resource parameters of an executes target are lexical proof
                // bindings, including when that contract is declared later.
                // Visit each declaration's tokens once here, then parse it
                // after the contract index is complete.
                deferred_theorems.push(self.position);
                let mut depth = 0usize;
                loop {
                    crate::instrumentation::record_deterministic_work(1);
                    match self.peek() {
                        Some(Token::LBrace) => depth += 1,
                        Some(Token::RBrace) if depth > 0 => {
                            depth -= 1;
                            if depth == 0 {
                                self.position += 1;
                                break;
                            }
                        }
                        None => return Err(self.error("unterminated theorem declaration")),
                        _ => {}
                    }
                    self.position += 1;
                }
            } else if self.peek_ident() == Some("contract") {
                contract_definitions.push(self.parse_contract_definition()?);
            } else if self.peek_ident() == Some("abstract") {
                resource_definitions.push(self.parse_resource_definition(true)?);
            } else if self.peek_ident() == Some("resource") {
                resource_definitions.push(self.parse_resource_definition(false)?);
            } else if self.peek_ident() == Some("counted") {
                return Err(self
                    .error("`counted resource` has been removed; declare an ordinary `resource`"));
            } else if self.peek_ident() == Some("extern") {
                function_blocks.push(self.parse_function_block(true)?);
            } else {
                function_blocks.push(self.parse_function_block(false)?);
            }
        }

        for definition in &algebraic_type_definitions {
            if self.source_aliases.contains_key(&definition.name) {
                return Err(self.error(format!(
                    "C source alias `{}` conflicts with a specification datatype",
                    definition.name
                )));
            }
        }
        let end = self.position;
        for position in deferred_theorems {
            self.position = position;
            theorem_definitions.push(self.parse_theorem_definition()?);
        }
        self.position = end;
        let file = ClickFile {
            verifying_sources,
            algebraic_type_definitions,
            predicate_definitions,
            click_function_definitions,
            resource_definitions,
            theorem_definitions,
            contract_definitions,
            function_blocks,
        };
        Ok(file)
    }

    fn parse_contract_definition(&mut self) -> Result<ContractDefinition, ClickError> {
        self.expect_ident_spelling("contract")?;
        let proof_parameters = if self.peek_next() == Some(&Token::LParen) {
            let name = self.expect_ident("contract name")?;
            self.expect(Token::LParen)?;
            let mut parameters = Vec::new();
            while self.peek() != Some(&Token::RParen) {
                if self.peek_next() != Some(&Token::Colon) {
                    return Err(
                        self.error("contract proof parameters require `name: resource(...)`")
                    );
                }
                let parameter = self.parse_owned_resource_binding()?;
                let ResourceClause::Named { binding, .. } = &parameter else {
                    return Err(
                        self.error("contract proof parameters require `name: resource(...)`")
                    );
                };
                self.contract_resource_parameters
                    .insert(binding.name.clone(), parameter.clone());
                parameters.push(parameter);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::RParen)?;
            self.expect_ident_spelling("for")?;
            self.current_resource_bindings.clear();
            self.pending_contract_name = Some(name);
            Some(parameters)
        } else {
            None
        };
        let function_block = self.parse_function_block(false)?;
        if let Some(parameters) = &proof_parameters {
            let identities = parameters
                .iter()
                .filter_map(|parameter| match parameter {
                    ResourceClause::Named { binding, .. } => Some(binding.identity),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            let mut owned_parameters = BTreeSet::new();
            for requirement in function_block.requires() {
                if let Requirement::Resource(ResourceClause::Named { binding, .. }) =
                    requirement.inner()
                {
                    if !identities.contains(&binding.identity) {
                        return Err(self.error(format!(
                            "resource `{}` must be declared in the contract proof-parameter list",
                            binding.name
                        )));
                    }
                    if !owned_parameters.insert(binding.identity) {
                        return Err(self.error(format!(
                            "duplicate ownership of proof parameter `{}`",
                            binding.name
                        )));
                    }
                }
            }
        }
        self.contract_resource_parameters.clear();
        if function_block.decreases().is_some()
            || function_block.grouped_proof().is_some()
            || !function_block.constructs().is_empty()
            || function_block
                .ensures()
                .iter()
                .any(|clause| !matches!(clause.proof(), SourceProof::Default))
            || function_block
                .effects()
                .iter()
                .any(|clause| !matches!(clause.proof(), SourceProof::Default))
        {
            return Err(self.error(
                "named contracts cannot carry proofs, `decreases`, or `constructs` clauses",
            ));
        }
        let bindings = proof_parameters
            .as_deref()
            .unwrap_or_default()
            .iter()
            .filter_map(|parameter| {
                let ResourceClause::Named { binding, resource } = parameter else {
                    return None;
                };
                let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                    return None;
                };
                Some((binding.name.clone(), binding.identity, name.clone()))
            })
            .collect();
        self.contract_proof_bindings
            .insert(function_block.signature().name().to_string(), bindings);
        Ok(ContractDefinition {
            proof_parameters,
            function_block,
        })
    }

    fn parse_algebraic_type_definition(&mut self) -> Result<AlgebraicTypeDefinition, ClickError> {
        self.expect_ident_spelling("spec")?;
        self.expect_ident_spelling("enum")?;
        let name = self.expect_ident("algebraic datatype name")?;
        let mut type_parameters = Vec::new();
        if self.peek() == Some(&Token::LessThan) {
            self.position += 1;
            loop {
                type_parameters.push(self.expect_ident("type parameter")?);
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::GreaterThan) => {
                        self.position += 1;
                        break;
                    }
                    Some(token) => {
                        return Err(self.error(format!(
                            "expected `,` or `>` after type parameter, got {}",
                            token.describe()
                        )));
                    }
                    None => return Err(self.error("expected `>` after type parameter")),
                }
            }
        }
        self.expect(Token::LBrace)?;
        let mut variants = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            let variant_name = self.expect_ident("variant name")?;
            let mut fields = Vec::new();
            if self.peek() == Some(&Token::LParen) {
                self.position += 1;
                if self.peek() != Some(&Token::RParen) {
                    loop {
                        fields.push(self.parse_algebraic_field_type(&type_parameters)?);
                        match self.peek() {
                            Some(Token::Comma) => self.position += 1,
                            Some(Token::RParen) => break,
                            Some(token) => {
                                return Err(self.error(format!(
                                    "expected `,` or `)` after variant field, got {}",
                                    token.describe()
                                )));
                            }
                            None => return Err(self.error("expected `)` after variant fields")),
                        }
                    }
                }
                self.expect(Token::RParen)?;
            }
            variants.push(AlgebraicVariantDefinition {
                name: variant_name,
                fields,
            });
            if self.peek() == Some(&Token::Comma) {
                self.position += 1;
            } else if self.peek() != Some(&Token::RBrace) {
                return Err(self.error("expected `,` or `}` after algebraic datatype variant"));
            }
        }
        self.expect(Token::RBrace)?;
        Ok(AlgebraicTypeDefinition {
            name,
            type_parameters,
            variants,
        })
    }

    fn parse_algebraic_field_type(
        &mut self,
        type_parameters: &[String],
    ) -> Result<AlgebraicFieldType, ClickError> {
        let name = self
            .peek_ident()
            .ok_or_else(|| self.error("expected algebraic variant field type"))?
            .to_string();
        if type_parameters.iter().any(|parameter| parameter == &name) {
            self.position += 1;
            return Ok(AlgebraicFieldType::Parameter(name));
        }
        if is_c_type_keyword(&name) {
            let parsed = self.parse_type()?;
            if !algebraic_field_c_type_supported(parsed.c_type) {
                return Err(self.error(
                    "algebraic datatype fields must be C scalar, data-pointer, or algebraic values",
                ));
            }
            return Ok(AlgebraicFieldType::C(parsed.c_type));
        }

        self.position += 1;
        let mut arguments = Vec::new();
        if self.peek() == Some(&Token::LessThan) {
            self.position += 1;
            loop {
                arguments.push(self.parse_algebraic_field_type(type_parameters)?);
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::GreaterThan) => {
                        self.position += 1;
                        break;
                    }
                    Some(Token::ShiftRight) => {
                        self.tokens[self.position] = Token::GreaterThan;
                        break;
                    }
                    Some(token) => {
                        return Err(self.error(format!(
                            "expected `,` or `>` after datatype argument, got {}",
                            token.describe()
                        )));
                    }
                    None => return Err(self.error("expected `>` after datatype arguments")),
                }
            }
        }
        Ok(AlgebraicFieldType::Algebraic { name, arguments })
    }

    fn parse_verifying_source(&mut self) -> Result<String, ClickError> {
        self.expect_ident_spelling("verifying")?;
        let source_path = self.expect_string("C source path")?;
        if self.peek_ident() == Some("as") {
            self.position += 1;
            let alias = self.expect_ident("C source alias")?;
            if self
                .source_aliases
                .insert(alias.clone(), source_path.clone())
                .is_some()
            {
                return Err(self.error(format!("duplicate C source alias `{alias}`")));
            }
        }
        self.expect(Token::Semicolon)?;
        Ok(source_path)
    }

    fn is_qualified_c_name(&self) -> bool {
        self.peek_next() == Some(&Token::ColonColon)
            && self
                .peek_ident()
                .is_some_and(|name| self.source_aliases.contains_key(name))
    }

    fn parse_qualified_c_name(&mut self) -> Result<(String, CExpression), ClickError> {
        let alias = self.expect_ident("C source alias")?;
        self.expect(Token::ColonColon)?;
        let mut name = self.expect_ident("C declaration name")?;
        if self.peek() == Some(&Token::ColonColon) {
            self.expect(Token::ColonColon)?;
            let local = self.expect_ident("function-local static name")?;
            name = format!("{name}::{local}");
        }
        let qualified = format!("{alias}::{name}");
        let source = self
            .source_aliases
            .get(&alias)
            .ok_or_else(|| self.error(format!("unknown C source alias `{alias}`")))?;
        let expression = match &self.qualified_objects {
            None => CExpression::Variable(qualified.clone()),
            Some(objects) => objects
                .get(source)
                .and_then(|objects| objects.get(&name))
                .map(|object| {
                    if object.ambiguous {
                        Err(self.error(format!("ambiguous function-local static `{qualified}`: multiple block scopes declare this name")))
                    } else {
                        Ok(object.expression.clone())
                    }
                })
                .ok_or_else(|| {
                    self.error(format!(
                        "no supported C object `{qualified}` in `{source}`"
                    ))
                })??,
        };
        Ok((qualified, expression))
    }

    fn qualified_object(&self, name: &str) -> Option<&QualifiedCObject> {
        let (alias, name) = name.split_once("::")?;
        self.qualified_objects
            .as_ref()?
            .get(self.source_aliases.get(alias)?)?
            .get(name)
    }

    fn parse_segment_primary(&mut self) -> Result<(ContractExpression, CExpression), ClickError> {
        if self.peek_next() == Some(&Token::ColonColon) {
            let (name, expression) = self.parse_qualified_c_name()?;
            return Ok((
                ContractExpression::CFragment(CExpression::Variable(name)),
                expression,
            ));
        }
        let expression = self.parse_ensure_primary()?.to_kernel_expression();
        // Keep the source spelling, but give a global array's pointer its
        // scalar element type. Resource lowering otherwise knows only
        // parameter types and would default a global byte slice to `int32`
        // cells, letting `owns bytes[0..1]` authorize the neighboring byte.
        let lowered = self.retype_global_array_pointer(&expression);
        Ok((ContractExpression::CFragment(expression), lowered))
    }

    /// Wraps a bare global-array name in a cast to its element pointer type.
    /// A parameter shadowing the global is not in the per-function shape map,
    /// so it keeps the parameter's own type.
    fn retype_global_array_pointer(&self, expression: &CExpression) -> CExpression {
        let CExpression::Variable(name) = expression else {
            return expression.clone();
        };
        match self
            .current_global_array_shapes
            .get(name)
            .and_then(|array| array.element_type.pointer_to())
        {
            Some(target_type) => CExpression::Cast {
                expression: Box::new(expression.clone()),
                target_type,
                pointee_volatile: false,
            },
            None => expression.clone(),
        }
    }

    fn parse_predicate_definition(&mut self) -> Result<PredicateDefinition, ClickError> {
        self.expect_ident_spelling("predicate")?;
        let name = self.expect_ident("predicate name")?;
        let type_parameters = self.parse_click_type_parameters()?;
        let previous_type_parameters = std::mem::replace(
            &mut self.current_click_type_parameters,
            type_parameters.iter().cloned().collect(),
        );
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
        let previous_algebraic_params = std::mem::replace(
            &mut self.current_algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let body = self.parse_proposition()?;
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;
        self.current_algebraic_params = previous_algebraic_params;
        self.current_click_type_parameters = previous_type_parameters;
        self.expect(Token::RBrace)?;
        Ok(PredicateDefinition {
            name,
            type_parameters,
            parameters: parsed_parameters.parameters,
            body,
        })
    }

    fn parse_click_function_definition(&mut self) -> Result<ClickFunctionDefinition, ClickError> {
        self.expect_ident_spelling("function")?;
        let name = self.expect_ident("function name")?;
        let type_parameters = self.parse_click_type_parameters()?;
        let previous_type_parameters = std::mem::replace(
            &mut self.current_click_type_parameters,
            type_parameters.iter().cloned().collect(),
        );
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Arrow)?;
        let (return_type, parsed_c_return_type) = self.parse_click_type()?;
        if let Some(parsed_return_type) = parsed_c_return_type {
            if parsed_return_type.struct_name.is_some() && !parsed_return_type.struct_pointer {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            if parsed_return_type.c_type == C0Type::Void {
                return Err(self.error("pure Click functions must return a value"));
            }
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
        let previous_algebraic_params = std::mem::replace(
            &mut self.current_algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let body = self.parse_contract_expression()?;
        self.current_struct_params = previous_struct_params;
        self.current_struct_array_params = previous_struct_array_params;
        self.current_algebraic_params = previous_algebraic_params;
        self.current_click_type_parameters = previous_type_parameters;
        self.expect(Token::RBrace)?;
        Ok(ClickFunctionDefinition {
            name,
            type_parameters,
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
        let previous_algebraic_params = std::mem::replace(
            &mut self.current_algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let previous_resource_bindings = std::mem::take(&mut self.current_resource_bindings);
        let previous_resource_targets = std::mem::take(&mut self.current_resource_targets);
        let previous_contract_bindings = std::mem::take(&mut self.current_contract_bindings);
        let composite_body = match self.peek() {
            Some(Token::Semicolon) if is_abstract => {
                self.position += 1;
                None
            }
            Some(Token::Semicolon) => {
                return Err(self
                    .error("a resource without a body must be declared with `abstract resource`"));
            }
            Some(Token::LBrace) if !is_abstract => Some(self.parse_composite_resource_body(&name)?),
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
        self.current_algebraic_params = previous_algebraic_params;
        self.current_resource_bindings = previous_resource_bindings;
        self.current_resource_targets = previous_resource_targets;
        self.current_contract_bindings = previous_contract_bindings;
        Ok(ResourceDefinition {
            name,
            parameters: parsed_parameters.parameters,
            composite_body,
            field_schema: None,
        })
    }

    fn parse_composite_resource_body(
        &mut self,
        resource_name: &str,
    ) -> Result<CompositeResourceBody, ClickError> {
        self.expect(Token::LBrace)?;
        let mut fields = Vec::new();
        while self.peek_ident() == Some("field") {
            self.position += 1;
            let name = self.expect_ident("resource field name")?;
            self.expect(Token::Colon)?;
            let (click_type, parsed_c_type) = self.parse_click_type()?;
            if parsed_c_type.as_ref().is_some_and(|ty| {
                !algebraic_field_c_type_supported(ty.c_type)
                    || ty.struct_name.is_some()
                    || ty.constant
                    || ty.pointee_constant
            }) {
                return Err(self.error(format!("resource field `{name}` requires an unqualified scalar, pointer, or algebraic Click type")));
            }
            self.expect(Token::Semicolon)?;
            fields.push(ResourceFieldDefinition { name, click_type });
        }
        let previous_resource_fields = self.current_resource_fields.clone();
        if !fields.is_empty() {
            self.current_resource_fields = fields
                .iter()
                .enumerate()
                .map(|(field_index, field)| {
                    (
                        field.name.clone(),
                        ResourceFieldAccess {
                            owner: "__body".into(),
                            resource_name: resource_name.into(),
                            identity: Variable(u64::MAX),
                            children: vec![],
                            field: field.name.clone(),
                            field_index,
                            click_type: Some(field.click_type.clone()),
                        },
                    )
                })
                .collect();
        }
        if self.peek_ident() == Some("match") {
            if self.match_nesting != 0 {
                return Err(self.error("nested resource matches are not supported"));
            }
            self.position += 1;
            let field = self.expect_ident("resource model field")?;
            self.expect(Token::LBrace)?;
            let mut arms = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                let type_name = self.expect_ident("match pattern datatype")?;
                self.expect(Token::ColonColon)?;
                let variant = self.expect_ident("match pattern variant")?;
                let mut bindings = Vec::new();
                if self.peek() == Some(&Token::LParen) {
                    self.position += 1;
                    while self.peek() != Some(&Token::RParen) {
                        bindings.push(self.expect_ident("match pattern binding")?);
                        if self.peek() != Some(&Token::Comma) {
                            break;
                        }
                        self.position += 1;
                    }
                    self.expect(Token::RParen)?;
                }
                self.expect(Token::FatArrow)?;
                let inserted = bindings
                    .iter()
                    .filter(|name| self.current_contract_bindings.insert((*name).clone()))
                    .cloned()
                    .collect::<Vec<_>>();
                self.match_nesting += 1;
                let saved_bindings = self.current_resource_bindings.clone();
                let saved_targets = self.current_resource_targets.clone();
                let body = self.parse_composite_resource_body(resource_name);
                self.current_resource_bindings = saved_bindings;
                self.current_resource_targets = saved_targets;
                self.match_nesting -= 1;
                let body = body?;
                for name in inserted {
                    self.current_contract_bindings.remove(&name);
                }
                if !body.fields.is_empty()
                    || body.matched.is_some()
                    || body.condition.is_some()
                    || !body.witnesses.is_empty()
                {
                    return Err(self.error("resource match arms currently require immediate memory clauses and facts, without fields, guards, matches, or witnesses"));
                }
                arms.push(ResourceMatchArm {
                    type_name,
                    variant,
                    bindings,
                    body,
                });
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                } else if self.peek() != Some(&Token::RBrace) {
                    return Err(self.error("expected `,` or `}` after resource match arm"));
                }
            }
            self.expect(Token::RBrace)?;
            self.expect(Token::RBrace)?;
            self.current_resource_fields = previous_resource_fields;
            return Ok(CompositeResourceBody {
                children: vec![],
                fields,
                matched: Some(ResourceMatchBody { field, arms }),
                condition: None,
                contains: vec![],
                facts: vec![],
                witnesses: vec![],
            });
        }
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
        let mut witnesses: Vec<ResourceWitness> = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("field") => return Err(self.error("resource fields must be declared before body clauses and outside the resource guard")),
                Some("let") => {
                    let binding = self.parse_contract_let_binding()?;
                    let ContractLetBindingKind::Where(condition) = binding.kind else {
                        return Err(self.error(
                            "a resource body `let` must be `let name: type where proposition;`",
                        ));
                    };
                    let click_type = binding
                        .click_type
                        .as_ref()
                        .expect("`let ... where` carries its type");
                    let Some(c_type) = click_type.c_type() else {
                        return Err(self.error(
                            "resource witnesses must have a C pointer type, not an algebraic type",
                        ));
                    };
                    if !c_type.is_pointer() {
                        return Err(self.error(format!(
                            "resource witness `{}` must have a pointer type",
                            binding.name
                        )));
                    }
                    if witnesses.iter().any(|witness| witness.name == binding.name) {
                        return Err(
                            self.error(format!("duplicate resource witness `{}`", binding.name))
                        );
                    }
                    witnesses.push(ResourceWitness {
                        name: binding.name,
                        c_type,
                    });
                    facts.push(condition);
                }
                Some("contains") => {
                    self.position += 1;
                    contains.push(self.parse_composite_resource_contains_clause()?);
                    self.expect(Token::Semicolon)?;
                }
                Some("owns") => {
                    self.position += 1;
                    if self.match_nesting == 0 && self.peek_next() == Some(&Token::Colon) {
                        return Err(self.error("named child resources currently require a constructor match arm"));
                    }
                    contains.push(self.parse_owned_resource_binding()?);
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
                        "expected `contains`, `owns`, `views`, `fact`, or `let` in resource body, got `{name}`"
                    )));
                }
                None => {
                    return Err(self.error(
                        "expected `contains`, `owns`, `views`, `fact`, or `let` in resource body, got end of input",
                    ));
                }
            }
        }
        self.expect(Token::RBrace)?;
        if condition.is_some() {
            self.expect(Token::RBrace)?;
        }
        contains = contains
            .into_iter()
            .flat_map(expand_aggregate_resource_clause)
            .collect();
        self.current_resource_fields = previous_resource_fields;
        Ok(CompositeResourceBody {
            children: vec![],
            fields,
            matched: None,
            condition,
            contains,
            facts,
            witnesses,
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
            let (click_type, parsed_c_type) = self.parse_click_type()?;
            let parsed_parameter = if let Some(parsed_type) = parsed_c_type {
                if self.peek() == Some(&Token::LParen) {
                    let (c_type, function_pointer_signature) =
                        self.parse_abstract_function_pointer_type(parsed_type)?;
                    ParsedParameter {
                        parameter: FunctionParameter {
                            click_type: ClickType::C(c_type),
                            name,
                            struct_name: None,
                            function_pointer_signature: Some(function_pointer_signature),
                            constant: false,
                            pointee_constant: false,
                        },
                        struct_name: None,
                        declared_bytes: None,
                        struct_array: false,
                    }
                } else {
                    self.parse_parameter_array_suffix(name, parsed_type)?
                }
            } else {
                ParsedParameter {
                    parameter: FunctionParameter {
                        click_type,
                        name,
                        struct_name: None,
                        function_pointer_signature: None,
                        constant: false,
                        pointee_constant: false,
                    },
                    struct_name: None,
                    declared_bytes: None,
                    struct_array: false,
                }
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

    fn parse_theorem_definition(&mut self) -> Result<TheoremDefinition, ClickError> {
        self.expect_ident_spelling("theorem")?;
        let name = self.expect_ident("theorem name")?;
        let type_parameters = self.parse_click_type_parameters()?;
        let previous_type_parameters = std::mem::replace(
            &mut self.current_click_type_parameters,
            type_parameters.iter().cloned().collect(),
        );
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        let executes = if self.peek_ident() == Some("executes") {
            self.position += 1;
            let callback = self.expect_ident("callback parameter")?;
            self.expect(Token::LParen)?;
            let call_parameters = self.parse_parameters()?;
            self.expect(Token::RParen)?;
            Some(TheoremExecution {
                callback,
                parameters: call_parameters.parameters,
            })
        } else {
            None
        };
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
        let previous_algebraic_params = std::mem::replace(
            &mut self.current_algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
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
                    let resource = self.parse_owned_resource_binding()?;
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
                    let resource = self.parse_owned_resource_binding()?;
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
                    let ensure = if let Some(execution) = &executes {
                        let mut names = parameter_names.clone();
                        names.extend(execution.parameters.iter().map(|p| p.name().to_string()));
                        names.extend(contract_let_names.iter().cloned());
                        self.parse_ensure_clause_with_execution_scope(Some(&names))?
                    } else {
                        self.parse_ensure_clause()?
                    };
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
        self.current_algebraic_params = previous_algebraic_params;
        self.current_click_type_parameters = previous_type_parameters;

        let requires: Vec<Requirement> = requires
            .into_iter()
            .flat_map(expand_aggregate_requirement)
            .collect();
        let ensures: Vec<EnsureClause> = ensures
            .into_iter()
            .flat_map(expand_aggregate_ensure_clause)
            .collect();

        Ok(TheoremDefinition {
            name,
            type_parameters,
            parameters: parsed_parameters.parameters,
            executes,
            requires,
            ensures,
        })
    }

    fn parse_function_block(&mut self, external: bool) -> Result<FunctionBlock, ClickError> {
        let previous_resource_targets = std::mem::replace(
            &mut self.current_resource_targets,
            self.contract_resource_parameters.clone(),
        );
        let previous_resource_bindings = std::mem::take(&mut self.current_resource_bindings);
        for (name, parameter) in &self.contract_resource_parameters {
            let ResourceClause::Named { binding, resource } = parameter else {
                unreachable!()
            };
            let ResourceClause::Declared {
                name: resource_name,
                ..
            } = resource.as_ref()
            else {
                unreachable!()
            };
            self.current_resource_bindings
                .insert(name.clone(), (binding.identity, resource_name.clone()));
        }
        if external {
            self.expect_ident_spelling("extern")?;
        }
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
        let aggregate_objects = self
            .aggregate_objects_by_function
            .get(signature.name())
            .cloned()
            .unwrap_or_default();
        let previous_aggregate_objects =
            std::mem::replace(&mut self.current_aggregate_objects, aggregate_objects);
        // A parameter shadowing a file-scope array hides it inside this
        // function, for indexing shapes and element widths alike.
        let global_array_shapes = self
            .global_array_shapes_by_function
            .get(signature.name())
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|(name, _)| !parameter_names.contains(name))
            .collect();
        let previous_global_array_shapes =
            std::mem::replace(&mut self.current_global_array_shapes, global_array_shapes);
        let mut visible_struct_array_params = struct_array_params;
        if let Some(aggregate_array_objects) = self
            .aggregate_array_objects_by_function
            .get(signature.name())
        {
            visible_struct_array_params.extend(
                aggregate_array_objects
                    .iter()
                    .filter(|name| !parameter_names.contains(*name))
                    .cloned(),
            );
        }
        let previous_struct_array_params = std::mem::replace(
            &mut self.current_struct_array_params,
            visible_struct_array_params,
        );
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
                    let resource = self.parse_owned_resource_binding()?;
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
                    let resource = self.parse_owned_resource_binding()?;
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
                    let resource = self.parse_owned_resource_binding()?;
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
        if external {
            if decreases.is_some()
                || grouped_proof.is_some()
                || ensures
                    .iter()
                    .any(|ensure| !matches!(ensure.proof(), SourceProof::Default))
                || effects
                    .iter()
                    .any(|effect| !matches!(effect.proof(), SourceProof::Default))
            {
                return Err(self
                    .error("external function contracts cannot carry proof or decreases clauses"));
            }
        }
        self.current_struct_params = previous_struct_params;
        self.current_resource_bindings = previous_resource_bindings;
        self.current_resource_targets = previous_resource_targets;
        self.current_aggregate_objects = previous_aggregate_objects;
        self.current_global_array_shapes = previous_global_array_shapes;
        self.current_struct_array_params = previous_struct_array_params;

        let requires: Vec<Requirement> = requires
            .into_iter()
            .flat_map(expand_aggregate_requirement)
            .collect();
        let constructs: Vec<ResourceClause> = constructs
            .into_iter()
            .flat_map(expand_aggregate_resource_clause)
            .collect();
        let ensures: Vec<EnsureClause> = ensures
            .into_iter()
            .flat_map(expand_aggregate_ensure_clause)
            .collect();

        let mut object_alignment_facts = Vec::new();
        for requirement in &requires {
            requirement_object_alignment_facts(
                requirement,
                &self.struct_layouts,
                &mut object_alignment_facts,
            );
        }
        let mut requires = requires;
        requires.extend(
            object_alignment_facts
                .into_iter()
                .map(Requirement::Proposition),
        );
        let requirement_label_indices = requires
            .iter()
            .enumerate()
            .filter_map(|(index, requirement)| {
                requirement.label().map(|label| (label.to_string(), index))
            })
            .collect();

        Ok(FunctionBlock {
            signature,
            external,
            one_call_proof: false,
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
        let click_type = if self.peek() == Some(&Token::Colon) {
            self.position += 1;
            let (click_type, parsed_type) = self.parse_click_type()?;
            if let Some(parsed_type) = parsed_type
                && parsed_type.struct_name.is_some()
                && !parsed_type.struct_pointer
            {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            Some(click_type)
        } else {
            None
        };
        let kind = if self.peek() == Some(&Token::Equal) {
            self.position += 1;
            ContractLetBindingKind::Value(self.parse_contract_expression()?)
        } else if self.peek_ident() == Some("where") {
            self.position += 1;
            if click_type.is_none() {
                return Err(self.error("`let ... where` requires an explicit type annotation"));
            }
            ContractLetBindingKind::Where(self.parse_proposition()?)
        } else {
            return Err(self.error("expected `=` or `where` in `let` binding"));
        };
        self.expect(Token::Semicolon)?;
        Ok(ContractLetBinding {
            name,
            click_type,
            kind,
        })
    }

    fn parse_function_signature(&mut self) -> Result<ParsedFunctionSignature, ClickError> {
        let parsed_return_type = self.parse_type()?;
        if parsed_return_type.constant {
            return Err(
                self.error("const-qualified function return types are not supported in this slice")
            );
        }
        let return_type = if let Some(struct_name) = parsed_return_type
            .struct_name
            .as_deref()
            .filter(|_| !parsed_return_type.struct_pointer)
        {
            self.scalar_struct_value_type(struct_name)?
        } else {
            parsed_return_type.c_type
        };
        let name = match self.pending_contract_name.take() {
            Some(name) => name,
            None => self.expect_ident("function name")?,
        };
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let struct_params = parsed_parameters.struct_params;
        let struct_array_params = parsed_parameters.struct_array_params;

        Ok(ParsedFunctionSignature {
            signature: FunctionSignature {
                return_type,
                return_pointee_constant: parsed_return_type.pointee_constant,
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
                let (name, c_type, function_pointer_signature) =
                    self.parse_function_pointer_declarator(parsed_type.clone())?;
                ParsedParameter {
                    parameter: FunctionParameter {
                        click_type: ClickType::C(c_type),
                        name,
                        struct_name: None,
                        function_pointer_signature: Some(function_pointer_signature),
                        constant: false,
                        pointee_constant: false,
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
        let is_constant = if self.peek_ident() == Some("const") {
            self.position += 1;
            true
        } else {
            false
        };
        let spelling = self.expect_ident("type")?;
        if spelling == "struct" {
            let struct_name = self.expect_ident("struct name")?;
            let mut object_constant = is_constant;
            if self.peek_ident() == Some("const") {
                self.position += 1;
                object_constant = true;
            }
            if self.peek() == Some(&Token::Star) {
                let mut c_type = C0Type::Int32;
                let mut pointee_constant = false;
                let mut saw_pointer = false;
                while self.peek() == Some(&Token::Star) {
                    if saw_pointer && pointee_constant {
                        return Err(self.error(
                            "const qualification beyond the first pointer level is not supported",
                        ));
                    }
                    let base_constant = object_constant;
                    object_constant = false;
                    self.position += 1;
                    c_type = match c_type {
                        C0Type::Int32 => C0Type::Int32Pointer,
                        C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                        _ => return Err(self.error("pointer depth beyond `**` is not supported")),
                    };
                    pointee_constant = base_constant;
                    if self.peek_ident() == Some("const") {
                        self.position += 1;
                        object_constant = true;
                    }
                    saw_pointer = true;
                }
                return Ok(ParsedType {
                    c_type,
                    struct_name: Some(struct_name),
                    struct_pointer: true,
                    constant: object_constant,
                    pointee_constant,
                });
            }
            return Ok(ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(struct_name),
                struct_pointer: false,
                constant: object_constant,
                pointee_constant: false,
            });
        }

        let scalar_type = match spelling.as_str() {
            "void" => C0Type::Void,
            "int16" | "short" | "int16_t" => C0Type::Int16,
            "int32" | "int" | "int32_t" => C0Type::Int32,
            "uint8" | "uint8_t" => C0Type::UInt8,
            "uint16" | "uint16_t" => C0Type::UInt16,
            "uint32" | "uint32_t" => C0Type::UInt32,
            "int64" | "int64_t" | "ssize_t" => C0Type::Int64,
            "long" => {
                if self.peek_ident() == Some("double") {
                    return Err(self.error(
                        "unsupported C type `long double`: extended-precision floating-point values are not modeled in C0",
                    ));
                }
                C0Type::Int64
            }
            "uint64" | "unsigned long" | "size_t" | "uint64_t" => C0Type::UInt64,
            "float" => C0Type::Float32,
            "double" => C0Type::Float64,
            "unsigned" => {
                if self.peek_ident() == Some("char") {
                    self.position += 1;
                    C0Type::UInt8
                } else if self.peek_ident() == Some("int") {
                    self.position += 1;
                    C0Type::UInt32
                } else if self.peek_ident() == Some("short") {
                    self.position += 1;
                    C0Type::UInt16
                } else if self.peek_ident() == Some("long") {
                    self.position += 1;
                    C0Type::UInt64
                } else {
                    return Err(self.error(
                        "unsupported integer width `unsigned`; only `unsigned char`, `unsigned short`, and `unsigned int` are modeled",
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
                if self.peek_ident() == Some("short") {
                    self.position += 1;
                    C0Type::Int16
                } else if self.peek_ident() == Some("long") {
                    self.position += 1;
                    C0Type::Int64
                } else {
                    return Err(self.error(
                        "unsupported integer width `signed`; only `signed short` is modeled among signed standard aliases",
                    ));
                }
            }
            "char" => C0Type::Char,
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
        let mut object_constant = is_constant;
        let mut pointee_constant = false;
        if self.peek_ident() == Some("const") {
            self.position += 1;
            object_constant = true;
        }
        let mut saw_pointer = false;
        while self.peek() == Some(&Token::Star) {
            if saw_pointer && pointee_constant {
                return Err(self
                    .error("const qualification beyond the first pointer level is not supported"));
            }
            let base_constant = object_constant;
            object_constant = false;
            self.position += 1;
            c_type = match c_type {
                C0Type::Void => C0Type::VoidPointer,
                C0Type::Int16 => C0Type::Int16Pointer,
                C0Type::UInt16 => C0Type::UInt16Pointer,
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::Char => C0Type::CharPointer,
                C0Type::UInt8 => C0Type::UInt8Pointer,
                C0Type::UInt32 => C0Type::UInt32Pointer,
                C0Type::Int64 => C0Type::Int64Pointer,
                C0Type::UInt64 => C0Type::UInt64Pointer,
                C0Type::Int16Pointer => C0Type::Int16PointerPointer,
                C0Type::UInt16Pointer => C0Type::UInt16PointerPointer,
                C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                C0Type::CharPointer => C0Type::CharPointerPointer,
                C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
                C0Type::UInt32Pointer => C0Type::UInt32PointerPointer,
                C0Type::Int64Pointer => C0Type::Int64PointerPointer,
                C0Type::UInt64Pointer => C0Type::UInt64PointerPointer,
                _ => return Err(self.error("pointer depth beyond `**` is not supported")),
            };
            if base_constant {
                pointee_constant = true;
            }
            if self.peek_ident() == Some("const") {
                self.position += 1;
                object_constant = true;
            }
            saw_pointer = true;
        }
        Ok(ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
            constant: object_constant,
            pointee_constant,
        })
    }

    fn parse_click_type(&mut self) -> Result<(ClickType, Option<ParsedType>), ClickError> {
        let Some(name) = self.peek_ident() else {
            return Err(self.error("expected Click type"));
        };
        if is_c_type_keyword(name) {
            let parsed = self.parse_type()?;
            return Ok((ClickType::C(parsed.c_type), Some(parsed)));
        }
        if self.current_click_type_parameters.contains(name) {
            let name = name.to_string();
            self.position += 1;
            return Ok((ClickType::Parameter(name), None));
        }
        let application = self.parse_algebraic_type_application()?;
        Ok((ClickType::Algebraic(application), None))
    }

    fn parse_click_type_parameters(&mut self) -> Result<Vec<String>, ClickError> {
        if self.peek() != Some(&Token::LessThan) {
            return Ok(Vec::new());
        }
        self.position += 1;
        let mut parameters = Vec::new();
        loop {
            parameters.push(self.expect_ident("type parameter")?);
            match self.peek() {
                Some(Token::Comma) => self.position += 1,
                Some(Token::GreaterThan) => {
                    self.position += 1;
                    break;
                }
                Some(token) => {
                    return Err(self.error(format!(
                        "expected `,` or `>` after type parameter, got {}",
                        token.describe()
                    )));
                }
                None => return Err(self.error("expected `>` after type parameters")),
            }
        }
        Ok(parameters)
    }

    fn scalar_struct_value_type(&self, struct_name: &str) -> Result<C0Type, ClickError> {
        let layout = self
            .struct_layouts
            .get(struct_name)
            .ok_or_else(|| self.error(format!("unknown struct declaration `{struct_name}`")))?;
        for field in layout.fields().values() {
            if field.union_name().is_some() {
                continue;
            }
            if let Some(nested_name) = field.struct_name()
                && field.array_element_width().is_some()
                && field.array_shape().is_some()
            {
                self.scalar_struct_value_type(nested_name)?;
                continue;
            }
            if field.c_type() == C0Type::Int32
                && field.struct_name().is_some()
                && field.array_element_width().is_none()
            {
                self.scalar_struct_value_type(
                    field
                        .struct_name()
                        .expect("embedded struct field has a struct name"),
                )?;
                continue;
            }
            if field.union_name().is_some()
                || (field.struct_name().is_some() && !field.c_type().is_pointer())
                || !matches!(
                    field.c_type(),
                    C0Type::Int16
                        | C0Type::Int32
                        | C0Type::Char
                        | C0Type::UInt8
                        | C0Type::UInt16
                        | C0Type::UInt32
                        | C0Type::Int64
                        | C0Type::UInt64
                        | C0Type::Float32
                        | C0Type::Float64
                        | C0Type::Int32Array(_)
                        | C0Type::CharArray(_)
                        | C0Type::UInt8Array(_)
                        | C0Type::Float32Array(_)
                        | C0Type::Float64Array(_)
                        | C0Type::Int32Pointer
                        | C0Type::CharPointer
                        | C0Type::UInt8Pointer
                        | C0Type::Float32Pointer
                        | C0Type::Float64Pointer
                        | C0Type::Int32PointerPointer
                        | C0Type::CharPointerPointer
                        | C0Type::UInt8PointerPointer
                        | C0Type::Float32PointerPointer
                        | C0Type::Float64PointerPointer
                )
            {
                return Err(self.error(format!(
                    "struct-by-value currently supports modeled integer and floating-point fields, fixed scalar arrays, fixed-dimensional embedded-struct arrays, data-pointer fields, embedded struct fields, and named union fields; `struct {struct_name}` contains a function pointer or unsupported field shape"
                )));
            }
        }
        Ok(C0Type::UInt8Array(layout.size_bytes()))
    }

    fn parse_function_pointer_declarator(
        &mut self,
        return_type: ParsedType,
    ) -> Result<(String, C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        if return_type.struct_name.is_some() && !return_type.struct_pointer {
            return Err(self.error(
                "function-pointer return values must use modeled scalars or struct pointers",
            ));
        }
        self.expect(Token::LParen)?;
        self.expect(Token::Star)?;
        let name = self.expect_ident("function-pointer parameter name")?;
        self.expect(Token::RParen)?;
        let (c_type, function_pointer_signature) =
            self.parse_function_pointer_signature_tail(return_type)?;
        Ok((name, c_type, function_pointer_signature))
    }

    /// Parses the nameless C declarator used as a Click-native binder type:
    /// `callback: int32 (*)(int32, int32)`.
    fn parse_abstract_function_pointer_type(
        &mut self,
        return_type: ParsedType,
    ) -> Result<(C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        if return_type.struct_name.is_some() && !return_type.struct_pointer {
            return Err(self.error(
                "function-pointer return values must use modeled scalars or struct pointers",
            ));
        }
        self.expect(Token::LParen)?;
        self.expect(Token::Star)?;
        self.expect(Token::RParen)?;
        self.parse_function_pointer_signature_tail(return_type)
    }

    fn parse_function_pointer_signature_tail(
        &mut self,
        return_type: ParsedType,
    ) -> Result<(C0Type, syntax::C0FunctionPointerSignature), ClickError> {
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                let parsed_type = self.parse_type()?;
                if parsed_type.c_type == C0Type::Void {
                    return Err(self.error("function-pointer parameters cannot have type `void`"));
                }
                if parsed_type.struct_name.is_some() && !parsed_type.struct_pointer {
                    return Err(
                        self.error("function-pointer parameters cannot pass structs by value")
                    );
                }
                let parameter_name = if matches!(self.peek(), Some(Token::Ident(_))) {
                    self.expect_ident("function-pointer parameter name")?
                } else {
                    "__click_callback_parameter".to_string()
                };
                let parsed_parameter =
                    self.parse_parameter_array_suffix(parameter_name, parsed_type)?;
                parameters.push(syntax::C0FunctionPointerParameter::new(
                    parsed_parameter.parameter.c_type(),
                    parsed_parameter.struct_name,
                    parsed_parameter.parameter.pointee_is_constant(),
                ));
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
        if parameters.len() > 13 {
            return Err(self.error("function-pointer signatures support at most 13 parameters"));
        }
        let parameter_types = parameters
            .iter()
            .map(|parameter| {
                (
                    parameter.c_type().to_kernel_type(),
                    parameter.pointee_is_constant(),
                )
            })
            .collect::<Vec<_>>();
        let signature = crate::kernel::CType::qualified_function_pointer_signature(
            return_type.c_type.to_kernel_type(),
            return_type.pointee_constant,
            &parameter_types,
        );
        if signature == crate::kernel::CallbackSignature::UNSPECIFIED {
            return Err(self.error("function-pointer signature uses an unsupported modeled type"));
        }
        let function_pointer_signature = syntax::C0FunctionPointerSignature::new(
            return_type.c_type,
            return_type.struct_name,
            parameters,
            return_type.pointee_constant,
        );
        Ok((
            C0Type::FunctionPointer(signature),
            function_pointer_signature,
        ))
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
            let c_type = if let Some(struct_name) = struct_name.as_deref()
                && !parsed_type.struct_pointer
            {
                self.scalar_struct_value_type(struct_name)?
            } else {
                parsed_type.c_type
            };
            return Ok(ParsedParameter {
                parameter: FunctionParameter {
                    click_type: ClickType::C(c_type),
                    name,
                    struct_name: struct_name.clone(),
                    function_pointer_signature: None,
                    constant: parsed_type.constant,
                    pointee_constant: parsed_type.pointee_constant,
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
                    click_type: ClickType::C(C0Type::Int32Pointer),
                    name,
                    struct_name: struct_name.clone(),
                    function_pointer_signature: None,
                    constant: false,
                    pointee_constant: parsed_type.constant || parsed_type.pointee_constant,
                },
                struct_name,
                declared_bytes: None,
                struct_array: true,
            });
        }
        let (pointer_type, element_width) = match parsed_type.c_type {
            C0Type::Int16 => (C0Type::Int16Pointer, 2),
            C0Type::Int32 => (C0Type::Int32Pointer, 4),
            C0Type::Char => (C0Type::CharPointer, 1),
            C0Type::UInt8 => (C0Type::UInt8Pointer, 1),
            C0Type::UInt16 => (C0Type::UInt16Pointer, 2),
            C0Type::UInt32 => (C0Type::UInt32Pointer, 4),
            C0Type::Int64 => (C0Type::Int64Pointer, 8),
            C0Type::UInt64 => (C0Type::UInt64Pointer, 8),
            C0Type::Int16Pointer => (C0Type::Int16PointerPointer, 8),
            C0Type::UInt16Pointer => (C0Type::UInt16PointerPointer, 8),
            C0Type::Int32Pointer => (C0Type::Int32PointerPointer, 8),
            C0Type::CharPointer => (C0Type::CharPointerPointer, 8),
            C0Type::UInt8Pointer => (C0Type::UInt8PointerPointer, 8),
            C0Type::UInt32Pointer => (C0Type::UInt32PointerPointer, 8),
            C0Type::Int64Pointer => (C0Type::Int64PointerPointer, 8),
            C0Type::UInt64Pointer => (C0Type::UInt64PointerPointer, 8),
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
                click_type: ClickType::C(pointer_type),
                name,
                struct_name: None,
                function_pointer_signature: None,
                constant: false,
                pointee_constant: parsed_type.constant || parsed_type.pointee_constant,
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
        let segments = self.parse_current_contract_segments()?;
        if segments.len() > 1 {
            return Ok(ResourceClause::MemoryAggregate { access, segments });
        }
        let segment = segments
            .into_iter()
            .next()
            .expect("resource target parser returns at least one segment");
        Ok(match access {
            ResourceAccessMode::Own => ResourceClause::OwnMemory(segment),
            ResourceAccessMode::View => ResourceClause::ViewMemory(segment),
        })
    }

    fn parse_owned_resource_binding(&mut self) -> Result<ResourceClause, ClickError> {
        if let Some(name) = self.peek_ident()
            && self.peek_next() != Some(&Token::Colon)
            && let Some(parameter) = self.contract_resource_parameters.get(name).cloned()
        {
            self.position += 1;
            return Ok(parameter);
        }
        if !matches!(self.peek(), Some(Token::Ident(_))) || self.peek_next() != Some(&Token::Colon)
        {
            return self.parse_owned_resource_target();
        }
        let name = self.expect_ident("resource instance name")?;
        self.expect(Token::Colon)?;
        if self.current_resource_bindings.contains_key(&name)
            || self.current_contract_bindings.contains(&name)
        {
            return Err(self.error(format!("duplicate resource instance binding `{name}`")));
        }
        let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
        let ResourceClause::Declared {
            name: resource_name,
            ..
        } = &resource
        else {
            return Err(self.error("named ownership requires a field-bearing declared resource"));
        };
        let identity = Variable(self.next_resource_identity);
        self.next_resource_identity += 1;
        self.current_resource_bindings
            .insert(name.clone(), (identity, resource_name.clone()));
        let target = ResourceClause::Named {
            binding: ResourceInstanceBinding {
                name: name.clone(),
                identity,
                children: vec![],
                schema: None,
                fields: None,
                fold_fields: None,
                child_bindings: None,
            },
            resource: Box::new(resource),
        };
        self.current_resource_targets.insert(name, target.clone());
        Ok(target)
    }

    fn parse_owned_resource_target(&mut self) -> Result<ResourceClause, ClickError> {
        if let Some(mut target) = self
            .peek_ident()
            .and_then(|name| self.current_resource_targets.get(name))
            .cloned()
        {
            self.position += 1;
            while self.peek() == Some(&Token::Dot) {
                self.position += 1;
                let child = self.expect_ident("child resource name")?;
                let ResourceClause::Named { binding, .. } = &mut target else {
                    return Err(self.error("child access requires a named resource"));
                };
                binding.name.push('.');
                binding.name.push_str(&child);
                binding.children.push(child);
            }
            return Ok(target);
        }
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
        self.parse_ensure_clause_with_execution_scope(None)
    }

    fn parse_ensure_clause_with_execution_scope(
        &mut self,
        execution_names: Option<&BTreeSet<String>>,
    ) -> Result<EnsureClause, ClickError> {
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
        let previous = execution_names.map(|_| std::mem::take(&mut self.current_resource_bindings));
        if let Some(names) = execution_names
            && let Ensure::Proposition(ClickProposition::PredicateCall { name, .. }) = &ensure
            && let Some(bindings) = self.contract_proof_bindings.get(name)
        {
            for (name, identity, resource) in bindings {
                crate::instrumentation::record_deterministic_work(1);
                if name == "result" || names.contains(name) {
                    return Err(self.error(format!("target resource parameter `{name}` conflicts with an execution proof binding")));
                }
                self.current_resource_bindings
                    .insert(name.clone(), (*identity, resource.clone()));
            }
        }
        let proof = self.parse_proof_clause_or_default()?;
        if let Some(previous) = previous {
            self.current_resource_bindings = previous;
        }

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
            let Some(click_type) = binding.click_type else {
                unreachable!("`let ... where` parser requires an explicit type")
            };
            let ClickType::C(c_type) = click_type else {
                return Err(self.error(
                    "`let ... where` quantifies a C value; algebraic quantifiers are not supported yet",
                ));
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

        if self.peek_ident() == Some("aligned") && self.peek_next() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::LParen)?;
            let pointer = self.parse_contract_expression()?;
            let Some(pointer) = contract_expression_as_c_fragment(&pointer) else {
                return Err(self.error("aligned expects a current C pointer expression"));
            };
            self.expect(Token::Comma)?;
            let alignment = match self.next() {
                Some(Token::Number(alignment)) if alignment.is_power_of_two() => alignment,
                Some(token) => {
                    return Err(self.error(format!(
                        "aligned expects a power-of-two byte alignment, got {token:?}"
                    )));
                }
                None => {
                    return Err(self
                        .error("aligned expects a power-of-two byte alignment, got end of input"));
                }
            };
            self.expect(Token::RParen)?;
            return Ok(aligned_proposition(pointer, u64::from(alignment)));
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
                Some(
                    "load_int32"
                        | "load_uint8"
                        | "load_int32_pointer"
                        | "load_uint8_pointer"
                        | "address"
                        | "byte_offset"
                )
            )
            && self.peek_next() == Some(&Token::LParen)
        {
            let start = self.position;
            let (name, arguments) = self.parse_call_arguments("predicate or function name")?;
            if let Some(classification) = float_classification_from_name(&name) {
                let [expression] = arguments.as_slice() else {
                    return Err(self.error(format!(
                        "floating-point classification `{name}` expects one argument"
                    )));
                };
                return Ok(ClickProposition::FloatClassification {
                    expression: expression.clone(),
                    classification,
                });
            }
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
            Token::Ident(operator) if operator == "in" => Ok(ComparisonOperator::In),
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

    fn parse_resource_child_bindings(
        &mut self,
        parent: &ResourceClause,
        introduce: bool,
    ) -> Result<Vec<(String, String, Variable)>, ClickError> {
        let ResourceClause::Declared { name: family, .. } = parent else {
            return Err(self.error("child bindings require a declared resource family"));
        };
        self.expect(Token::LBrace)?;
        let mut result = Vec::new();
        let mut slots = BTreeSet::new();
        let mut names = BTreeSet::new();
        while self.peek() != Some(&Token::RBrace) {
            let slot = self.expect_ident("child slot")?;
            self.expect(Token::Colon)?;
            let name = self.expect_ident("child resource name")?;
            if !slots.insert(slot.clone()) || !names.insert(name.clone()) {
                return Err(self.error("duplicate child slot or resource name"));
            }
            if self.current_contract_bindings.contains(&name) {
                return Err(self.error("child resource name conflicts with a C or pure binding"));
            }
            let identity =
                if let Some((identity, existing)) = self.current_resource_bindings.get(&name) {
                    if existing != family {
                        return Err(self.error("child resource has the wrong family"));
                    }
                    *identity
                } else if introduce {
                    let identity = Variable(self.next_resource_identity);
                    self.next_resource_identity += 1;
                    identity
                } else {
                    return Err(self.error(format!("unknown child resource `{name}`")));
                };
            if introduce {
                self.current_resource_bindings
                    .insert(name.clone(), (identity, family.clone()));
                self.current_resource_targets.insert(
                    name.clone(),
                    ResourceClause::Named {
                        binding: ResourceInstanceBinding {
                            name: name.clone(),
                            identity,
                            children: Vec::new(),
                            schema: None,
                            fields: None,
                            fold_fields: None,
                            child_bindings: Some(Vec::new().into()),
                        },
                        resource: Box::new(parent.clone()),
                    },
                );
            }
            result.push((slot, name, identity));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RBrace)?;
        Ok(result)
    }

    fn parse_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let name = self.expect_ident("tactic")?;
        match name.as_str() {
            "let" => {
                let name = self.expect_ident("fold result name")?;
                self.expect(Token::Equal)?;
                self.expect_ident_spelling("fold")?;
                self.expect(Token::LParen)?;
                let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
                let ResourceClause::Declared {
                    name: resource_name,
                    ..
                } = &resource
                else {
                    return Err(self.error("fold construction requires a declared resource"));
                };
                if self.current_contract_bindings.contains(&name) {
                    return Err(self.error("fold result conflicts with a C or pure binding"));
                }
                let identity =
                    if let Some((identity, previous)) = self.current_resource_bindings.get(&name) {
                        if previous != resource_name {
                            return Err(self.error("fold result changes the named resource family"));
                        }
                        *identity
                    } else {
                        let identity = Variable(self.next_resource_identity);
                        self.next_resource_identity += 1;
                        identity
                    };
                self.expect(Token::Comma)?;
                self.expect(Token::LBrace)?;
                let mut fields = Vec::new();
                while self.peek() != Some(&Token::RBrace) {
                    let field = self.expect_ident("resource field name")?;
                    self.expect(Token::Colon)?;
                    let value = self.parse_contract_expression()?;
                    fields.push((field, value));
                    if self.peek() != Some(&Token::Comma) {
                        break;
                    }
                    self.position += 1;
                }
                self.expect(Token::RBrace)?;
                let child_bindings = if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                    self.parse_resource_child_bindings(&resource, false)?
                } else {
                    Vec::new()
                };
                self.expect(Token::RParen)?;
                self.expect(Token::Semicolon)?;
                let binding = ResourceInstanceBinding {
                    name: name.clone(),
                    identity,
                    children: vec![],
                    schema: None,
                    fields: None,
                    fold_fields: None,
                    child_bindings: Some(Vec::new().into()),
                };
                self.current_resource_bindings
                    .insert(name.clone(), (identity, resource_name.clone()));
                self.current_resource_targets.insert(
                    name,
                    ResourceClause::Named {
                        binding: binding.clone(),
                        resource: Box::new(resource.clone()),
                    },
                );
                Ok(ProofTactic::FoldResource(ResourceClause::Named {
                    binding: ResourceInstanceBinding {
                        fold_fields: Some(fields),
                        child_bindings: Some(child_bindings.into()),
                        ..binding
                    },
                    resource: Box::new(resource),
                }))
            }
            "both" => self.parse_both_proof_tactic(),
            "close_invariants" if self.peek_ident() == Some("by") => {
                self.position += 1;
                let body = self.parse_possibly_empty_tactic_block()?;
                if self.peek() == Some(&Token::Semicolon) {
                    self.position += 1;
                }
                Ok(ProofTactic::CloseInvariantsBy(body))
            }
            _ => self.parse_other_proof_tactic(name),
        }
    }

    #[inline(never)]
    fn parse_both_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let left_tactics = self.parse_possibly_empty_tactic_block()?;
        self.expect_ident_spelling("and")?;
        let right_tactics = self.parse_possibly_empty_tactic_block()?;
        if self.peek() == Some(&Token::Semicolon) {
            self.position += 1;
        }
        Ok(ProofTactic::Both(ProofBoth {
            left_tactics,
            right_tactics,
        }))
    }

    // Conjunction spines do not retain the larger frames for loop, resource,
    // and leaf syntax at every child-proof level.
    #[inline(never)]
    fn parse_other_proof_tactic(&mut self, name: String) -> Result<ProofTactic, ClickError> {
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
        if name == "match" {
            let scrutinee = self.parse_contract_expression()?;
            self.expect(Token::LBrace)?;
            let mut arms = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                let type_name = self.expect_ident("match pattern datatype")?;
                self.expect(Token::ColonColon)?;
                let variant = self.expect_ident("match pattern variant")?;
                let mut bindings = Vec::new();
                let mut binding_names = BTreeSet::new();
                if self.peek() == Some(&Token::LParen) {
                    self.position += 1;
                    while self.peek() != Some(&Token::RParen) {
                        let binding = self.expect_ident("match pattern binding")?;
                        if !binding_names.insert(binding.clone()) {
                            return Err(self.error(format!("duplicate match binding `{binding}`")));
                        }
                        bindings.push(binding);
                        if self.peek() != Some(&Token::Comma) {
                            break;
                        }
                        self.position += 1;
                    }
                    self.expect(Token::RParen)?;
                }
                self.expect(Token::FatArrow)?;
                let newly_bound = bindings
                    .iter()
                    .filter(|name| self.current_contract_bindings.insert((*name).clone()))
                    .cloned()
                    .collect::<Vec<_>>();
                let tactics = self.parse_possibly_empty_tactic_block();
                for name in newly_bound {
                    self.current_contract_bindings.remove(&name);
                }
                arms.push(ProofInductionArm {
                    type_name,
                    variant,
                    bindings,
                    tactics: tactics?,
                });
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
            }
            self.expect(Token::RBrace)?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::Match(Box::new(ProofMatch { scrutinee, arms })));
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
            let mut resources = Vec::new();
            let mut decreases = None;
            let mut initialize_proof = None;
            let mut preserve_proof = None;
            while self.peek() != Some(&Token::RBrace) {
                // A loop declares resources exactly as a contract does. They
                // bound the body's authority and the loop's write footprint,
                // so they are region declarations rather than proof items.
                if self.peek_ident() == Some("owns") {
                    self.position += 1;
                    let resource = self.parse_owned_resource_target()?;
                    self.expect(Token::Semicolon)?;
                    resources.push(resource);
                    continue;
                }
                if self.peek_ident() == Some("views") {
                    self.position += 1;
                    let resource = self.parse_resource_target(ResourceAccessMode::View)?;
                    self.expect(Token::Semicolon)?;
                    resources.push(resource);
                    continue;
                }
                if self.peek_ident() == Some("decreases") {
                    self.position += 1;
                    if decreases.is_some() {
                        return Err(self.error("duplicate loop `decreases` clause"));
                    }
                    decreases = Some(self.parse_termination_measure()?);
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
            if items.is_empty() && decreases.is_none() && resources.is_empty() {
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
                resources,
                initialize_proof,
                preserve_proof,
            }));
        }
        self.parse_named_proof_tactic(name)
    }

    // Keep the large leaf-tactic dispatch frame out of recursive proof-body
    // parsing. Expanded both/if/closure scopes can nest while reading terms.
    #[inline(never)]
    fn parse_named_proof_tactic(&mut self, name: String) -> Result<ProofTactic, ClickError> {
        let tactic = match name.as_str() {
            "step" => {
                self.expect(Token::LParen)?;
                let step = if self.peek() == Some(&Token::RParen) {
                    ProofTactic::Step
                } else {
                    let name = self.expect_ident("call contract name")?;
                    let arguments = if self.peek() == Some(&Token::LParen) {
                        self.position += 1;
                        let mut arguments = Vec::new();
                        while self.peek() != Some(&Token::RParen) {
                            let name = self.expect_ident("owned resource argument")?;
                            let (identity, resource_name) = self
                                .current_resource_bindings
                                .get(&name)
                                .cloned()
                                .ok_or_else(|| {
                                    self.error(format!("unknown resource instance `{name}`"))
                                })?;
                            arguments.push(ContractResourceArgument {
                                name,
                                resource_name,
                                identity,
                            });
                            if self.peek() != Some(&Token::Comma) {
                                break;
                            }
                            self.position += 1;
                        }
                        self.expect(Token::RParen)?;
                        Some(arguments)
                    } else {
                        None
                    };
                    ProofTactic::StepContract(ContractApplication { name, arguments })
                };
                self.expect(Token::RParen)?;
                step
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
                let mut tactic = if self
                    .peek_ident()
                    .is_some_and(|name| self.current_resource_targets.contains_key(name))
                {
                    ProofTactic::UnfoldResource(self.parse_owned_resource_target()?)
                } else if matches!(self.peek(), Some(Token::Ident(_)))
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
                if self.peek_ident() == Some("as") {
                    self.position += 1;
                    let ProofTactic::UnfoldResource(ResourceClause::Named { binding, resource }) =
                        &mut tactic
                    else {
                        return Err(self.error("`as` requires a named resource unfold"));
                    };
                    binding.child_bindings =
                        Some(self.parse_resource_child_bindings(resource, true)?.into());
                }
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
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::NormalizeUsing(premises));
                }
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
                if self.peek() == Some(&Token::LBrace) {
                    self.position += 1;
                    let mut arms = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        let type_name = self.expect_ident("induction pattern datatype")?;
                        self.expect(Token::ColonColon)?;
                        let variant = self.expect_ident("induction pattern variant")?;
                        let mut bindings = Vec::new();
                        if self.peek() == Some(&Token::LParen) {
                            self.position += 1;
                            if self.peek() != Some(&Token::RParen) {
                                loop {
                                    bindings.push(self.expect_ident("induction pattern binding")?);
                                    match self.peek() {
                                        Some(Token::Comma) => self.position += 1,
                                        Some(Token::RParen) => break,
                                        Some(token) => {
                                            return Err(self.error(format!(
                                                "expected `,` or `)` after induction binding, got {}",
                                                token.describe()
                                            )));
                                        }
                                        None => {
                                            return Err(
                                                self.error("expected `)` after induction bindings")
                                            );
                                        }
                                    }
                                }
                            }
                            self.expect(Token::RParen)?;
                        }
                        self.expect(Token::FatArrow)?;
                        let newly_bound = bindings
                            .iter()
                            .filter(|binding| {
                                self.current_contract_bindings.insert((*binding).clone())
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        let tactics = self.parse_possibly_empty_tactic_block();
                        for binding in newly_bound {
                            self.current_contract_bindings.remove(&binding);
                        }
                        arms.push(ProofInductionArm {
                            type_name,
                            variant,
                            bindings,
                            tactics: tactics?,
                        });
                        if self.peek() == Some(&Token::Comma) {
                            self.position += 1;
                        }
                    }
                    self.expect(Token::RBrace)?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::StructuralInduct {
                        parameter,
                        hypothesis,
                        arms,
                    });
                }
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
        self.parse_contract_concat()
    }

    fn parse_contract_concat(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_bitwise_or()?;
        while self.peek() == Some(&Token::PlusPlus) {
            self.position += 1;
            let right = self.parse_contract_bitwise_or()?;
            expression = ContractExpression::SequenceConcat(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_termination_measure(&mut self) -> Result<TerminationMeasure, ClickError> {
        let components = if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            if self.peek() == Some(&Token::RParen) {
                return Err(self.error("termination measure cannot be empty"));
            }
            let mut components = vec![self.parse_contract_expression()?];
            while self.peek() == Some(&Token::Comma) {
                self.position += 1;
                components.push(self.parse_contract_expression()?);
            }
            self.expect(Token::RParen)?;
            components
        } else {
            vec![self.parse_contract_expression()?]
        };
        Ok(TerminationMeasure::new(components))
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
        let segments = self.parse_current_contract_segments_inner(false)?;
        let [segment] = segments.as_slice() else {
            return Err(
                self.error("aggregate contract segments are only supported in resource clauses")
            );
        };
        Ok(segment.clone())
    }

    fn parse_current_contract_segments(&mut self) -> Result<Vec<ContractSegment>, ClickError> {
        self.parse_current_contract_segments_inner(true)
    }

    fn parse_current_contract_segments_inner(
        &mut self,
        allow_aggregates: bool,
    ) -> Result<Vec<ContractSegment>, ClickError> {
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
            return Ok(vec![ContractSegment {
                state: ContractSegmentState::Current,
                base,
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(layout.size_bytes() / 4)),
                surface: ContractSegmentSurface::Object(struct_name.clone()),
            }]);
        }
        let (mut surface_base, mut base) = if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let (surface, expression) = self.parse_segment_primary()?;
            let base = match expression {
                CExpression::TypedLoad { pointer, .. } => *pointer,
                CExpression::Value(CValue::Pointer(_)) => {
                    let ContractExpression::CFragment(CExpression::Variable(name)) = &surface
                    else {
                        return Err(self
                            .error("memory segment base must be a current C pointer expression"));
                    };
                    let Some(address) = self
                        .qualified_object(name)
                        .and_then(|object| object.address.clone())
                    else {
                        return Err(self.error("cannot take the address of this C expression"));
                    };
                    address
                }
                expression => CExpression::AddressOf(Box::new(expression)),
            };
            let surface = CExpression::AddressOf(Box::new(
                contract_expression_as_c_fragment(&surface).expect("C segment base"),
            ));
            (ContractExpression::CFragment(surface), base)
        } else if matches!(
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
            self.parse_segment_primary()?
        };
        let mut struct_name = match &surface_base {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_struct_params
                .get(name)
                .or_else(|| self.current_aggregate_objects.get(name))
                .or_else(|| {
                    self.qualified_object(name)
                        .and_then(|object| object.struct_name.as_ref())
                })
                .cloned(),
            _ => None,
        };
        let mut union_name: Option<String> = None;
        let mut struct_array_element_width = match &surface_base {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name))
                if self.current_struct_array_params.contains(name) =>
            {
                struct_name
                    .as_ref()
                    .and_then(|name| self.struct_layouts.get(name))
                    .map(|layout| layout.size_bytes())
            }
            ContractExpression::CFragment(CExpression::Variable(name)) => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some() && object.array_shape.is_some())
                .and_then(|object| object.struct_name.as_ref())
                .and_then(|name| self.struct_layouts.get(name))
                .map(|layout| layout.size_bytes()),
            _ => None,
        };
        let mut struct_array_shape = match &surface_base {
            ContractExpression::CFragment(CExpression::Variable(name)) => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some())
                .and_then(|object| object.array_shape.clone()),
            _ => None,
        };
        let mut scalar_array_shape = match &surface_base {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_global_array_shapes
                .get(name)
                .map(|array| array.shape.clone())
                .or_else(|| {
                    self.qualified_object(name)
                        .and_then(|object| object.array_shape.clone())
                }),
            _ => None,
        };
        let mut indexed_scalar_field: Option<(String, u32, CType)> = None;
        let mut scalar_range_offset = None;
        while matches!(self.peek(), Some(Token::Arrow | Token::Dot))
            || (self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range())
        {
            if self.peek() == Some(&Token::LBracket) {
                self.position += 1;
                let index = self.parse_contract_expression()?;
                self.expect(Token::RBracket)?;
                let index = contract_expression_as_c_fragment(&index).ok_or_else(|| {
                    self.error("struct array indices must be current C expressions")
                })?;
                let surface_base_before_index = surface_base;
                if let Some(element_width) = struct_array_element_width {
                    let mut indexes = vec![index.clone()];
                    let mut surface_indexes = vec![ContractExpression::CFragment(index.clone())];
                    while struct_array_shape.is_some() && self.peek() == Some(&Token::LBracket) {
                        self.position += 1;
                        let next_index = self.parse_contract_expression()?;
                        self.expect(Token::RBracket)?;
                        let next_index = contract_expression_as_c_fragment(&next_index)
                            .ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                        indexes.push(next_index.clone());
                        surface_indexes.push(ContractExpression::CFragment(next_index));
                    }
                    let offset = if let Some(shape) = struct_array_shape.take() {
                        if indexes.len() != shape.len() {
                            return Err(self.error(format!(
                                "multidimensional struct array field requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        flatten_array_indices(indexes, &shape)
                    } else {
                        index
                    };
                    let stride = CExpression::Multiply(
                        Box::new(offset),
                        Box::new(CExpression::Value(int32(element_width))),
                    );
                    base = CExpression::Add(Box::new(base), Box::new(stride));
                    surface_base = surface_indexes
                        .into_iter()
                        .fold(surface_base_before_index, |base, index| {
                            ContractExpression::Index(Box::new(base), Box::new(index))
                        });
                    struct_array_element_width = None;
                    indexed_scalar_field = None;
                } else if let Some(shape) = struct_array_shape.take() {
                    let mut indexes = vec![index.clone()];
                    let mut surface_indexes = vec![ContractExpression::CFragment(index)];
                    while self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range()
                    {
                        self.position += 1;
                        let next_index = self.parse_contract_expression()?;
                        self.expect(Token::RBracket)?;
                        let next_index = contract_expression_as_c_fragment(&next_index)
                            .ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                        indexes.push(next_index.clone());
                        surface_indexes.push(ContractExpression::CFragment(next_index));
                    }
                    if indexes.len() != shape.len() {
                        return Err(self.error(format!(
                            "multidimensional scalar array field requires {} indices, got {}",
                            shape.len(),
                            indexes.len()
                        )));
                    }
                    let offset = flatten_array_indices(indexes, &shape);
                    base = CExpression::Add(Box::new(base), Box::new(offset));
                    surface_base = surface_indexes
                        .into_iter()
                        .fold(surface_base_before_index, |base, index| {
                            ContractExpression::Index(Box::new(base), Box::new(index))
                        });
                    struct_name = None;
                    union_name = None;
                    struct_array_element_width = None;
                } else if let Some(shape) = scalar_array_shape.take() {
                    let mut indexes = vec![index.clone()];
                    let mut surface_indexes = vec![ContractExpression::CFragment(index)];
                    while self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range()
                    {
                        self.position += 1;
                        let next_index = self.parse_contract_expression()?;
                        self.expect(Token::RBracket)?;
                        let next_index = contract_expression_as_c_fragment(&next_index)
                            .ok_or_else(|| {
                                self.error("global array indices must be current C expressions")
                            })?;
                        indexes.push(next_index.clone());
                        surface_indexes.push(ContractExpression::CFragment(next_index));
                    }
                    let has_following_range =
                        self.peek() == Some(&Token::LBracket) && self.contract_bracket_is_range();
                    if indexes.len() != shape.len() && !has_following_range {
                        return Err(self.error(format!(
                            "multidimensional global array requires {} indices, got {}",
                            shape.len(),
                            indexes.len()
                        )));
                    }
                    let offset = flatten_array_indices(indexes, &shape);
                    base = if has_following_range {
                        scalar_range_offset = Some(offset);
                        base
                    } else {
                        CExpression::Index(Box::new(base), Box::new(offset))
                    };
                    surface_base = surface_indexes
                        .into_iter()
                        .fold(surface_base_before_index, |base, index| {
                            ContractExpression::Index(Box::new(base), Box::new(index))
                        });
                    struct_name = None;
                    union_name = None;
                    struct_array_element_width = None;
                } else {
                    let surface_index = ContractExpression::CFragment(index.clone());
                    base = CExpression::Index(Box::new(base), Box::new(index));
                    surface_base = ContractExpression::Index(
                        Box::new(surface_base_before_index),
                        Box::new(surface_index),
                    );
                    struct_name = None;
                    union_name = None;
                    struct_array_shape = None;
                    scalar_array_shape = None;
                    indexed_scalar_field = None;
                }
                continue;
            }
            self.position += 1;
            let field_name = self.expect_ident("field name")?;
            if !matches!(
                self.peek(),
                Some(Token::Arrow | Token::Dot | Token::LBracket)
            ) {
                if let Some(base_union_name) = &union_name
                    && self.union_layouts.contains_key(base_union_name)
                {
                    let field = self.resolve_union_field_metadata(base_union_name, &field_name)?;
                    self.validate_field_place(&field)?;
                    return Ok(vec![Self::field_segment_from_metadata(
                        base,
                        &field_name,
                        &field,
                    )]);
                }
                if let Some(base_struct_name) = &struct_name
                    && self.struct_layouts.contains_key(base_struct_name)
                {
                    let field =
                        self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                    if field.struct_name.is_some() && !field.c_type.is_pointer() {
                        if !allow_aggregates {
                            return Err(self.error(
                                "aggregate struct fields are only supported in resource clauses",
                            ));
                        }
                        return self.aggregate_field_segments(base, &field_name, &field);
                    }
                    self.validate_field_place(&field)?;
                    return Ok(vec![Self::field_segment_from_metadata(
                        base,
                        &field_name,
                        &field,
                    )]);
                }
                return Ok(vec![self.resolve_field_segment(base, &field_name)?]);
            }
            let (
                lowered,
                next_struct_name,
                next_union_name,
                next_array_element_width,
                next_array_shape,
                field_memory_pointer,
            ) = if let Some(base_union_name) = &union_name
                && self.union_layouts.contains_key(base_union_name)
            {
                let field = self.resolve_union_field_metadata(base_union_name, &field_name)?;
                let pointer = self.offset_field_pointer(base, field.offset_bytes);
                let field_memory_pointer = field_has_direct_memory_place(&field);
                (
                    lowered_field_expression(pointer, &field),
                    field.struct_name,
                    None,
                    None,
                    None,
                    field_memory_pointer,
                )
            } else if let Some(base_struct_name) = &struct_name
                && self.struct_layouts.contains_key(base_struct_name)
            {
                let field = self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                let pointer = self.offset_field_pointer(base, field.offset_bytes);
                let field_memory_pointer = field_has_direct_memory_place(&field);
                indexed_scalar_field = scalar_array_field_element(&field)
                    .map(|(width, ty)| (field_name.clone(), width, ty));
                (
                    lowered_field_expression(pointer, &field),
                    field.struct_name,
                    field.union_name,
                    field.array_element_width,
                    field.array_shape,
                    field_memory_pointer,
                )
            } else {
                indexed_scalar_field = None;
                (
                    self.resolve_field_load(base, &field_name)?,
                    None,
                    None,
                    None,
                    None,
                    false,
                )
            };
            let range_base = if field_memory_pointer
                && self.peek() == Some(&Token::LBracket)
                && self.contract_bracket_is_range()
            {
                match &lowered {
                    // An inline array field already denotes its address and
                    // carries its element type; unwrapping it to the raw byte
                    // pointer would index the range in four-byte cells. Keep
                    // the typed base so the slice keeps the element width.
                    CExpression::TypedLoad {
                        value_type:
                            CType::Int32Array(_)
                            | CType::UInt8Array(_)
                            | CType::Int16Array(_)
                            | CType::UInt16Array(_)
                            | CType::UInt32Array(_)
                            | CType::Int64Array(_)
                            | CType::UInt64Array(_),
                        ..
                    } => None,
                    CExpression::TypedLoad { pointer, .. } => Some((**pointer).clone()),
                    _ => None,
                }
            } else {
                None
            };
            surface_base = ContractExpression::Field {
                base: Box::new(surface_base),
                field: field_name,
                lowered: lowered.clone(),
            };
            base = range_base.unwrap_or(lowered);
            struct_name = next_struct_name;
            union_name = next_union_name;
            struct_array_element_width = next_array_element_width;
            struct_array_shape = next_array_shape;
        }
        if let Some((name, element_width, element_type)) = indexed_scalar_field {
            return Ok(vec![ContractSegment {
                state: ContractSegmentState::Current,
                base,
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Field {
                    name,
                    element_width: Some(element_width),
                    element_type: Some(element_type),
                },
            }]);
        }
        self.expect(Token::LBracket)?;
        let start_expression = self.parse_contract_expression()?;
        let mut start = contract_expression_as_c_fragment(&start_expression)
            .ok_or_else(|| self.error("memory segment start must be a current C expression"))?;
        self.expect(Token::DotDot)?;
        let end_expression = self.parse_contract_expression()?;
        let mut end = contract_expression_as_c_fragment(&end_expression)
            .ok_or_else(|| self.error("memory segment end must be a current C expression"))?;
        self.expect(Token::RBracket)?;
        if let Some(offset) = scalar_range_offset {
            start = CExpression::Add(Box::new(offset.clone()), Box::new(start));
            end = CExpression::Add(Box::new(offset), Box::new(end));
        }
        Ok(vec![ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start,
            end,
            surface: ContractSegmentSurface::Range {
                base: surface_base,
                start: start_expression,
                end: end_expression,
            },
        }])
    }

    fn aggregate_field_segments(
        &self,
        base: CExpression,
        field_name: &str,
        field: &ResolvedField,
    ) -> Result<Vec<ContractSegment>, ClickError> {
        let Some(struct_name) = field.struct_name.as_deref() else {
            return Err(self.error(format!(
                "aggregate field `{field_name}` has no embedded struct layout"
            )));
        };
        if let Some(element_width) = field.array_element_width {
            let shape = field.array_shape.as_deref().ok_or_else(|| {
                self.error(format!(
                    "embedded struct array field `{field_name}` has no shape metadata"
                ))
            })?;
            let element_count = shape.iter().try_fold(1u32, |count, length| {
                count.checked_mul(*length).ok_or_else(|| {
                    self.error(format!(
                        "embedded struct array field `{field_name}` is too large"
                    ))
                })
            })?;
            let mut segments = Vec::new();
            for flat_index in 0..element_count {
                let element_offset = field
                    .offset_bytes
                    .checked_add(flat_index.checked_mul(element_width).ok_or_else(|| {
                        self.error(format!(
                            "embedded struct array field `{field_name}` offset overflows"
                        ))
                    })?)
                    .ok_or_else(|| {
                        self.error(format!(
                            "embedded struct array field `{field_name}` offset overflows"
                        ))
                    })?;
                let path = row_major_index_path(flat_index, shape);
                self.append_aggregate_leaf_segments(
                    &mut segments,
                    base.clone(),
                    struct_name,
                    element_offset,
                    &format!("{field_name}{path}"),
                )?;
            }
            return Ok(segments);
        }

        let mut segments = Vec::new();
        self.append_aggregate_leaf_segments(
            &mut segments,
            base,
            struct_name,
            field.offset_bytes,
            field_name,
        )?;
        Ok(segments)
    }

    fn append_aggregate_leaf_segments(
        &self,
        segments: &mut Vec<ContractSegment>,
        base: CExpression,
        struct_name: &str,
        base_offset: u32,
        name_prefix: &str,
    ) -> Result<(), ClickError> {
        let layout = self.struct_layouts.get(struct_name).ok_or_else(|| {
            self.error(format!(
                "unknown embedded struct declaration `{struct_name}`"
            ))
        })?;
        let mut fields = layout.fields().iter().collect::<Vec<_>>();
        fields.sort_by_key(|(name, field)| (field.offset_bytes(), (*name).clone()));
        for (field_name, _field) in fields {
            let resolved = self.resolve_struct_field_metadata(struct_name, field_name)?;
            let full_name = format!("{name_prefix}.{field_name}");
            if let Some(nested_name) = resolved
                .struct_name
                .as_deref()
                .filter(|_| !resolved.c_type.is_pointer())
            {
                if resolved.array_element_width.is_some() {
                    self.append_aggregate_array_leaf_segments(
                        segments,
                        base.clone(),
                        base_offset,
                        &resolved,
                        nested_name,
                        &full_name,
                    )?;
                } else {
                    let nested_offset = base_offset
                        .checked_add(resolved.offset_bytes)
                        .ok_or_else(|| self.error("aggregate field offset overflows"))?;
                    self.append_aggregate_leaf_segments(
                        segments,
                        base.clone(),
                        nested_name,
                        nested_offset,
                        &full_name,
                    )?;
                }
                continue;
            }
            if resolved.union_name.is_some() {
                return Err(self.error(format!(
                    "aggregate field `{full_name}` contains an unsupported union"
                )));
            }
            let absolute_offset = base_offset
                .checked_add(resolved.offset_bytes)
                .ok_or_else(|| self.error("aggregate field offset overflows"))?;
            let absolute_end = base_offset
                .checked_add(resolved.slot_end_bytes)
                .ok_or_else(|| self.error("aggregate field extent overflows"))?;
            let mut absolute = resolved.clone();
            absolute.offset_bytes = absolute_offset;
            absolute.slot_end_bytes = absolute_end;
            self.validate_field_place(&absolute)?;
            segments.push(Self::field_segment_from_metadata(
                base.clone(),
                &full_name,
                &absolute,
            ));
        }
        Ok(())
    }

    fn append_aggregate_array_leaf_segments(
        &self,
        segments: &mut Vec<ContractSegment>,
        base: CExpression,
        base_offset: u32,
        field: &ResolvedField,
        struct_name: &str,
        name_prefix: &str,
    ) -> Result<(), ClickError> {
        let element_width = field.array_element_width.ok_or_else(|| {
            self.error(format!(
                "aggregate field `{name_prefix}` has no element width"
            ))
        })?;
        let shape = field.array_shape.as_deref().ok_or_else(|| {
            self.error(format!(
                "aggregate field `{name_prefix}` has no shape metadata"
            ))
        })?;
        let element_count = shape.iter().try_fold(1u32, |count, length| {
            count
                .checked_mul(*length)
                .ok_or_else(|| self.error(format!("aggregate field `{name_prefix}` is too large")))
        })?;
        for flat_index in 0..element_count {
            let offset = base_offset
                .checked_add(field.offset_bytes)
                .ok_or_else(|| self.error("aggregate field offset overflows"))?
                .checked_add(flat_index.checked_mul(element_width).ok_or_else(|| {
                    self.error(format!("aggregate field `{name_prefix}` offset overflows"))
                })?)
                .ok_or_else(|| self.error("aggregate field offset overflows"))?;
            let path = row_major_index_path(flat_index, shape);
            self.append_aggregate_leaf_segments(
                segments,
                base.clone(),
                struct_name,
                offset,
                &format!("{name_prefix}{path}"),
            )?;
        }
        Ok(())
    }

    fn resolve_field_segment(
        &self,
        base: CExpression,
        field_name: &str,
    ) -> Result<ContractSegment, ClickError> {
        let Some(field) = self.resolve_field_metadata(&base, field_name)? else {
            // A base whose layout this parse cannot name, such as a loaded
            // pointer, keeps its field name for later lowering to resolve.
            return Ok(ContractSegment {
                state: ContractSegmentState::Current,
                base,
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Field {
                    name: field_name.to_string(),
                    element_width: None,
                    element_type: None,
                },
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
        if let C0Type::Int32Array(_) | C0Type::CharArray(_) | C0Type::UInt8Array(_) = field.c_type {
            let (element_width, element_type) = match field.c_type {
                C0Type::Int32Array(_) => (4, CType::Int32),
                C0Type::CharArray(_) => (1, CType::UInt8),
                C0Type::UInt8Array(_) => (1, CType::UInt8),
                _ => unreachable!("validated inline array field"),
            };
            let field_base = crate::kernel::c_pointer_offset_bytes(base, field.offset_bytes);
            return ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::TypedLoad {
                    pointer: Box::new(field_base),
                    value_type: field.c_type.to_kernel_type(),
                    volatile: false,
                },
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(
                    (field.slot_end_bytes - field.offset_bytes) / element_width,
                )),
                surface: ContractSegmentSurface::Field {
                    name: field_name.to_string(),
                    element_width: Some(element_width),
                    element_type: Some(element_type),
                },
            };
        }
        let element_width = match field.c_type {
            C0Type::Char => 1,
            C0Type::UInt8 => 1,
            C0Type::Int16 | C0Type::UInt16 => 2,
            C0Type::Int64 | C0Type::UInt64 => 8,
            C0Type::Float32 => 4,
            C0Type::Float64 => 8,
            _ => 4,
        };
        let start = field.offset_bytes / element_width;
        let end = field.slot_end_bytes / element_width;
        ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start: CExpression::Value(int32(start)),
            end: CExpression::Value(int32(end)),
            surface: ContractSegmentSurface::Field {
                name: field_name.to_string(),
                // Non-array fields use their ABI width as the resource slot
                // width. Smaller integer fields retain their natural
                // two-byte/one-byte units so a typed load is covered exactly.
                element_width: Some(element_width),
                element_type: Some(field.c_type.to_kernel_type()),
            },
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
            volatile: false,
        })
    }

    fn resolve_c0_field_load(
        &self,
        base: C0Expression,
        field_name: &str,
    ) -> Result<Option<C0Expression>, ClickError> {
        let struct_name = match &base {
            C0Expression::Variable(base_name) => self
                .current_struct_params
                .get(base_name)
                .or_else(|| self.current_aggregate_objects.get(base_name)),
            C0Expression::Field {
                field_struct_name, ..
            } => field_struct_name.as_ref(),
            C0Expression::AggregateAddress { struct_name, .. } => Some(struct_name),
            _ => None,
        };
        if let Some(struct_name) = struct_name {
            let field = self.resolve_struct_field_metadata(struct_name, field_name)?;
            let pointer = self.offset_c0_field_pointer(base.clone(), field.offset_bytes);
            return Ok(Some(if let Some(union_name) = field.union_name {
                C0Expression::UnionAddress {
                    pointer: Box::new(pointer),
                    union_name,
                }
            } else if field.c_type == C0Type::Int32 {
                if let Some(struct_name) = field.struct_name {
                    C0Expression::AggregateAddress {
                        pointer: Box::new(pointer),
                        struct_name,
                    }
                } else {
                    C0Expression::Field {
                        pointer: Box::new(pointer),
                        field_type: field.c_type,
                        field_struct_name: None,
                        function_pointer_signature: None,
                        array_shape: None,
                    }
                }
            } else {
                C0Expression::Field {
                    pointer: Box::new(pointer),
                    field_type: field.c_type,
                    field_struct_name: field.struct_name,
                    function_pointer_signature: field.function_pointer_signature.clone(),
                    array_shape: field.array_shape,
                }
            }));
        }
        if let C0Expression::UnionAddress { union_name, .. } = &base {
            let field = self.resolve_union_field_metadata(union_name, field_name)?;
            let pointer = self.offset_c0_field_pointer(base.clone(), field.offset_bytes);
            return Ok(Some(C0Expression::UnionField {
                pointer: Box::new(pointer),
                field_type: field.c_type,
                union_name: union_name.clone(),
            }));
        }
        Ok(None)
    }

    fn resolve_field_metadata(
        &self,
        base: &CExpression,
        field_name: &str,
    ) -> Result<Option<ResolvedField>, ClickError> {
        let Some(base_name) = named_place_base(base) else {
            return Ok(None);
        };
        let Some(struct_name) = self
            .current_struct_params
            .get(base_name)
            .or_else(|| self.current_aggregate_objects.get(base_name))
        else {
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
            union_name: field.union_name().map(str::to_string),
            function_pointer_signature: field.function_pointer_signature().cloned(),
            array_element_width: field.array_element_width(),
            array_shape: field.array_shape().map(|shape| shape.to_vec()),
            offset_bytes: field.offset_bytes(),
            byte_width: field.byte_width(),
            slot_end_bytes,
        })
    }

    fn resolve_union_field_metadata(
        &self,
        union_name: &str,
        field_name: &str,
    ) -> Result<ResolvedField, ClickError> {
        let Some(layout) = self.union_layouts.get(union_name) else {
            return Err(self.error(format!("unknown union declaration `{union_name}`")));
        };
        let Some(field) = layout.field(field_name) else {
            return Err(self.error(format!("union `{union_name}` has no member `{field_name}`")));
        };
        Ok(ResolvedField {
            c_type: field.c_type(),
            struct_name: None,
            union_name: None,
            function_pointer_signature: None,
            array_element_width: None,
            array_shape: None,
            offset_bytes: field.offset_bytes(),
            byte_width: field.byte_width(),
            slot_end_bytes: layout.size_bytes(),
        })
    }

    fn validate_field_place(&self, field: &ResolvedField) -> Result<(), ClickError> {
        if field.array_element_width.is_some() {
            return Err(
                self.error("arrays of embedded structs require an index before a resource segment")
            );
        }
        if field.c_type == C0Type::Int32
            && (field.struct_name.is_some() || field.union_name.is_some())
        {
            return Err(self.error(
                "aggregate struct and union field places are not supported; name a leaf field instead",
            ));
        }
        if matches!(
            field.c_type,
            C0Type::Int32Array(_) | C0Type::CharArray(_) | C0Type::UInt8Array(_)
        ) {
            if field.slot_end_bytes < field.offset_bytes
                || (matches!(field.c_type, C0Type::Int32Array(_))
                    && (field.slot_end_bytes - field.offset_bytes) % 4 != 0)
            {
                return Err(self.error("inline array field has an invalid resource extent"));
            }
            return Ok(());
        }
        if matches!(field.c_type, C0Type::Int16 | C0Type::UInt16) {
            if field.offset_bytes % 2 != 0
                || field.byte_width != 2
                || field.slot_end_bytes < field.offset_bytes
                || (field.slot_end_bytes - field.offset_bytes) % 2 != 0
            {
                return Err(self.error("16-bit field places require two-byte alignment and width"));
            }
            return Ok(());
        }
        if matches!(field.c_type, C0Type::Int64 | C0Type::UInt64) {
            if field.offset_bytes % 8 != 0
                || field.byte_width != 8
                || field.slot_end_bytes < field.offset_bytes
                || (field.slot_end_bytes - field.offset_bytes) % 8 != 0
            {
                return Err(
                    self.error("64-bit field places require eight-byte alignment and width")
                );
            }
            return Ok(());
        }
        if matches!(field.c_type, C0Type::Char | C0Type::UInt8) {
            if field.byte_width != 1 || field.slot_end_bytes < field.offset_bytes {
                return Err(self.error("uint8 field places require one-byte width"));
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
        if self.peek() == Some(&Token::LParen)
            && matches!(self.peek_next(), Some(Token::Ident(name)) if name == "uint32")
        {
            self.position += 1;
            let target_type = self.parse_type()?.c_type.to_kernel_type();
            if target_type.is_pointer() {
                return Err(self.error("contract scalar casts do not accept pointer target types"));
            }
            self.expect(Token::RParen)?;
            let operand = self.parse_contract_unary()?;
            let Some(expression) = contract_expression_as_c_fragment(&operand) else {
                return Err(self.error("scalar cast expects a current C expression; put old(...) around the whole cast for an entry-state value"));
            };
            return Ok(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(expression),
                target_type,
                pointee_volatile: false,
            }));
        }
        if self.peek() == Some(&Token::Minus) {
            if let Some(value) = self.peek_next().and_then(negatable_int32_magnitude) {
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
        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let expression = self.parse_contract_unary()?;
            let Some(expression) = contract_expression_as_c_fragment(&expression) else {
                return Err(self.error("address-of is only supported on current C expressions"));
            };
            return Ok(ContractExpression::CFragment(CExpression::AddressOf(
                Box::new(expression),
            )));
        }

        self.parse_contract_postfix()
    }

    fn parse_contract_postfix(&mut self) -> Result<ContractExpression, ClickError> {
        let expression = self.parse_contract_primary()?;
        self.parse_contract_postfix_suffix(expression)
    }

    // Keep postfix metadata and field-lowering temporaries out of the
    // recursive expression parser frame. Nested `match` expressions only
    // retain this small dispatcher while their primary is parsed.
    #[inline(never)]
    fn parse_contract_postfix_suffix(
        &mut self,
        mut expression: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let mut struct_name = match &expression {
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_struct_params
                .get(name)
                .or_else(|| self.current_aggregate_objects.get(name))
                .cloned(),
            _ => None,
        };
        let mut union_name: Option<String> = None;
        let mut struct_array_element_width = match &expression {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_struct_array_params
                .contains(name)
                .then(|| {
                    struct_name
                        .as_ref()
                        .and_then(|name| self.struct_layouts.get(name))
                        .map(|layout| layout.size_bytes())
                })
                .flatten(),
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some() && object.array_shape.is_some())
                .and_then(|object| object.struct_name.as_ref())
                .and_then(|name| self.struct_layouts.get(name))
                .map(|layout| layout.size_bytes()),
            _ => None,
        };
        let mut struct_array_shape = match &expression {
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some())
                .and_then(|object| object.array_shape.clone()),
            _ => None,
        };
        let mut scalar_array_shape = match &expression {
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.array_shape.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_global_array_shapes
                .get(name)
                .map(|array| array.shape.clone()),
            _ => None,
        };
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_contract_expression()?;
                    self.expect(Token::RBracket)?;
                    if let Some(element_width) = struct_array_element_width
                        && let Some(base_struct_name) = &struct_name
                        && self.struct_layouts.contains_key(base_struct_name)
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
                        let mut indexes = vec![index.clone()];
                        while struct_array_shape.is_some() && self.peek() == Some(&Token::LBracket)
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            let next_index = contract_expression_as_c_fragment(&next_index)
                                .ok_or_else(|| {
                                    self.error("struct array indices must be current C expressions")
                                })?;
                            indexes.push(next_index);
                        }
                        let offset = if let Some(shape) = struct_array_shape.take() {
                            if indexes.len() != shape.len() {
                                return Err(self.error(format!(
                                    "multidimensional struct array field requires {} indices, got {}",
                                    shape.len(),
                                    indexes.len()
                                )));
                            }
                            flatten_array_indices(indexes, &shape)
                        } else {
                            index
                        };
                        let stride = CExpression::Multiply(
                            Box::new(offset),
                            Box::new(CExpression::Value(int32(element_width))),
                        );
                        expression = ContractExpression::CFragment(CExpression::Add(
                            Box::new(base),
                            Box::new(stride),
                        ));
                        struct_array_element_width = None;
                    } else if let Some(shape) = struct_array_shape.take() {
                        let mut indexes =
                            vec![contract_expression_as_c_fragment(&index).ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?];
                        while self.peek() == Some(&Token::LBracket)
                            && !self.contract_bracket_is_range()
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            indexes.push(
                                contract_expression_as_c_fragment(&next_index).ok_or_else(
                                    || {
                                        self.error(
                                            "struct array indices must be current C expressions",
                                        )
                                    },
                                )?,
                            );
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error(format!(
                                "multidimensional scalar array field requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let offset = flatten_array_indices(indexes, &shape);
                        expression = ContractExpression::Index(
                            Box::new(expression),
                            Box::new(ContractExpression::CFragment(offset)),
                        );
                        struct_name = None;
                        union_name = None;
                        struct_array_element_width = None;
                    } else if let Some(shape) = scalar_array_shape.take() {
                        let mut indexes =
                            vec![contract_expression_as_c_fragment(&index).ok_or_else(|| {
                                self.error("global array indices must be current C expressions")
                            })?];
                        while self.peek() == Some(&Token::LBracket)
                            && !self.contract_bracket_is_range()
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            indexes.push(
                                contract_expression_as_c_fragment(&next_index).ok_or_else(
                                    || {
                                        self.error(
                                            "global array indices must be current C expressions",
                                        )
                                    },
                                )?,
                            );
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error(format!(
                                "multidimensional global array requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let offset = flatten_array_indices(indexes, &shape);
                        expression = ContractExpression::Index(
                            Box::new(expression),
                            Box::new(ContractExpression::CFragment(offset)),
                        );
                        struct_name = None;
                        union_name = None;
                        struct_array_element_width = None;
                    } else {
                        expression =
                            ContractExpression::Index(Box::new(expression), Box::new(index));
                        struct_name = None;
                        union_name = None;
                        struct_array_element_width = None;
                        struct_array_shape = None;
                        scalar_array_shape = None;
                    }
                }
                Some(Token::Arrow | Token::Dot) => {
                    if let ContractExpression::ResourceField(access) = &mut expression {
                        if self.peek() != Some(&Token::Dot) {
                            return Err(self.error("resource children use `.`, not `->`"));
                        }
                        self.position += 1;
                        let next = self.expect_ident("resource child or field name")?;
                        access
                            .children
                            .push(std::mem::replace(&mut access.field, next));
                        access.click_type = None;
                        continue;
                    }
                    if let ContractExpression::CFragment(CExpression::Variable(owner)) = &expression
                        && let Some((identity, resource_name)) =
                            self.current_resource_bindings.get(owner).cloned()
                    {
                        if self.peek() != Some(&Token::Dot) {
                            return Err(self.error("resource fields use `.`, not `->`"));
                        }
                        let owner = owner.clone();
                        self.position += 1;
                        let field = self.expect_ident("resource field name")?;
                        expression = ContractExpression::ResourceField(ResourceFieldAccess {
                            owner,
                            resource_name,
                            identity,
                            children: vec![],
                            field,
                            field_index: 0,
                            click_type: None,
                        });
                        continue;
                    }
                    if struct_array_element_width.is_some() {
                        return Err(self.error(
                            "arrays of embedded structs require an index before field access",
                        ));
                    }
                    self.position += 1;
                    let field_name = self.expect_ident("field name")?;
                    let surface_base = expression.clone();
                    let Some(base) = contract_expression_as_c_fragment(&expression) else {
                        return Err(
                            self.error("field access is only supported on current C fragments")
                        );
                    };
                    if let Some(base_union_name) = &union_name
                        && self.union_layouts.contains_key(base_union_name)
                    {
                        let field =
                            self.resolve_union_field_metadata(base_union_name, &field_name)?;
                        let pointer = self.offset_field_pointer(base, field.offset_bytes);
                        struct_name = field.struct_name.clone();
                        union_name = None;
                        struct_array_element_width = None;
                        struct_array_shape = None;
                        expression = ContractExpression::Field {
                            base: Box::new(surface_base),
                            field: field_name,
                            lowered: lowered_field_expression(pointer, &field),
                        };
                    } else if let Some(base_struct_name) = &struct_name
                        && self.struct_layouts.contains_key(base_struct_name)
                    {
                        let field =
                            self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                        let pointer = self.offset_field_pointer(base, field.offset_bytes);
                        struct_name = field.struct_name.clone();
                        union_name = field.union_name.clone();
                        struct_array_element_width = field.array_element_width;
                        struct_array_shape = field.array_shape.clone();
                        scalar_array_shape = None;
                        expression = ContractExpression::Field {
                            base: Box::new(surface_base),
                            field: field_name,
                            lowered: lowered_field_expression(pointer, &field),
                        };
                    } else {
                        expression = ContractExpression::Field {
                            base: Box::new(surface_base),
                            field: field_name.clone(),
                            lowered: self.resolve_field_load(base, &field_name)?,
                        };
                        struct_array_element_width = None;
                        struct_array_shape = None;
                        scalar_array_shape = None;
                    }
                }
                _ => return Ok(expression),
            }
        }
    }

    fn contract_bracket_is_range(&self) -> bool {
        if self.peek() != Some(&Token::LBracket) {
            return false;
        }
        let mut depth = 0usize;
        for token in self.tokens.iter().skip(self.position) {
            match token {
                Token::LBracket => depth += 1,
                Token::DotDot if depth == 1 => return true,
                Token::RBracket => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                    if depth == 0 {
                        return false;
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn parse_contract_match(&mut self) -> Result<ContractExpression, ClickError> {
        self.position += 1;
        let scrutinee = self.parse_contract_expression()?;
        self.expect(Token::LBrace)?;
        let mut arms = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            let type_name = self.expect_ident("match pattern datatype")?;
            self.expect(Token::ColonColon)?;
            let variant = self.expect_ident("match pattern variant")?;
            let mut bindings = Vec::new();
            if self.peek() == Some(&Token::LParen) {
                self.position += 1;
                if self.peek() != Some(&Token::RParen) {
                    loop {
                        bindings.push(self.expect_ident("match pattern binding")?);
                        match self.peek() {
                            Some(Token::Comma) => self.position += 1,
                            Some(Token::RParen) => break,
                            Some(token) => {
                                return Err(self.error(format!(
                                    "expected `,` or `)` after match binding, got {}",
                                    token.describe()
                                )));
                            }
                            None => {
                                return Err(self.error("expected `)` after match bindings"));
                            }
                        }
                    }
                }
                self.expect(Token::RParen)?;
            }
            self.expect(Token::FatArrow)?;
            let newly_bound = bindings
                .iter()
                .filter(|binding| self.current_contract_bindings.insert((*binding).clone()))
                .cloned()
                .collect::<Vec<_>>();
            let body = self.parse_contract_expression();
            for binding in newly_bound {
                self.current_contract_bindings.remove(&binding);
            }
            let body = body?;
            arms.push(AlgebraicMatchArm {
                type_name,
                variant,
                bindings,
                body,
            });
            if self.peek() == Some(&Token::Comma) {
                self.position += 1;
            } else if self.peek() != Some(&Token::RBrace) {
                return Err(self.error("expected `,` or `}` after match arm"));
            }
        }
        self.expect(Token::RBrace)?;
        return Ok(ContractExpression::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms,
        });
    }

    fn parse_contract_primary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.is_qualified_c_name() {
            let (name, lowered) = self.parse_qualified_c_name()?;
            return Ok(ContractExpression::QualifiedC { name, lowered });
        }
        if self.peek_ident() == Some("match") {
            if self.match_nesting >= MATCH_NESTING_LIMIT {
                return Err(self.error(format!(
                    "match nesting exceeds Click's supported depth of {MATCH_NESTING_LIMIT}"
                )));
            }
            self.match_nesting += 1;
            let result = self.parse_contract_match();
            self.match_nesting -= 1;
            return result;
        }

        self.parse_contract_non_match_primary()
    }

    #[inline(never)]
    fn parse_contract_non_match_primary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.looks_like_algebraic_constructor() {
            let algebraic_type = self.parse_algebraic_type_application()?;
            self.expect(Token::ColonColon)?;
            let variant = self.expect_ident("algebraic constructor variant")?;
            let mut arguments = Vec::new();
            if self.peek() == Some(&Token::LParen) {
                self.position += 1;
                if self.peek() != Some(&Token::RParen) {
                    arguments.push(self.parse_contract_expression()?);
                    while self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                        arguments.push(self.parse_contract_expression()?);
                    }
                }
                self.expect(Token::RParen)?;
            }
            return Ok(ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            });
        }

        if self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let mut elements = Vec::new();
            if self.peek() != Some(&Token::RBracket) {
                elements.push(self.parse_contract_expression()?);
                while self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                    elements.push(self.parse_contract_expression()?);
                }
            }
            self.expect(Token::RBracket)?;
            return Ok(ContractExpression::SequenceLiteral(elements));
        }

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
            let binding_was_in_scope = !self.current_contract_bindings.insert(binding.name.clone());
            let body = self.parse_contract_expression();
            if !binding_was_in_scope {
                self.current_contract_bindings.remove(&binding.name);
            }
            let body = body?;
            return Ok(ContractExpression::Let {
                name: binding.name,
                click_type: binding.click_type,
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

        if self.peek_ident() == Some("address") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let pointer = self.parse_contract_expression()?;
            let Some(pointer) = contract_expression_as_c_fragment(&pointer) else {
                return Err(self.error("address expects a current C pointer expression"));
            };
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(pointer),
                target_type: CType::UInt64,
                pointee_volatile: false,
            }));
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
            Some("load_uint32") => Some(CType::UInt32),
            Some("load_int64") => Some(CType::Int64),
            Some("load_uint64") => Some(CType::UInt64),
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
                volatile: false,
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
                if let Some(field) = self.current_resource_fields.get(&name) {
                    return Ok(ContractExpression::ResourceField(field.clone()));
                }
                if self.current_contract_bindings.contains(&name) {
                    Ok(ContractExpression::Binding(name))
                } else {
                    match self.current_algebraic_params.get(&name) {
                        Some((algebraic_type, binder_index)) => {
                            Ok(ContractExpression::AlgebraicVariable {
                                name,
                                algebraic_type: algebraic_type.clone(),
                                binder_index: *binder_index,
                            })
                        }
                        None => Ok(ContractExpression::CFragment(CExpression::Variable(name))),
                    }
                }
            }
            Some(Token::Number(value)) => Ok(ContractExpression::CFragment(CExpression::Value(
                CValue::Int32(Bitvector32Term::Constant(value)),
            ))),
            Some(Token::UInt8Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt8(Bitvector32Term::Constant(u32::from(value)))),
            )),
            Some(Token::UInt32Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt32(Bitvector32Term::Constant(value))),
            )),
            Some(Token::Int64Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::Int64(Bitvector32Term::Int64Constant(value))),
            )),
            Some(Token::UInt64Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(value))),
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

    fn looks_like_algebraic_constructor(&self) -> bool {
        if !matches!(self.peek(), Some(Token::Ident(_))) {
            return false;
        }
        if self.peek_next() == Some(&Token::ColonColon) {
            return true;
        }
        if self.peek_next() != Some(&Token::LessThan) {
            return false;
        }
        let mut index = self.position + 2;
        let mut nested = 1usize;
        while let Some(token) = self.tokens.get(index) {
            match token {
                Token::LessThan => nested += 1,
                Token::GreaterThan => {
                    nested -= 1;
                    if nested == 0 {
                        return self.tokens.get(index + 1) == Some(&Token::ColonColon);
                    }
                }
                Token::ShiftRight if nested >= 2 => {
                    nested -= 2;
                    if nested == 0 {
                        return self.tokens.get(index + 1) == Some(&Token::ColonColon);
                    }
                }
                _ => {}
            }
            index += 1;
        }
        false
    }

    fn parse_algebraic_type_application(&mut self) -> Result<AlgebraicTypeApplication, ClickError> {
        let name = self.expect_ident("algebraic datatype name")?;
        let mut arguments = Vec::new();
        if self.peek() == Some(&Token::LessThan) {
            self.position += 1;
            loop {
                let (argument, parsed_c_type) = self.parse_click_type()?;
                if let Some(parsed) = parsed_c_type
                    && !algebraic_field_c_type_supported(parsed.c_type)
                {
                    return Err(self.error("algebraic datatype arguments must be value types"));
                }
                arguments.push(argument);
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::GreaterThan) => {
                        self.position += 1;
                        break;
                    }
                    Some(Token::ShiftRight) => {
                        self.tokens[self.position] = Token::GreaterThan;
                        break;
                    }
                    Some(token) => {
                        return Err(self.error(format!(
                            "expected `,` or `>` after datatype argument, got {}",
                            token.describe()
                        )));
                    }
                    None => return Err(self.error("expected `>` after datatype arguments")),
                }
            }
        }
        Ok(AlgebraicTypeApplication {
            rigid: false,
            name,
            arguments,
        })
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
            if let Some(value) = self.peek_next().and_then(negatable_int32_magnitude) {
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
        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            return Ok(C0Expression::AddressOf(Box::new(
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
                Some(Token::Arrow | Token::Dot) => {
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
            Some(Token::UInt32Number(value)) => Ok(C0Expression::UInt32Literal(value)),
            Some(Token::Int64Number(value)) => Ok(C0Expression::Int64Literal(value)),
            Some(Token::UInt64Number(value)) => Ok(C0Expression::UInt64Literal(value)),
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

fn float_classification_from_name(name: &str) -> Option<syntax::C0FloatClassification> {
    match name {
        "isfinite" => Some(syntax::C0FloatClassification::Finite),
        "isinf" => Some(syntax::C0FloatClassification::Infinite),
        "iszero" => Some(syntax::C0FloatClassification::Zero),
        "issubnormal" => Some(syntax::C0FloatClassification::Subnormal),
        "isnan" => Some(syntax::C0FloatClassification::Nan),
        _ => None,
    }
}

fn expand_aggregate_resource_clause(resource: ResourceClause) -> Vec<ResourceClause> {
    match resource {
        ResourceClause::MemoryAggregate { access, segments } => segments
            .into_iter()
            .map(|segment| match access {
                ResourceAccessMode::Own => ResourceClause::OwnMemory(segment),
                ResourceAccessMode::View => ResourceClause::ViewMemory(segment),
            })
            .collect(),
        ResourceClause::Quantified { quantity, resource } => {
            expand_aggregate_resource_clause(*resource)
                .into_iter()
                .map(|resource| ResourceClause::Quantified {
                    quantity: quantity.clone(),
                    resource: Box::new(resource),
                })
                .collect()
        }
        resource => vec![resource],
    }
}

fn expand_aggregate_requirement(requirement: Requirement) -> Vec<Requirement> {
    match requirement {
        Requirement::Labeled { label, requirement } => expand_aggregate_requirement(*requirement)
            .into_iter()
            .map(|requirement| Requirement::Labeled {
                label: label.clone(),
                requirement: Box::new(requirement),
            })
            .collect(),
        Requirement::Resource(resource) => expand_aggregate_resource_clause(resource)
            .into_iter()
            .map(Requirement::Resource)
            .collect(),
        requirement => vec![requirement],
    }
}

fn expand_aggregate_ensure_clause(clause: EnsureClause) -> Vec<EnsureClause> {
    let EnsureClause {
        name,
        ensure,
        proof,
    } = clause;
    match ensure {
        Ensure::Resource(resource) => expand_aggregate_resource_clause(resource)
            .into_iter()
            .map(|resource| EnsureClause {
                name: name.clone(),
                ensure: Ensure::Resource(resource),
                proof: proof.clone(),
            })
            .collect(),
        ensure => vec![EnsureClause {
            name,
            ensure,
            proof,
        }],
    }
}

/// Names the object a contract segment's base refers to.
///
/// A segment may spell its base directly (`object.field`) or by address
/// (`&object.field`); both name the same object, so field resolution has to
/// see through the address-of. Anything else is not a named place.
/// The magnitude of a literal that a leading `-` turns into an `int32`.
///
/// `int32` reaches one further below zero than above it, so the magnitude
/// 2^31 is negatable even though the positive spelling of it is not an
/// `int32`. The tokenizer therefore hands that one over as a wider literal
/// and it narrows here, where the minus sign is in hand.
fn negatable_int32_magnitude(token: &Token) -> Option<u32> {
    match token {
        Token::Number(value) if *value <= i32::MAX as u32 => Some(*value),
        Token::Int64Number(value) if *value == i32::MAX as i64 + 1 => Some(i32::MAX as u32 + 1),
        _ => None,
    }
}

fn named_place_base(expression: &CExpression) -> Option<&String> {
    match expression {
        CExpression::Variable(name) => Some(name),
        CExpression::AddressOf(inner) => match inner.as_ref() {
            CExpression::Variable(name) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

fn flatten_array_indices(indexes: Vec<CExpression>, dimensions: &[u32]) -> CExpression {
    let mut terms = Vec::with_capacity(indexes.len());
    for (index, expression) in indexes.into_iter().enumerate() {
        let stride = dimensions[index + 1..]
            .iter()
            .copied()
            .fold(1u32, |stride, dimension| {
                stride
                    .checked_mul(dimension)
                    .expect("validated array shape has a representable stride")
            });
        terms.push(if stride == 1 {
            expression
        } else {
            CExpression::Multiply(
                Box::new(expression),
                Box::new(CExpression::Value(int32(stride))),
            )
        });
    }
    let mut terms = terms.into_iter();
    let mut offset = terms
        .next()
        .expect("a multidimensional access has at least one index");
    for term in terms {
        offset = CExpression::Add(Box::new(offset), Box::new(term));
    }
    offset
}

fn row_major_index_path(flat_index: u32, shape: &[u32]) -> String {
    let mut remaining = flat_index;
    let mut indexes = vec![0; shape.len()];
    for (dimension, length) in shape.iter().enumerate().rev() {
        indexes[dimension] = remaining % *length;
        remaining /= *length;
    }
    indexes
        .into_iter()
        .map(|index| format!("[{index}]"))
        .collect()
}

fn lowered_field_expression(pointer: CExpression, field: &ResolvedField) -> CExpression {
    if field.c_type == C0Type::Int32 && (field.struct_name.is_some() || field.union_name.is_some())
    {
        pointer
    } else {
        CExpression::TypedLoad {
            pointer: Box::new(pointer),
            value_type: field.c_type.to_kernel_type(),
            volatile: false,
        }
    }
}

fn field_has_direct_memory_place(field: &ResolvedField) -> bool {
    if field.struct_name.is_some() || field.union_name.is_some() {
        return false;
    }
    matches!(
        field.c_type,
        C0Type::Int16
            | C0Type::Int32
            | C0Type::Char
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64
            | C0Type::UInt64
            | C0Type::Int32Array(_)
            | C0Type::CharArray(_)
            | C0Type::UInt8Array(_)
    )
}

fn scalar_array_field_element(field: &ResolvedField) -> Option<(u32, CType)> {
    if field.struct_name.is_some() || field.union_name.is_some() || field.array_shape.is_none() {
        return None;
    }
    match field.c_type {
        C0Type::Int32Array(_) => Some((4, CType::Int32)),
        C0Type::CharArray(_) => Some((1, CType::UInt8)),
        C0Type::UInt8Array(_) => Some((1, CType::UInt8)),
        _ => None,
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

/// `aligned(p, n)` is sugar for `address(p) & (n - 1) == 0`; the kernel
/// decides that shape from the pointer's formation.
fn aligned_proposition(pointer: CExpression, alignment: u64) -> ClickProposition {
    let uint64 = |value: u64| {
        ContractExpression::CFragment(CExpression::Value(CValue::UInt64(
            Bitvector32Term::UInt64Constant(value),
        )))
    };
    ClickProposition::Comparison {
        left: ContractExpression::BitwiseAnd(
            Box::new(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(pointer),
                target_type: CType::UInt64,
                pointee_volatile: false,
            })),
            Box::new(uint64(alignment - 1)),
        ),
        operator: ComparisonOperator::Equal,
        right: uint64(0),
    }
}

/// The alignment fact a required complete-object clause carries: a live
/// object of a struct type is placed at that type's alignment, so a
/// required `object(p)` states `aligned(p, alignof(struct))`, which the
/// caller proves and the function relies on. A produced object and a
/// resource body state alignment explicitly (`ensures aligned(result, n)`,
/// `fact aligned(p, n)`): a function may return an object it received
/// inside a resource without knowing its alignment, and a generated body
/// fact would make a counted population require a positive witness.
fn object_alignment_fact(
    clause: &ResourceClause,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Option<ClickProposition> {
    let (ResourceClause::OwnMemory(segment) | ResourceClause::ViewMemory(segment)) = clause else {
        return None;
    };
    let ContractSegmentSurface::Object(struct_name) = &segment.surface else {
        return None;
    };
    let alignment = u64::from(struct_layouts.get(struct_name)?.alignment_bytes());
    (alignment >= 2).then(|| aligned_proposition(segment.base.clone(), alignment))
}

fn requirement_object_alignment_facts(
    requirement: &Requirement,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
    out: &mut Vec<ClickProposition>,
) {
    match requirement {
        Requirement::Labeled { requirement, .. } => {
            requirement_object_alignment_facts(requirement, struct_layouts, out);
        }
        Requirement::Resource(clause) => out.extend(object_alignment_fact(clause, struct_layouts)),
        Requirement::LoadableSegment { .. } | Requirement::Proposition(_) => {}
    }
}
