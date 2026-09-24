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
/// Braces and brackets also introduce recursive surface-parser frames. This
/// limit is deliberately separate from parentheses: a match expression is
/// already bounded independently, while nested theorem/proof blocks and
/// quantifier bodies share the ordinary structural budget.
pub(super) const STRUCTURAL_NESTING_LIMIT: usize = 32;
/// Conditional contract expressions recurse through both branch bodies. Keep
/// that expression-specific path on the same bounded structural budget as
/// quantifier and proof bodies instead of relying on the broad delimiter cap.
pub(super) const CONTRACT_IF_NESTING_LIMIT: usize = STRUCTURAL_NESTING_LIMIT;
/// Generic algebraic applications and datatype fields recurse through angle
/// brackets, which are not part of the delimiter preflight because they also
/// spell comparison operators. Keep that type-only recursion bounded here.
pub(super) const ALGEBRAIC_TYPE_NESTING_LIMIT: usize = STRUCTURAL_NESTING_LIMIT;
/// A final token-level backstop for delimiter nesting that is not owned by a
/// single recursive parser. The grammar-specific counters below use the
/// smaller structural limit; this larger bound keeps malformed or mixed
/// delimiter input from reaching an unguarded helper.
const DELIMITER_NESTING_LIMIT: usize = 128;
/// Operator chains create deeply nested boxed ASTs even though the precedence
/// loops themselves are iterative. Bound those chains before the first
/// over-deep node is constructed, keeping malformed source on a bounded-error
/// path and preserving the existing deep-certificate compatibility boundary.
pub(super) const EXPRESSION_CHAIN_LIMIT: usize = 512;
const UNARY_NESTING_LIMIT: usize = 64;
/// Sequential value bindings are parsed iteratively so this limit bounds the
/// resulting contract-expression chain without consuming parser stack.
pub(super) const CONTRACT_LET_CHAIN_LIMIT: usize = 128;
/// A value binding whose initializer contains another value binding remains
/// recursive, so keep that separate nesting path deliberately small.
const CONTRACT_LET_RECURSION_LIMIT: usize = 8;

/// The memory-range fact was spelled `loadable(...)` before it was named after
/// the `views` clause it shadows. There is no compatibility alias, so a source
/// still using the old spelling is refused by name rather than reported as an
/// unknown call.
const RETIRED_LOADABLE_SPELLING: &str = "`loadable(...)` was renamed `viewable(...)`";

/// The index shape and scalar element type of a C global or static array
/// visible to one function's contract. Resource lowering only knows parameter
/// types, so the element type travels with the name to give a byte or
/// halfword slice its physical element width instead of the `int32` default.
#[derive(Clone, Debug)]
pub(super) struct GlobalArrayShape {
    pub(super) shape: Vec<u32>,
    pub(super) element_type: CType,
}

/// The output pattern a call step may bind. The single-name form is kept as a
/// compatibility spelling for calls with exactly one produced instance or a
/// scalar result.
enum CallOutputPattern {
    Single(String),
    Named(Vec<(String, String)>),
}

pub(super) fn parse(source: &str) -> Result<ClickFile, ClickError> {
    Parser::new(source)
        .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?
        .parse_file()
}

pub(super) fn parse_with_layouts_and_aggregate_objects(
    source: &str,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    qualified_objects: BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>,
    local_struct_pointers_by_function: BTreeMap<String, BTreeMap<String, String>>,
) -> Result<ClickFile, ClickError> {
    let mut parser = Parser::new_with_layouts_and_aggregate_objects(
        source,
        struct_layouts,
        union_layouts,
        aggregate_objects_by_function,
        aggregate_array_objects_by_function,
        global_array_shapes_by_function,
    )
    .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
    parser.qualified_objects = Some(qualified_objects);
    parser.local_struct_pointers_by_function = local_struct_pointers_by_function;
    parser.parse_file()
}

pub(super) fn parse_file_items(source: &str) -> Result<ClickFile, ClickError> {
    let mut parser =
        Parser::new(source).map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
    parser.parse_file_items()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn parse_file_items_for_module(
    source: &str,
    identity: &str,
    imported_algebraic_types: &[AlgebraicTypeDefinition],
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    qualified_objects: BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>,
    local_struct_pointers_by_function: BTreeMap<String, BTreeMap<String, String>>,
) -> Result<ClickFile, ClickError> {
    let mut parser = Parser::new_with_layouts_and_aggregate_objects(
        source,
        struct_layouts,
        union_layouts,
        aggregate_objects_by_function,
        aggregate_array_objects_by_function,
        global_array_shapes_by_function,
    )
    .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
    let filename: std::sync::Arc<str> = std::sync::Arc::from(identity);
    for position in &mut parser.positions {
        *position = crate::source::SourcePosition::with_origin(
            position.line,
            position.column,
            filename.clone(),
            position.line,
        );
    }
    for definition in imported_algebraic_types {
        for variant in definition.variants() {
            parser.algebraic_variant_fields.insert(
                (definition.name().to_string(), variant.name().to_string()),
                variant.fields().to_vec(),
            );
        }
    }
    parser.qualified_objects = Some(qualified_objects);
    parser.local_struct_pointers_by_function = local_struct_pointers_by_function;
    parser.parse_file_items()
}

fn is_tactic_name(name: &str) -> bool {
    matches!(name, "auto" | "simp")
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(u32),
    BigNumber(String),
    UnsuffixedInt64(i64),
    UnsuffixedUInt64(u64),
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
            Self::BigNumber(value) => format!("number `{value}`"),
            Self::UnsuffixedInt64(value) => format!("number `{value}`"),
            Self::UnsuffixedUInt64(value) => format!("number `{value}`"),
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
            | Self::BigNumber(_)
            | Self::UnsuffixedInt64(_)
            | Self::UnsuffixedUInt64(_)
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

fn charged_token_equal(left: &[Token], right: &[Token]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    for (left, right) in left.iter().zip(right) {
        let payload = |token: &Token| match token {
            Token::Ident(value) | Token::BigNumber(value) | Token::String(value) => value.len(),
            _ => 0,
        };
        let work = payload(left)
            .saturating_add(payload(right))
            .saturating_add(1);
        if crate::instrumentation::deadline_exceeded_with_work(work) || left != right {
            return false;
        }
    }
    true
}

type ContractBinaryConstructor =
    fn(Box<ContractExpression>, Box<ContractExpression>) -> ContractExpression;

fn contract_binary_operator(token: &Token) -> Option<(usize, ContractBinaryConstructor)> {
    let (precedence, constructor): (usize, ContractBinaryConstructor) = match token {
        Token::PlusPlus => (0, ContractExpression::SequenceConcat),
        Token::Pipe => (1, ContractExpression::BitwiseOr),
        Token::Caret => (2, ContractExpression::BitwiseXor),
        Token::Amp => (3, ContractExpression::BitwiseAnd),
        Token::ShiftLeft => (4, ContractExpression::ShiftLeft),
        Token::ShiftRight => (4, ContractExpression::ShiftRight),
        Token::Plus => (5, ContractExpression::Add),
        Token::Minus => (5, ContractExpression::Subtract),
        Token::Star => (6, ContractExpression::Multiply),
        Token::Slash => (6, ContractExpression::Divide),
        Token::Percent => (6, ContractExpression::Remainder),
        _ => return None,
    };
    Some((precedence, constructor))
}

fn reduce_contract_binary_expression(
    values: &mut Vec<ContractExpression>,
    constructor: ContractBinaryConstructor,
) {
    let right = values
        .pop()
        .expect("a parsed binary operator has a right operand");
    let left = values
        .pop()
        .expect("a parsed binary operator has a left operand");
    values.push(constructor(Box::new(left), Box::new(right)));
}

struct ProofLetParserRestore {
    name: String,
    was_integer_let: bool,
    was_contract_binding: bool,
}

struct Parser {
    source_aliases: BTreeMap<String, String>,
    qualified_objects: Option<BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>>,
    pending_contract_name: Option<String>,
    contract_resource_parameters: BTreeMap<String, ResourceClause>,
    contract_proof_bindings: BTreeMap<String, Vec<(String, Variable, String)>>,
    next_resource_identity: u64,
    current_resource_bindings: BTreeMap<String, (Variable, String)>,
    /// Instances introduced by `let { slot: name } = unfold(parent)`. The slot's
    /// resource is declared by the parent's matched arm, which may not be
    /// parsed yet, so the recorded family is the parent's and every family
    /// comparison against these instances is left to declaration expansion.
    child_slot_identities: BTreeSet<Variable>,
    current_resource_fields: BTreeMap<String, ResourceFieldAccess>,
    current_resource_targets: BTreeMap<String, ResourceClause>,
    in_resource_definition: bool,
    match_nesting: usize,
    proposition_nesting: usize,
    proof_nesting: usize,
    contract_expression_nesting: usize,
    contract_if_nesting: usize,
    algebraic_type_nesting: usize,
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    matching_parentheses: Vec<Option<usize>>,
    position: usize,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    current_struct_params: BTreeMap<String, String>,
    /// The `void *` parameters of the function block being parsed, which a
    /// contract may cast to a struct pointer, and the struct each has been
    /// cast to so far.
    current_void_pointer_params: BTreeSet<String>,
    current_parameter_struct_casts: BTreeMap<String, String>,
    aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    /// The struct name of each automatic struct-pointer local of each C
    /// function, from the C parser. A contract's own parameters come from its
    /// signature; these are the body's locals, so a `have` or `fact` that
    /// names one has the same layout the parameter would have. A parameter of
    /// the same spelling wins: the contract is written against the signature.
    local_struct_pointers_by_function: BTreeMap<String, BTreeMap<String, String>>,
    current_aggregate_objects: BTreeMap<String, String>,
    current_struct_array_params: BTreeSet<String>,
    current_global_array_shapes: BTreeMap<String, GlobalArrayShape>,
    current_algebraic_params: BTreeMap<String, (AlgebraicTypeApplication, usize)>,
    current_click_type_parameters: BTreeSet<String>,
    current_contract_bindings: BTreeSet<String>,
    /// Declared field types of every `spec enum` variant in the file, keyed by
    /// datatype and variant name and indexed before any item is parsed. A
    /// resource's match arm types its constructor bindings from this index, so
    /// a struct-pointer binding is a memory base whether its datatype is
    /// declared above or below the resource: declaration order does not create
    /// scope.
    algebraic_variant_fields: BTreeMap<(String, String), Vec<AlgebraicFieldType>>,
    /// The constructor bindings of the match arm currently being parsed, with
    /// their declared field types. A struct-pointer binding is also in
    /// `current_struct_params`; the others are here only so using one as a
    /// memory base is refused by name instead of lowering to a width-unknown
    /// load.
    current_arm_binding_types: BTreeMap<String, AlgebraicFieldType>,
    current_integer_params: BTreeSet<String>,
    current_integer_lets: BTreeSet<String>,
    /// Names introduced by `let (...) satisfy` in this proof block only.
    /// Nested `have` and branch blocks start a new lexical binder scope;
    /// semantic freshness is checked again by the proof object.
    current_proof_let_names: BTreeSet<String>,
    proof_let_restores: Vec<ProofLetParserRestore>,
    integer_literal_context: bool,
    /// Instance binders declared by each C function block already parsed,
    /// keyed by function name. A call step reads exactly the entry for its
    /// callee, so binding a call site costs one lookup per written entry.
    ///
    /// This is an index over the clauses, not a second source for a binder's
    /// spelling: every entry is copied from the `ResourceClause::Named`
    /// binding the clause already carries, which is also the name lowering
    /// copies into `CResourceSpec::Instance::binder`. The parser cannot read
    /// that kernel field instead, because it resolves a call map while
    /// parsing, before any clause is lowered; and it needs each binder's
    /// identity, resource family, and `owns`/`produces` kind keyed by callee,
    /// which no lowered spec offers.
    callee_resource_binders: BTreeMap<String, BTreeMap<String, CalleeResourceBinder>>,
    /// Set while a `contract` block's embedded function block is parsed: its
    /// signature names an interface, not a callable C function.
    in_contract_definition: bool,
}

/// One `owns`, `consumes`, or `produces` instance binder of a C function
/// block, recorded so a caller's `step(callee(...), { ... })` can bind it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CalleeResourceBinder {
    identity: Variable,
    family: String,
    /// The named resource clause as written by the callee. A call output needs
    /// this richer target, not just the family used for binder transport, so
    /// later `unfold(name)` can recover the resource body and its arguments.
    resource: ResourceClause,
    /// C parameter names in declaration order, used to instantiate the
    /// resource arguments with the call's actual expressions.
    parameter_names: Vec<String>,
    kind: CalleeResourceBinderKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CalleeResourceBinderKind {
    /// `owns` and `consumes`: the caller supplies the instance through the map.
    Supplied,
    /// `produces`: the caller introduces the instance with `let`.
    Produced,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
    struct_pointer: bool,
    constant: bool,
    pointee_constant: bool,
}

/// A recognized `(struct name *)` cast prefix in a contract expression.
struct StructPointerCast {
    struct_name: String,
    pointee_constant: bool,
    /// Tokens the prefix occupies, from `(` through `)`.
    tokens: usize,
}

pub(super) fn is_c_type_keyword(name: &str) -> bool {
    matches!(
        name,
        "void"
            | "_Bool"
            | "bool"
            | "struct"
            | "int32"
            | "int"
            | "int32_t"
            | "int8"
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
            | "int8_t"
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
            | C0Type::Int8Array(_)
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
            ClickType::Parameter(_) | ClickType::C(_) | ClickType::Integer => None,
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedField {
    c_type: C0Type,
    pointee_constant: bool,
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
            child_slot_identities: BTreeSet::new(),
            current_resource_fields: BTreeMap::new(),
            current_resource_targets: BTreeMap::new(),
            in_resource_definition: false,
            tokens,
            positions,
            matching_parentheses,
            match_nesting: 0,
            proposition_nesting: 0,
            proof_nesting: 0,
            contract_expression_nesting: 0,
            contract_if_nesting: 0,
            algebraic_type_nesting: 0,
            position: 0,
            struct_layouts,
            union_layouts,
            current_struct_params: BTreeMap::new(),
            current_void_pointer_params: BTreeSet::new(),
            current_parameter_struct_casts: BTreeMap::new(),
            aggregate_objects_by_function,
            aggregate_array_objects_by_function,
            global_array_shapes_by_function,
            local_struct_pointers_by_function: BTreeMap::new(),
            current_aggregate_objects: BTreeMap::new(),
            current_struct_array_params: BTreeSet::new(),
            current_global_array_shapes: BTreeMap::new(),
            current_algebraic_params: BTreeMap::new(),
            current_click_type_parameters: BTreeSet::new(),
            current_contract_bindings: BTreeSet::new(),
            algebraic_variant_fields: BTreeMap::new(),
            current_arm_binding_types: BTreeMap::new(),
            current_integer_params: BTreeSet::new(),
            current_integer_lets: BTreeSet::new(),
            current_proof_let_names: BTreeSet::new(),
            proof_let_restores: Vec::new(),
            callee_resource_binders: BTreeMap::new(),
            in_contract_definition: false,
            integer_literal_context: false,
        })
    }

    fn parse_file(mut self) -> Result<ClickFile, ClickError> {
        let file = self.parse_file_items()?;
        let mut file = super::validation::expand_declared_resource_clauses(file)
            .map_err(|error| error.with_kind(ClickErrorKind::Type))?;
        super::validation::validate_click_definitions(&file)
            .map_err(|error| error.with_kind(ClickErrorKind::Type))?;
        super::lowering::check_resource_field_schemas(&mut file)
            .map_err(|error| error.with_kind(ClickErrorKind::Type))?;
        Ok(file)
    }

    /// Records each `spec enum` variant's declared field types before any item
    /// is parsed, so a resource's match arm can type its constructor bindings
    /// against a datatype declared anywhere in the file. The scan visits the
    /// token stream once and parses only the datatype declarations; the item
    /// loop then parses the same declarations again as the definitions the
    /// file carries. A declaration that does not parse is skipped without a
    /// diagnostic of its own: the item loop reaches it and reports the error
    /// in the order the file is written.
    fn index_algebraic_variant_fields(&mut self) {
        let resume = self.position;
        // Closing a nested datatype argument list rewrites the `>>` it ends on
        // into a single `>` and leaves it for the enclosing list to consume,
        // so the rewrite is not idempotent: a second parse would spend that
        // `>` on the inner list and fail on the outer one. Put every `>>` back
        // before the item loop reads the same tokens.
        let shift_rights = self
            .tokens
            .iter()
            .enumerate()
            .filter(|(_, token)| **token == Token::ShiftRight)
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        self.position = 0;
        let mut depth = 0usize;
        while self.position < self.tokens.len() {
            crate::instrumentation::record_deterministic_work(1);
            let declares_datatype = depth == 0
                && self.peek_ident() == Some("spec")
                && matches!(self.peek_next(), Some(Token::Ident(next)) if next == "enum");
            if declares_datatype {
                let declaration = self.position;
                match self.parse_algebraic_type_definition() {
                    Ok(definition) => {
                        for variant in definition.variants() {
                            self.algebraic_variant_fields
                                .entry((definition.name().to_string(), variant.name().to_string()))
                                .or_insert_with(|| variant.fields().to_vec());
                        }
                    }
                    // Resume from just after the `spec`, so the rest of the
                    // file is still indexed and the brace depth counts every
                    // token this scan walked past.
                    Err(_) => self.position = declaration + 1,
                }
                continue;
            }
            match self.peek() {
                Some(Token::LBrace) => depth += 1,
                Some(Token::RBrace) => depth = depth.saturating_sub(1),
                _ => {}
            }
            self.position += 1;
        }
        for index in shift_rights {
            self.tokens[index] = Token::ShiftRight;
        }
        self.position = resume;
    }

    fn parse_file_items(&mut self) -> Result<ClickFile, ClickError> {
        self.index_algebraic_variant_fields();
        let mut imports = Vec::new();
        let mut verifying_sources = Vec::new();
        let mut c_target = None;
        let mut thread_runtime = None;
        let mut algebraic_type_definitions = Vec::new();
        let mut predicate_definitions = Vec::new();
        let mut click_function_definitions = Vec::new();
        let mut resource_definitions = Vec::new();
        let mut theorem_definitions = Vec::new();
        let mut deferred_theorems = Vec::new();
        let mut contract_definitions = Vec::new();
        let mut function_blocks = Vec::new();

        while self.peek().is_some() {
            if self.peek_ident() == Some("import") {
                imports.push(self.parse_import()?);
            } else if self.peek_ident() == Some("verifying") {
                verifying_sources.push(self.parse_verifying_source()?);
            } else if self.peek_ident() == Some("target")
                && matches!(self.peek_next(), Some(Token::String(_)))
            {
                let target = self.parse_c_target()?;
                if c_target.is_some() {
                    return Err(self.error("a Click file declares more than one `target`"));
                }
                c_target = Some(target);
            } else if self.peek_ident() == Some("runtime")
                && matches!(self.peek_next(), Some(Token::String(_)))
            {
                let runtime = self.parse_thread_runtime()?;
                if thread_runtime.is_some() {
                    return Err(self.error("a Click file declares more than one `runtime`"));
                }
                thread_runtime = Some(runtime);
            } else if self.peek_ident() == Some("spec") {
                algebraic_type_definitions.push(self.parse_algebraic_type_definition()?);
            } else if self.peek_ident() == Some("predicate") {
                predicate_definitions.push(self.parse_predicate_definition()?);
            } else if self.peek_ident() == Some("function") {
                click_function_definitions.push(self.parse_click_function_definition()?);
            } else if self.peek_ident() == Some("theorem") {
                // An executes conclusion's `as` map is checked against the
                // target contract's proof parameters, including when that
                // contract is declared later. Visit each declaration's tokens
                // once here, then parse it after the contract index is
                // complete.
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
            imports,
            verifying_sources,
            c_target,
            thread_runtime: thread_runtime.unwrap_or_default(),
            algebraic_type_definitions,
            predicate_definitions,
            click_function_definitions,
            resource_definitions,
            theorem_definitions,
            contract_definitions,
            function_blocks,
            declaration_owners: BTreeMap::new(),
            entry_module: None,
        };
        Ok(file)
    }

    fn parse_import(&mut self) -> Result<ImportDeclaration, ClickError> {
        let position = self
            .here()
            .unwrap_or_else(|| crate::source::SourcePosition::new(1, 1));
        self.expect_ident_spelling("import")?;
        let path = self.expect_string("Click module path")?;
        self.expect(Token::Semicolon)?;
        Ok(ImportDeclaration { path, position })
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
        let previous_in_contract = std::mem::replace(&mut self.in_contract_definition, true);
        let function_block = self.parse_function_block(false);
        self.in_contract_definition = previous_in_contract;
        let function_block = function_block?;
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
        if name == "Integer" {
            return Err(self.error("`Integer` is reserved for the mathematical specification type"));
        }
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
            // Only a declared `struct tag*` records a tag: a bare
            // `struct tag` is not a pointer to a laid-out object and a
            // `struct tag**` does not point at one either, so neither is a
            // memory base in a match arm.
            let struct_name = if parsed.struct_pointer && parsed.c_type == C0Type::Int32Pointer {
                parsed.struct_name
            } else {
                None
            };
            return Ok(AlgebraicFieldType::C {
                c_type: parsed.c_type,
                struct_name,
            });
        }
        if name == "Integer" {
            self.position += 1;
            return Ok(AlgebraicFieldType::Integer);
        }

        self.position += 1;
        if self.peek() == Some(&Token::LessThan) {
            if self.algebraic_type_nesting >= ALGEBRAIC_TYPE_NESTING_LIMIT {
                return Err(self.error(format!(
                    "algebraic datatype nesting exceeds Click's supported depth of {ALGEBRAIC_TYPE_NESTING_LIMIT}"
                )));
            }
            self.algebraic_type_nesting += 1;
            let result = self.parse_algebraic_field_type_arguments(name, type_parameters);
            self.algebraic_type_nesting -= 1;
            return result;
        }
        Ok(AlgebraicFieldType::Algebraic {
            name,
            arguments: Vec::new(),
        })
    }

    fn parse_algebraic_field_type_arguments(
        &mut self,
        name: String,
        type_parameters: &[String],
    ) -> Result<AlgebraicFieldType, ClickError> {
        self.position += 1;
        let mut arguments = Vec::new();
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

    /// Parses `target "x86_64-linux-kernel";`, the C implementation target
    /// this file's C sources are preprocessed and verified under. The
    /// accepted spellings come from `CTarget` itself, so this and the
    /// pre-parse scan in `expansion` never drift apart.
    fn parse_c_target(&mut self) -> Result<crate::languages::c::target::CTarget, ClickError> {
        self.expect_ident_spelling("target")?;
        let at = self.error_context();
        let name = self.expect_string("C target name")?;
        self.expect(Token::Semicolon)?;
        crate::languages::c::target::CTarget::from_name(&name).ok_or_else(|| {
            self.error_at(
                at,
                format!(
                    "unknown C target `{name}`; accepted targets are {}",
                    crate::languages::c::target::CTarget::accepted_names()
                ),
            )
        })
    }

    fn parse_thread_runtime(
        &mut self,
    ) -> Result<crate::languages::c::thread_runtime::CThreadRuntime, ClickError> {
        self.expect_ident_spelling("runtime")?;
        let at = self.error_context();
        let name = self.expect_string("C thread runtime name")?;
        self.expect(Token::Semicolon)?;
        crate::languages::c::thread_runtime::CThreadRuntime::from_name(&name).ok_or_else(|| {
            self.error_at(
                at,
                format!("unknown C thread runtime `{name}`; accepted runtime is `modeled-pthread`"),
            )
        })
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
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
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
        let previous_definition = std::mem::replace(&mut self.in_resource_definition, true);
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
        self.in_resource_definition = previous_definition;
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

    /// Types a match arm's constructor bindings from the indexed datatype.
    /// A binding of struct-pointer type joins `current_struct_params`, which
    /// is what makes `parent->left` in the arm resolve against
    /// `struct tree_node`'s layout; every other binding is recorded only so
    /// that using it as a memory base is refused with its declared type. A
    /// pattern this index cannot resolve, because the datatype or the arity is
    /// wrong, is left to the validation that reports exactly that.
    fn bind_arm_binding_types(&mut self, type_name: &str, variant: &str, bindings: &[String]) {
        let Some(fields) = self
            .algebraic_variant_fields
            .get(&(type_name.to_string(), variant.to_string()))
            .filter(|fields| fields.len() == bindings.len())
            .cloned()
        else {
            return;
        };
        for (binding, field) in bindings.iter().zip(fields) {
            match field.struct_pointer_name() {
                Some(struct_name) => {
                    self.current_struct_params
                        .insert(binding.clone(), struct_name.to_string());
                }
                // The binding shadows any enclosing name for the arm, so an
                // outer struct parameter must not keep lending it a layout.
                None => {
                    self.current_struct_params.remove(binding);
                }
            }
            self.current_arm_binding_types
                .insert(binding.clone(), field);
        }
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
        let guarded_by = if self.peek_ident() == Some("guarded_by") {
            self.position += 1;
            let mutex = self.parse_guarded_by_mutex_field()?;
            self.expect(Token::Semicolon)?;
            Some(mutex)
        } else {
            None
        };
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
                let saved_struct_params = self.current_struct_params.clone();
                let saved_arm_binding_types = std::mem::take(&mut self.current_arm_binding_types);
                self.bind_arm_binding_types(&type_name, &variant, &bindings);
                let body = self.parse_composite_resource_body(resource_name);
                self.current_resource_bindings = saved_bindings;
                self.current_resource_targets = saved_targets;
                self.current_struct_params = saved_struct_params;
                self.current_arm_binding_types = saved_arm_binding_types;
                self.match_nesting -= 1;
                let body = body?;
                for name in inserted {
                    self.current_contract_bindings.remove(&name);
                }
                if body
                    .contains
                    .iter()
                    .any(|clause| matches!(clause, ResourceClause::Iterated(_)))
                {
                    return Err(self.error(
                        "iterated ownership (`forall ... { owns ...; }`) is supported in an unmatched resource body, not inside a match arm",
                    ));
                }
                if !body.fields.is_empty()
                    || body.guarded_by.is_some()
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
                guarded_by,
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
                Some("guarded_by") => return Err(self.error("`guarded_by` must appear once before the resource body clauses")),
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
                    if self.current_resource_fields.is_empty()
                        && self.peek_next() == Some(&Token::Colon)
                    {
                        return Err(self.error(
                            "a named child resource requires a field-bearing parent resource",
                        ));
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
                Some("forall") => {
                    contains.push(self.parse_iterated_resource_clause(resource_name)?);
                }
                Some(name) => {
                    return Err(self.error(format!(
                        "expected `contains`, `owns`, `views`, `fact`, `forall`, or `let` in resource body, got `{name}`"
                    )));
                }
                None => {
                    return Err(self.error(
                        "expected `contains`, `owns`, `views`, `fact`, `forall`, or `let` in resource body, got end of input",
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
            guarded_by,
            matched: None,
            condition,
            contains,
            facts,
            witnesses,
        })
    }

    fn parse_guarded_by_mutex_field(&mut self) -> Result<ContractSegment, ClickError> {
        let parameter = self.expect_ident("resource's struct pointer parameter")?;
        self.expect(Token::Arrow)?;
        let field_name = self.expect_ident("pthread mutex field")?;
        let struct_name = self.current_struct_params.get(&parameter).ok_or_else(|| {
            self.error(format!(
                "`guarded_by {parameter}->{field_name}` requires a struct pointer parameter"
            ))
        })?;
        let field = self.resolve_struct_field_metadata(struct_name, &field_name)?;
        let Some(union_name) = field.union_name.as_deref() else {
            return Err(self.error("`guarded_by` requires a `pthread_mutex_t` field"));
        };
        let Some(layout) = self.union_layouts.get(union_name) else {
            return Err(self.error("`guarded_by` mutex type has no imported layout"));
        };
        if !matches!(union_name, "__click_pthread_mutex" | "pthread_mutex_t")
            || layout.size_bytes() != 40
            || layout.alignment_bytes() != 8
            || field.byte_width != 40
            || !field.offset_bytes.is_multiple_of(8)
        {
            return Err(self
                .error("`guarded_by` requires a 40-byte, 8-byte-aligned `pthread_mutex_t` field"));
        }
        Ok(Self::field_segment_from_metadata(
            CExpression::Variable(parameter.clone()),
            Some(ContractExpression::CFragment(CExpression::Variable(
                parameter,
            ))),
            &field_name,
            &field,
        ))
    }

    /// `forall (k: int32) where <range> { [if <guard> {] owns <segment>; [}] }`
    /// inside a resource body. The binder is a C `int32` name for the range,
    /// the guard, and the element segment, and for nothing after the clause.
    fn parse_iterated_resource_clause(
        &mut self,
        resource_name: &str,
    ) -> Result<ResourceClause, ClickError> {
        self.expect_ident_spelling("forall")?;
        self.expect(Token::LParen)?;
        let binder = self.expect_ident("iterated ownership index name")?;
        self.expect(Token::Colon)?;
        let (click_type, _) = self.parse_click_type()?;
        if click_type != ClickType::C(C0Type::Int32) {
            return Err(self.error(format!(
                "iterated ownership index `{binder}` must have type `int32`"
            )));
        }
        self.expect(Token::RParen)?;
        if self.peek_ident() != Some("where") {
            return Err(self.error(format!(
                "iterated ownership needs a bounded index: write `forall ({binder}: int32) where lo <= {binder} and {binder} < hi {{ ... }}`"
            )));
        }
        self.position += 1;
        let integer_was_bound = self.current_integer_params.remove(&binder);
        let integer_let_was_bound = self.current_integer_lets.remove(&binder);
        let c_was_bound = self.current_contract_bindings.remove(&binder);
        let parsed = (|| {
            let range = self.parse_proposition()?;
            self.expect(Token::LBrace)?;
            let guard = if self.peek_ident() == Some("if") {
                self.position += 1;
                let guard = self.parse_proposition()?;
                self.expect(Token::LBrace)?;
                Some(guard)
            } else {
                None
            };
            let mut elements = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                match self.peek_ident() {
                    Some("owns") => {
                        self.position += 1;
                        elements.push(self.parse_resource_target(ResourceAccessMode::Own)?);
                        self.expect(Token::Semicolon)?;
                    }
                    Some(other) => {
                        return Err(self.error(format!(
                            "an iterated ownership clause holds `owns` element ranges only, got `{other}`"
                        )));
                    }
                    None => {
                        return Err(self.error(
                            "an iterated ownership clause holds `owns` element ranges only",
                        ));
                    }
                }
            }
            self.expect(Token::RBrace)?;
            if guard.is_some() {
                self.expect(Token::RBrace)?;
            }
            Ok((range, guard, elements))
        })();
        if integer_was_bound {
            self.current_integer_params.insert(binder.clone());
        }
        if integer_let_was_bound {
            self.current_integer_lets.insert(binder.clone());
        }
        if c_was_bound {
            self.current_contract_bindings.insert(binder.clone());
        }
        let (range, guard, elements) = parsed?;
        let [ResourceClause::OwnMemory(element)] = <[ResourceClause; 1]>::try_from(elements)
            .map_err(|elements| {
                self.error(format!(
                    "an iterated ownership clause owns exactly one element range per index, found {}",
                    elements.len()
                ))
            })?
        else {
            return Err(self.error(
                "an iterated ownership clause owns one memory range `base[start..end]` per index",
            ));
        };
        let clause = IteratedResourceClause {
            owner: resource_name.to_string(),
            binder,
            range,
            guard,
            element,
        };
        if clause.guard.is_none() {
            // Unconditional iterated ownership of one cell per index is the
            // plain range; it lowers to exactly the clause `owns base[lo..hi]`.
            return crate::surface::lowering::unguarded_iterated_clause_as_range(&clause)
                .map(ResourceClause::OwnMemory)
                .map_err(|message| self.error(message));
        }
        Ok(ResourceClause::Iterated(Box::new(clause)))
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
        let previous_integer_params = std::mem::replace(
            &mut self.current_integer_params,
            parsed_parameters
                .parameters
                .iter()
                .filter(|parameter| matches!(parameter.click_type(), ClickType::Integer))
                .map(|parameter| parameter.name().to_string())
                .collect(),
        );
        let previous_integer_literal_context =
            std::mem::replace(&mut self.integer_literal_context, false);
        let previous_integer_lets = std::mem::take(&mut self.current_integer_lets);
        let executes = if self.peek_ident() == Some("executes") {
            self.position += 1;
            let callback = self.expect_ident("callback parameter")?;
            self.expect(Token::LParen)?;
            let call_parameters = self.parse_parameters()?;
            self.expect(Token::RParen)?;
            Some(TheoremExecution {
                callback,
                parameters: call_parameters.parameters,
                target_instances: Vec::new(),
            })
        } else {
            None
        };
        let mut target_instances = Vec::new();
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
                    if matches!(
                        contract_lets
                            .last()
                            .and_then(|binding| binding.click_type.as_ref()),
                        Some(ClickType::Integer)
                    ) {
                        // The let is substituted into later clauses, so keep
                        // its literal context active while those clauses are
                        // parsed instead of losing the annotation first.
                        self.integer_literal_context = true;
                        self.current_integer_lets.insert(
                            contract_lets
                                .last()
                                .expect("just pushed let binding")
                                .name
                                .clone(),
                        );
                    }
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
                                borrowed: true,
                                condition: None,
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
                                borrowed: false,
                                condition: None,
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
                        let (ensure, introduced) =
                            self.parse_ensure_clause_with_execution_scope(Some(&names))?;
                        target_instances.extend(introduced);
                        ensure
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
        self.current_integer_params = previous_integer_params;
        self.current_integer_lets = previous_integer_lets;
        self.integer_literal_context = previous_integer_literal_context;

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
            executes: executes.map(|execution| TheoremExecution {
                target_instances,
                ..execution
            }),
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
        let parameter_names_in_order = signature
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<Vec<_>>();
        let previous_integer_params = std::mem::take(&mut self.current_integer_params);
        let previous_integer_lets = std::mem::take(&mut self.current_integer_lets);
        let previous_integer_literal_context =
            std::mem::replace(&mut self.integer_literal_context, false);
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut decreases = None;
        let mut constructs = Vec::new();
        let mut ensures = Vec::new();
        let mut exceptional_ensures = Vec::new();
        // A local of struct-pointer type is a memory base in this function's
        // proof just as a parameter is. The signature wins a shared spelling.
        for (name, struct_name) in self
            .local_struct_pointers_by_function
            .get(signature.name())
            .into_iter()
            .flatten()
        {
            struct_params
                .entry(name.clone())
                .or_insert_with(|| struct_name.clone());
        }
        let previous_struct_params =
            std::mem::replace(&mut self.current_struct_params, struct_params);
        let previous_void_pointer_params = std::mem::replace(
            &mut self.current_void_pointer_params,
            signature
                .parameters()
                .iter()
                .filter(|parameter| parameter.c_type() == C0Type::VoidPointer)
                .map(|parameter| parameter.name().to_string())
                .collect(),
        );
        let previous_parameter_struct_casts =
            std::mem::take(&mut self.current_parameter_struct_casts);
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
                    if matches!(
                        contract_lets
                            .last()
                            .and_then(|binding| binding.click_type.as_ref()),
                        Some(ClickType::Integer)
                    ) {
                        self.integer_literal_context = true;
                        self.current_integer_lets.insert(
                            contract_lets
                                .last()
                                .expect("just pushed let binding")
                                .name
                                .clone(),
                        );
                    }
                }
                Some("requires") => {
                    let requirement = self.parse_requirement()?;
                    requires.push(
                        apply_contract_lets_to_requirement(requirement, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("if") => {
                    self.position += 1;
                    let condition = self.parse_proposition()?;
                    self.expect(Token::LBrace)?;
                    while self.peek() != Some(&Token::RBrace) {
                        if self.peek_ident() != Some("produces") {
                            let keyword = self.peek_ident().unwrap_or("end of input");
                            return Err(self.error(format!(
                                "conditional function contracts currently accept only `produces`, got `{keyword}`"
                            )));
                        }
                        self.position += 1;
                        let resource = self.parse_owned_resource_binding()?;
                        if matches!(resource, ResourceClause::Named { .. }) {
                            return Err(self.error(
                                "conditional `produces` clauses cannot introduce named resource instances yet",
                            ));
                        }
                        let proof = self.parse_proof_clause_or_default()?;
                        ensures.push(
                            apply_contract_lets_to_ensure_clause(
                                EnsureClause {
                                    name: None,
                                    ensure: Ensure::Resource(resource),
                                    proof,
                                    borrowed: false,
                                    condition: Some(condition.clone()),
                                },
                                &contract_lets,
                            )
                            .map_err(|message| self.error(message))?,
                        );
                    }
                    self.expect(Token::RBrace)?;
                }
                Some("decreases") => {
                    self.position += 1;
                    if decreases.is_some() {
                        return Err(self.error(format!(
                            "duplicate `decreases` clause in `{}`",
                            signature.name()
                        )));
                    }
                    // D6: one expression, classified after resolution.
                    // `decreases n;`, `decreases list(node);`, and
                    // `decreases sub;` are the same syntax here; declared
                    // resource expansion decides which measure each one is.
                    let measure = self.parse_contract_expression()?;
                    self.expect(Token::Semicolon)?;
                    decreases = Some(CFunctionDecrease::Unresolved(
                        substitute_contract_expression(
                            &measure,
                            &contract_let_substitutions(&contract_lets),
                        )
                        .map_err(|message| self.error(message))?,
                    ));
                }
                Some("owns") => {
                    self.position += 1;
                    let resource = self.parse_owned_resource_binding()?;
                    let proof = self.parse_proof_clause_or_default()?;
                    let binder_resource =
                        apply_contract_lets_to_resource_clause(resource.clone(), &contract_lets)
                            .map_err(|message| self.error(message))?;
                    self.record_callee_resource_binder(
                        signature.name(),
                        &binder_resource,
                        &parameter_names_in_order,
                        CalleeResourceBinderKind::Supplied,
                    );
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
                                borrowed: true,
                                condition: None,
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
                    let binder_resource =
                        apply_contract_lets_to_resource_clause(resource.clone(), &contract_lets)
                            .map_err(|message| self.error(message))?;
                    self.record_callee_resource_binder(
                        signature.name(),
                        &binder_resource,
                        &parameter_names_in_order,
                        CalleeResourceBinderKind::Supplied,
                    );
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
                    let binder_resource =
                        apply_contract_lets_to_resource_clause(resource.clone(), &contract_lets)
                            .map_err(|message| self.error(message))?;
                    self.record_callee_resource_binder(
                        signature.name(),
                        &binder_resource,
                        &parameter_names_in_order,
                        CalleeResourceBinderKind::Produced,
                    );
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                name: None,
                                ensure: Ensure::Resource(resource),
                                proof,
                                borrowed: false,
                                condition: None,
                            },
                            &contract_lets,
                        )
                        .map_err(|message| self.error(message))?,
                    );
                }
                Some("immutable" | "mutable") => {
                    return Err(self.error(
                        "effect clauses were removed; declare ownership with `owns` and `views` (a narrow write is `views X; owns Y;`)",
                    ));
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
                    if let Ensure::Proposition(proposition) = ensure.ensure() {
                        let mut variables = BTreeSet::new();
                        collect_current_proposition_variables(proposition, &mut variables);
                        if variables.contains("exception") {
                            return Err(self.error(
                                "`exception` is available only in an `exceptional ensures` clause",
                            ));
                        }
                    }
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(ensure, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("exceptional") => {
                    if signature.exceptional_type().is_none() {
                        return Err(self.error(format!(
                            "`exceptional ensures` requires `throws int32` in the signature of `{}`",
                            signature.name()
                        )));
                    }
                    self.position += 1;
                    self.expect_ident_spelling("ensures")?;
                    let ensure = self.parse_ensure_clause_after_keyword()?;
                    let Ensure::Proposition(proposition) = ensure.ensure() else {
                        return Err(
                            self.error("exceptional postconditions must be pure propositions")
                        );
                    };
                    let mut variables = BTreeSet::new();
                    collect_current_proposition_variables(proposition, &mut variables);
                    if variables.contains("result") {
                        return Err(self.error(
                            "`result` is not available in an `exceptional ensures` clause; use `exception` for the thrown payload",
                        ));
                    }
                    exceptional_ensures.push(
                        apply_contract_lets_to_ensure_clause(ensure, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `decreases`, `owns`, `views`, `consumes`, `produces`, `constructs`, `ensures`, `exceptional ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `decreases`, `owns`, `views`, `consumes`, `produces`, `constructs`, `ensures`, or `}}` in `{}`",
                        signature.name()
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let grouped_proof = if self.peek_ident() == Some("by") {
            let proof = self.parse_by_clause()?;
            if ensures
                .iter()
                .chain(exceptional_ensures.iter())
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
        if external
            && (decreases.is_some()
                || grouped_proof.is_some()
                || ensures
                    .iter()
                    .chain(exceptional_ensures.iter())
                    .any(|ensure| !matches!(ensure.proof(), SourceProof::Default)))
        {
            return Err(
                self.error("external function contracts cannot carry proof or decreases clauses")
            );
        }
        if external && signature.exceptional_type().is_some() {
            return Err(
                self.error("external exceptional contracts are not supported in this slice")
            );
        }
        if signature.exceptional_type().is_some()
            && (!constructs.is_empty()
                || requires
                    .iter()
                    .any(|requirement| matches!(requirement.inner(), Requirement::Resource(_)))
                || ensures
                    .iter()
                    .any(|ensure| matches!(ensure.ensure(), Ensure::Resource(_))))
        {
            return Err(self.error(
                "exceptional contracts with resources or mutable effects are not supported in this slice",
            ));
        }
        // `diverges` says the function may not return, so it cannot also ask
        // for the termination evidence a `decreases` clause requests, and
        // every loop that says it may not exit needs the function to say so.
        if signature.diverges() && decreases.is_some() {
            return Err(self.error(format!(
                "`{}` is declared `diverges` and cannot also carry a function-level `decreases` clause",
                signature.name()
            )));
        }
        if !signature.diverges() {
            let mut loop_clauses = Vec::new();
            if let Some(proof) = &grouped_proof {
                proof.collect_termination_loop_clauses(&mut loop_clauses);
            }
            for ensure in ensures.iter().chain(exceptional_ensures.iter()) {
                ensure
                    .proof()
                    .collect_termination_loop_clauses(&mut loop_clauses);
            }
            if let Some(clause) = loop_clauses.iter().find(|clause| clause.diverges()) {
                return Err(self.error(format!(
                    "{} in `{}` is declared `diverges`, so `{}` must be declared `diverges` too",
                    loop_clause_description(clause.label()),
                    signature.name(),
                    signature.name()
                )));
            }
        }
        self.current_struct_params = previous_struct_params;
        self.current_void_pointer_params = previous_void_pointer_params;
        let parameter_struct_casts = std::mem::replace(
            &mut self.current_parameter_struct_casts,
            previous_parameter_struct_casts,
        );
        self.current_resource_bindings = previous_resource_bindings;
        self.current_resource_targets = previous_resource_targets;
        self.current_aggregate_objects = previous_aggregate_objects;
        self.current_global_array_shapes = previous_global_array_shapes;
        self.current_struct_array_params = previous_struct_array_params;
        self.current_integer_params = previous_integer_params;
        self.current_integer_lets = previous_integer_lets;
        self.integer_literal_context = previous_integer_literal_context;

        // Flattening an aggregate clause keeps the clause the author wrote
        // beside each member, so diagnostics number clauses as written.
        let mut requirement_source_clauses = Vec::new();
        let requires: Vec<Requirement> = requires
            .into_iter()
            .enumerate()
            .flat_map(|(source, requirement)| {
                let expanded = expand_aggregate_requirement(requirement);
                requirement_source_clauses.extend(std::iter::repeat_n(source, expanded.len()));
                expanded
            })
            .collect();
        let constructs: Vec<ResourceClause> = constructs
            .into_iter()
            .flat_map(expand_aggregate_resource_clause)
            .collect();
        let mut ensure_source_clauses = Vec::new();
        let ensures: Vec<EnsureClause> = ensures
            .into_iter()
            .enumerate()
            .flat_map(|(source, ensure)| {
                let expanded = expand_aggregate_ensure_clause(ensure);
                ensure_source_clauses.extend(std::iter::repeat_n(source, expanded.len()));
                expanded
            })
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
            requirement_source_clauses,
            requirement_label_indices,
            decreases,
            structural_clauses: Vec::new(),
            constructs,
            ensures,
            exceptional_ensures,
            ensure_source_clauses,
            grouped_proof,
            parameter_struct_casts,
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
            let previous_integer_literal_context = std::mem::replace(
                &mut self.integer_literal_context,
                matches!(click_type.as_ref(), Some(ClickType::Integer)),
            );
            let value = self.parse_contract_expression();
            self.integer_literal_context = previous_integer_literal_context;
            ContractLetBindingKind::Value(value?)
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
        let pending_contract_name = self.pending_contract_name.take();
        let is_named_contract = pending_contract_name.is_some();
        let name = match pending_contract_name {
            Some(name) => name,
            None => self.expect_ident("function name")?,
        };
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let exceptional_type = if self.peek_ident() == Some("throws") {
            self.position += 1;
            let parsed = self.parse_type()?;
            if parsed.constant
                || parsed.pointee_constant
                || parsed.struct_name.is_some()
                || parsed.c_type != C0Type::Int32
            {
                return Err(self.error("the exceptional payload type must be `int32`"));
            }
            if is_named_contract {
                return Err(
                    self.error("named exceptional contracts are not supported in this slice")
                );
            }
            Some(C0Type::Int32)
        } else {
            None
        };
        // `diverges` is contextual: only the position right after the
        // parameter list, or right after a `throws` payload type, gives the
        // spelling its meaning. The order is fixed so one signature has one
        // spelling.
        let diverges = if self.peek_ident() == Some("diverges") {
            self.position += 1;
            true
        } else {
            false
        };
        if diverges && self.peek_ident() == Some("throws") {
            return Err(self.error("`throws` must come before `diverges` in a signature"));
        }
        let struct_params = parsed_parameters.struct_params;
        let struct_array_params = parsed_parameters.struct_array_params;

        Ok(ParsedFunctionSignature {
            signature: FunctionSignature {
                return_type,
                return_pointee_constant: parsed_return_type.pointee_constant,
                name,
                parameters: parsed_parameters.parameters,
                exceptional_type,
                diverges,
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

        let integer = crate::languages::c::integer_specifiers::parse(
            std::iter::once(spelling.as_str()).chain(
                self.tokens[self.position..]
                    .iter()
                    .map_while(|token| match token {
                        Token::Ident(word) => Some(word.as_str()),
                        _ => None,
                    }),
            ),
        )
        .map_err(|message| self.error(message))?;
        let scalar_type = if let Some((c_type, count)) = integer {
            self.position += count - 1;
            c_type
        } else {
            match spelling.as_str() {
                "void" => C0Type::Void,
                "_Bool" | "bool" => C0Type::Bool,
                "int8" | "int8_t" => C0Type::Int8,
                "int16" | "int16_t" => C0Type::Int16,
                "int32" | "int32_t" => C0Type::Int32,
                "uint8" | "uint8_t" => C0Type::UInt8,
                "uint16" | "uint16_t" => C0Type::UInt16,
                "uint32" | "uint32_t" => C0Type::UInt32,
                "int64" | "int64_t" | "ssize_t" => C0Type::Int64,
                "uint64" | "size_t" | "uint64_t" => C0Type::UInt64,
                "float" => C0Type::Float32,
                "double" => C0Type::Float64,
                "volatile" => {
                    return Err(self.error("the `volatile` qualifier is not supported in C0"));
                }
                _ => {
                    return Err(self.error(format!(
                    "unknown C type `{spelling}`; expected a supported standard spelling or `struct`"
                )));
                }
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
                C0Type::Int8 => C0Type::Int8Pointer,
                C0Type::Int16 => C0Type::Int16Pointer,
                C0Type::UInt16 => C0Type::UInt16Pointer,
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::Char => C0Type::CharPointer,
                C0Type::UInt8 => C0Type::UInt8Pointer,
                C0Type::UInt32 => C0Type::UInt32Pointer,
                C0Type::Int64 => C0Type::Int64Pointer,
                C0Type::UInt64 => C0Type::UInt64Pointer,
                C0Type::Int8Pointer => C0Type::Int8PointerPointer,
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
        if name == "Integer" {
            self.position += 1;
            return Ok((ClickType::Integer, None));
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
                    C0Type::Int8 | C0Type::Int16
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
                        | C0Type::Int64Array(_)
                        | C0Type::UInt64Array(_)
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
                        // A callback field is an eight-byte pointer value,
                        // matching the C boundary's own by-value field set.
                        | C0Type::FunctionPointer(_)
                )
            {
                return Err(self.error(format!(
                    "struct-by-value currently supports modeled integer and floating-point fields, fixed scalar arrays, fixed-dimensional embedded-struct arrays, data-pointer fields, function-pointer fields, embedded struct fields, and named union fields; `struct {struct_name}` contains an unsupported field shape"
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
            C0Type::Int8 => (C0Type::Int8Pointer, 1),
            C0Type::Int16 => (C0Type::Int16Pointer, 2),
            C0Type::Int32 => (C0Type::Int32Pointer, 4),
            C0Type::Char => (C0Type::CharPointer, 1),
            C0Type::UInt8 => (C0Type::UInt8Pointer, 1),
            C0Type::UInt16 => (C0Type::UInt16Pointer, 2),
            C0Type::UInt32 => (C0Type::UInt32Pointer, 4),
            C0Type::Int64 => (C0Type::Int64Pointer, 8),
            C0Type::UInt64 => (C0Type::UInt64Pointer, 8),
            C0Type::Int8Pointer => (C0Type::Int8PointerPointer, 8),
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
        if matches!(self.peek(), Some(Token::Ident(_))) && self.peek_next() == Some(&Token::Colon) {
            return Err(
                self.error("named `requires` facts were removed; write `requires proposition;`")
            );
        }
        let requirement = match (self.peek_ident(), self.peek_next()) {
            (Some("viewable"), Some(Token::LParen)) => self.parse_loadable_requirement()?,
            (Some("loadable"), Some(Token::LParen)) => {
                return Err(self.error(RETIRED_LOADABLE_SPELLING));
            }
            _ => {
                let proposition = self.parse_proposition()?;
                self.expect(Token::Semicolon)?;
                Requirement::Proposition(proposition)
            }
        };
        if !matches!(requirement, Requirement::Proposition(_)) {
            self.expect(Token::Semicolon)?;
        }
        Ok(requirement)
    }

    fn parse_loadable_requirement(&mut self) -> Result<Requirement, ClickError> {
        match self.peek_ident() {
            Some("viewable") => {
                self.position += 1;
            }
            _ => return Err(self.error("expected `viewable` requirement")),
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
        let segments = self.parse_current_contract_segments_inner(
            access != ResourceAccessMode::View || self.in_resource_definition,
        )?;
        if access == ResourceAccessMode::View
            && !self.in_resource_definition
            && (segments.len() > 1
                || segments
                    .iter()
                    .any(|segment| matches!(segment.surface, ContractSegmentSurface::Object(_))))
        {
            return Err(self.error("whole-struct views require a declared resource"));
        }
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

    /// A `step(` argument that opens the chunk-5 call form: an identifier, a
    /// parenthesized argument list, and a comma introducing the binder map.
    /// The closing parenthesis comes from the precomputed nesting table, so
    /// the decision costs one lookup rather than a scan.
    fn call_binder_transport_follows(&self) -> bool {
        if !matches!(self.peek(), Some(Token::Ident(_))) || self.peek_next() != Some(&Token::LParen)
        {
            return false;
        }
        let Some(close) = self
            .matching_parentheses
            .get(self.position + 1)
            .cloned()
            .flatten()
        else {
            return false;
        };
        self.tokens.get(close + 1) == Some(&Token::Comma)
    }

    /// `callee(arguments), { binder: instance, ... }`, positioned after the
    /// opening parenthesis of `step(`. Produced instances are named by the
    /// surrounding `let` output pattern.
    fn parse_call_binder_transport(
        &mut self,
        output: Option<CallOutputPattern>,
    ) -> Result<CallBinderTransport, ClickError> {
        let callee = self.expect_ident("call step callee")?;
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            arguments.push(self.parse_contract_expression()?);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        self.expect(Token::Comma)?;
        let declared = self
            .callee_resource_binders
            .get(&callee)
            .cloned()
            .unwrap_or_default();
        self.expect(Token::LBrace)?;
        let mut binders: Vec<CallBinderBinding> = Vec::new();
        let mut bound = BTreeSet::new();
        let mut instances = BTreeSet::new();
        while self.peek() != Some(&Token::RBrace) {
            let binder = self.expect_ident("callee resource binder")?;
            self.expect(Token::Colon)?;
            let instance = self.expect_ident("caller resource instance")?;
            crate::instrumentation::record_deterministic_work(1);
            if callee == "pthread_mutex_init" {
                if binder != "invariant" {
                    return Err(
                        self.error("`pthread_mutex_init` call map requires `invariant: instance`")
                    );
                }
                if !bound.insert(binder.clone()) {
                    return Err(self.error("duplicate `invariant` in the mutex init call map"));
                }
                let Some((identity, _)) = self.current_resource_bindings.get(&instance).cloned()
                else {
                    return Err(self.error(format!("unknown resource instance `{instance}`")));
                };
                binders.push(CallBinderBinding {
                    binder,
                    binder_identity: Variable(u64::MAX - 1),
                    instance,
                    identity,
                });
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let Some(declaration) = declared.get(&binder) else {
                return Err(self.error(format!(
                    "`{callee}` declares no resource instance binder `{binder}`"
                )));
            };
            if declaration.kind == CalleeResourceBinderKind::Produced {
                return Err(self.error(format!(
                    "`{callee}` produces `{binder}`; introduce it with `let {binder} = step(...)`"
                )));
            }
            if !bound.insert(binder.clone()) {
                return Err(self.error(format!("duplicate binder `{binder}` in the call map")));
            }
            let Some((identity, family)) = self.current_resource_bindings.get(&instance).cloned()
            else {
                return Err(self.error(format!("unknown resource instance `{instance}`")));
            };
            if family != declaration.family && !self.child_slot_identities.contains(&identity) {
                return Err(self.error(format!(
                    "binder `{binder}` expects resource `{}`, but `{instance}` is `{family}`",
                    declaration.family
                )));
            }
            if !instances.insert(identity) {
                return Err(self.error(format!(
                    "resource instance `{instance}` cannot supply two binders of `{callee}`"
                )));
            }
            binders.push(CallBinderBinding {
                binder,
                binder_identity: declaration.identity,
                instance,
                identity,
            });
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RBrace)?;
        if callee == "pthread_mutex_init" && !bound.contains("invariant") {
            return Err(self.error("`pthread_mutex_init` call map requires `invariant: instance`"));
        }
        if let Some((missing, _)) = declared.iter().find(|(name, entry)| {
            entry.kind == CalleeResourceBinderKind::Supplied && !bound.contains(*name)
        }) {
            return Err(self.error(format!("call map omits `{callee}` binder `{missing}`")));
        }
        let produced_declarations = declared
            .iter()
            .filter(|(_, entry)| entry.kind == CalleeResourceBinderKind::Produced);
        let produced_declarations = produced_declarations.collect::<Vec<_>>();
        let mut result = None;
        let mut produced = Vec::new();
        match (output, produced_declarations.as_slice()) {
            (None, []) => {}
            (None, _) => {
                let names = produced_declarations
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(self.error(format!(
                    "`{callee}` produces named resource instance(s) `{names}`; bind them with `let {{ ... }} = step(...)`"
                )));
            }
            // The legacy single-name form binds the only produced instance,
            // or names the call's scalar result when there is no produced
            // instance. The frontier's call statement decides whether the
            // latter actually has a result.
            (Some(CallOutputPattern::Single(name)), []) => {
                if self.current_contract_bindings.contains(&name)
                    || self.current_integer_params.contains(&name)
                    || self.current_integer_lets.contains(&name)
                    || self.current_resource_bindings.contains_key(&name)
                {
                    return Err(self.error(format!(
                        "call result name `{name}` conflicts with a C, pure, or resource binding"
                    )));
                }
                result = Some(name);
            }
            (Some(CallOutputPattern::Single(name)), [(produced_name, declaration)]) => {
                produced.push(self.bind_produced_call_instance(
                    &name,
                    produced_name,
                    declaration,
                    &arguments,
                )?);
            }
            (Some(CallOutputPattern::Single(_)), _) => {
                let names = produced_declarations
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(self.error(format!(
                    "`{callee}` produces multiple named resource instances ({names}); use `let {{ binder: name, ... }} = step(...)`"
                )));
            }
            (Some(CallOutputPattern::Named(bindings)), _) => {
                if produced_declarations.is_empty() {
                    return Err(self.error(format!(
                        "`{callee}` produces no named resource instances; use `let name = step(...)` only for a scalar result"
                    )));
                }
                let mut bound = BTreeSet::new();
                let mut names = BTreeSet::new();
                for (binder, name) in bindings {
                    if !bound.insert(binder.clone()) {
                        return Err(self.error(format!(
                            "duplicate produced binder `{binder}` in the call output pattern"
                        )));
                    }
                    if !names.insert(name.clone()) {
                        return Err(self.error(format!(
                            "call output pattern introduces resource name `{name}` twice"
                        )));
                    }
                    let Some((_, declaration)) = produced_declarations
                        .iter()
                        .find(|(declared, _)| *declared == &binder)
                    else {
                        return Err(self.error(format!(
                            "`{callee}` does not produce named resource `{binder}`"
                        )));
                    };
                    produced.push(self.bind_produced_call_instance(
                        &name,
                        &binder,
                        declaration,
                        &arguments,
                    )?);
                }
                if bound.len() != produced_declarations.len() {
                    let missing = produced_declarations
                        .iter()
                        .filter(|(name, _)| !bound.contains(*name))
                        .map(|(name, _)| name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(self.error(format!(
                        "call output pattern omits produced resource binder(s) `{missing}`"
                    )));
                }
            }
        }
        Ok(CallBinderTransport {
            callee,
            arguments,
            binders,
            produced,
            result,
        })
    }

    fn bind_produced_call_instance(
        &mut self,
        name: &str,
        produced: &str,
        declaration: &CalleeResourceBinder,
        arguments: &[ContractExpression],
    ) -> Result<CallBinderBinding, ClickError> {
        if self.current_contract_bindings.contains(name)
            || self.current_integer_params.contains(name)
            || self.current_integer_lets.contains(name)
        {
            return Err(self.error("produced instance conflicts with a C or pure binding"));
        }
        let identity = match self.current_resource_bindings.get(name) {
            Some((identity, family)) => {
                if *family != declaration.family && !self.child_slot_identities.contains(identity) {
                    return Err(self.error("produced instance changes the named resource family"));
                }
                *identity
            }
            None => {
                let identity = Variable(self.next_resource_identity);
                self.next_resource_identity += 1;
                identity
            }
        };
        self.current_resource_bindings
            .insert(name.to_string(), (identity, declaration.family.clone()));
        let substitutions = declaration
            .parameter_names
            .iter()
            .zip(arguments.iter())
            .map(|(parameter, argument)| (parameter.clone(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let target = substitute_resource_clause_bindings(&declaration.resource, &substitutions)
            .map_err(|message| self.error(message))?;
        let ResourceClause::Named { binding, resource } = target else {
            return Err(self.error(format!(
                "produced resource binder `{produced}` has no named resource target"
            )));
        };
        self.current_resource_targets.insert(
            name.to_string(),
            ResourceClause::Named {
                binding: ResourceInstanceBinding {
                    name: name.to_string(),
                    identity,
                    children: binding.children,
                    schema: binding.schema,
                    fields: binding.fields,
                    fold_fields: None,
                    child_bindings: binding.child_bindings,
                },
                resource,
            },
        );
        Ok(CallBinderBinding {
            binder: produced.to_string(),
            binder_identity: declaration.identity,
            instance: name.to_string(),
            identity,
        })
    }

    /// Records one instance binder of the C function block being parsed, so a
    /// later `step(callee(...), { ... })` can bind it by name. Contract blocks
    /// name an interface rather than a callable function and are skipped.
    fn record_callee_resource_binder(
        &mut self,
        function: &str,
        resource: &ResourceClause,
        parameter_names: &[String],
        kind: CalleeResourceBinderKind,
    ) {
        if self.in_contract_definition {
            return;
        }
        let ResourceClause::Named { binding, resource } = resource else {
            return;
        };
        let ResourceClause::Declared { name: family, .. } = resource.as_ref() else {
            return;
        };
        crate::instrumentation::record_deterministic_work(1);
        self.callee_resource_binders
            .entry(function.to_string())
            .or_default()
            .insert(
                binding.name.clone(),
                CalleeResourceBinder {
                    identity: binding.identity,
                    family: family.clone(),
                    resource: ResourceClause::Named {
                        binding: binding.clone(),
                        resource: resource.clone(),
                    },
                    parameter_names: parameter_names.to_vec(),
                    kind,
                },
            );
    }

    fn parse_owned_resource_binding(&mut self) -> Result<ResourceClause, ClickError> {
        self.parse_owned_resource_binding_allowing_rebinding(false)
    }

    /// A loop header binder, which may reuse an enclosing binder's name. The
    /// loop rebinds that name to the instance it selects at entry, so a reused
    /// name keeps the enclosing instance identity and must name the same
    /// resource family.
    fn parse_loop_resource_binding(&mut self) -> Result<ResourceClause, ClickError> {
        self.parse_owned_resource_binding_allowing_rebinding(true)
    }

    fn parse_owned_resource_binding_allowing_rebinding(
        &mut self,
        rebinding: bool,
    ) -> Result<ResourceClause, ClickError> {
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
        let rebound = rebinding
            .then(|| self.current_resource_bindings.get(&name).cloned())
            .flatten();
        if (rebound.is_none() && self.current_resource_bindings.contains_key(&name))
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
        let identity = match rebound {
            Some((identity, family)) => {
                if &family != resource_name && !self.child_slot_identities.contains(&identity) {
                    return Err(self.error(format!(
                        "loop binder `{name}` rebinds an instance of resource `{family}`, not `{resource_name}`"
                    )));
                }
                identity
            }
            None => {
                let identity = Variable(self.next_resource_identity);
                self.next_resource_identity += 1;
                identity
            }
        };
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
                Ok(vec![StructuralItem { claim: proposition }])
            }
            Some(Token::Ident(kind))
                if kind == "immutable" || kind == "mutable" || kind == "step" =>
            {
                Err(self.error(
                    "loop effect clauses were removed; a loop frames by ownership by default, or declares `owns`/`views` of its own",
                ))
            }
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected `invariant`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected `invariant`, got {token:?}"
            ))),
            None => Err(self.error("expected `invariant`, got end of input")),
        }
    }

    fn parse_ensure_clause(&mut self) -> Result<EnsureClause, ClickError> {
        self.expect_ident_spelling("ensures")?;
        self.parse_ensure_clause_after_keyword()
    }

    fn parse_ensure_clause_after_keyword(&mut self) -> Result<EnsureClause, ClickError> {
        Ok(self.parse_ensure_clause_body(None)?.0)
    }

    /// Parse one `ensures` clause, returning the conclusion's `as` instance
    /// map alongside it when the clause belongs to an `executes` theorem.
    fn parse_ensure_clause_with_execution_scope(
        &mut self,
        execution_names: Option<&BTreeSet<String>>,
    ) -> Result<(EnsureClause, Vec<(String, String)>), ClickError> {
        self.expect_ident_spelling("ensures")?;
        self.parse_ensure_clause_body(execution_names)
    }

    fn parse_ensure_clause_body(
        &mut self,
        execution_names: Option<&BTreeSet<String>>,
    ) -> Result<(EnsureClause, Vec<(String, String)>), ClickError> {
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
        let introduced = match execution_names {
            Some(names) => self.introduce_execution_target_instances(&ensure, names)?,
            None => Vec::new(),
        };
        let proof = self.parse_proof_clause_or_default()?;
        if let Some(previous) = previous {
            self.current_resource_bindings = previous;
        }

        Ok((
            EnsureClause {
                name,
                ensure,
                proof,
                borrowed: false,
                condition: None,
            },
            introduced,
        ))
    }

    /// Bind the target contract's resource proof parameters for an `executes`
    /// proof block. Every instance name is introduced by the conclusion's
    /// `as { parameter: name }` map; the contract's own parameter spelling is
    /// never in scope, so the block has exactly one way to name an instance.
    fn introduce_execution_target_instances(
        &mut self,
        ensure: &Ensure,
        names: &BTreeSet<String>,
    ) -> Result<Vec<(String, String)>, ClickError> {
        let target = match ensure {
            Ensure::Proposition(ClickProposition::PredicateCall { name, .. }) => Some(name.clone()),
            _ => None,
        };
        let declared = target
            .as_deref()
            .and_then(|target| self.contract_proof_bindings.get(target))
            .cloned()
            .unwrap_or_default();
        let mut introduced: Vec<(String, String)> = Vec::new();
        let wrote_map = self.peek_ident() == Some("as");
        if wrote_map {
            self.position += 1;
            self.expect(Token::LBrace)?;
            while self.peek() != Some(&Token::RBrace) {
                crate::instrumentation::record_deterministic_work(1);
                let slot = self.expect_ident("target proof parameter")?;
                self.expect(Token::Colon)?;
                let name = self.expect_ident("introduced instance name")?;
                introduced.push((slot, name));
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::RBrace)?;
        }
        let Some(target) = target else {
            if wrote_map {
                return Err(
                    self.error("an `as` instance map requires a target contract as the conclusion")
                );
            }
            return Ok(Vec::new());
        };
        if declared.is_empty() && !introduced.is_empty() {
            return Err(self.error(format!(
                "contract `{target}` declares no proof parameters, so its conclusion takes no `as` map"
            )));
        }
        let mut bound: BTreeMap<&str, &str> = BTreeMap::new();
        let mut used: BTreeSet<&str> = BTreeSet::new();
        for (slot, name) in &introduced {
            crate::instrumentation::record_deterministic_work(1);
            if !declared
                .iter()
                .any(|(parameter, _, _)| parameter == slot.as_str())
            {
                return Err(self.error(format!(
                    "contract `{target}` does not declare a proof parameter `{slot}`"
                )));
            }
            if bound.insert(slot.as_str(), name.as_str()).is_some() {
                return Err(self.error(format!(
                    "duplicate `as` entry for proof parameter `{slot}` of contract `{target}`"
                )));
            }
            if !used.insert(name.as_str()) {
                return Err(self.error(format!("`as` introduces the name `{name}` twice")));
            }
            if name == "result" || names.contains(name.as_str()) {
                return Err(self.error(format!(
                    "`as` name `{name}` conflicts with an execution proof binding"
                )));
            }
        }
        let mut bindings = Vec::new();
        let mut ordered = Vec::new();
        for (parameter, identity, resource) in &declared {
            crate::instrumentation::record_deterministic_work(1);
            let Some(name) = bound.get(parameter.as_str()) else {
                return Err(self.error(format!(
                    "contract `{target}` proof parameter `{parameter}` needs an introduced name; \
                     write `ensures {target}(...) as {{ {parameter}: <name> }}`"
                )));
            };
            bindings.push(((*name).to_string(), (*identity, resource.clone())));
            ordered.push((parameter.clone(), (*name).to_string()));
        }
        self.current_resource_bindings.extend(bindings);
        Ok(ordered)
    }

    fn parse_ensure_condition(&mut self) -> Result<Ensure, ClickError> {
        Ok(Ensure::Proposition(self.parse_proposition()?))
    }

    fn parse_proposition(&mut self) -> Result<ClickProposition, ClickError> {
        if self.proposition_nesting > STRUCTURAL_NESTING_LIMIT {
            return Err(self.error(format!(
                "structural proposition nesting exceeds Click's supported depth of {STRUCTURAL_NESTING_LIMIT}"
            )));
        }
        self.proposition_nesting += 1;
        let result = self.parse_proposition_implies();
        self.proposition_nesting -= 1;
        result
    }

    fn parse_proposition_implies(&mut self) -> Result<ClickProposition, ClickError> {
        // `implies` is right associative, but parsing it recursively makes a
        // short source-level chain consume one Rust frame per link. Collect
        // the operands iteratively and fold them from the right instead.
        let mut operands = vec![self.parse_proposition_or()?];
        while self.peek_ident() == Some("implies") {
            if operands.len() >= EXPRESSION_CHAIN_LIMIT {
                return Err(self.error(format!(
                    "proposition operator nesting exceeds Click's supported depth of {EXPRESSION_CHAIN_LIMIT}"
                )));
            }
            self.position += 1;
            operands.push(self.parse_proposition_or()?);
        }
        let mut propositions = operands.into_iter().rev();
        let mut proposition = propositions
            .next()
            .expect("an implication chain always has one operand");
        for left in propositions {
            proposition = ClickProposition::Implies(Box::new(left), Box::new(proposition));
        }
        Ok(proposition)
    }

    fn parse_proposition_or(&mut self) -> Result<ClickProposition, ClickError> {
        let mut proposition = self.parse_proposition_and()?;
        let mut operands = 1;
        while self.peek_ident() == Some("or") {
            if operands >= EXPRESSION_CHAIN_LIMIT {
                return Err(self.error(format!(
                    "proposition operator nesting exceeds Click's supported depth of {EXPRESSION_CHAIN_LIMIT}"
                )));
            }
            self.position += 1;
            let right = self.parse_proposition_and()?;
            proposition = ClickProposition::Or(Box::new(proposition), Box::new(right));
            operands += 1;
        }
        Ok(proposition)
    }

    fn parse_proposition_and(&mut self) -> Result<ClickProposition, ClickError> {
        let mut proposition = self.parse_proposition_not()?;
        let mut operands = 1;
        while self.peek_ident() == Some("and") {
            if operands >= EXPRESSION_CHAIN_LIMIT {
                return Err(self.error(format!(
                    "proposition operator nesting exceeds Click's supported depth of {EXPRESSION_CHAIN_LIMIT}"
                )));
            }
            self.position += 1;
            let right = self.parse_proposition_not()?;
            proposition = ClickProposition::And(Box::new(proposition), Box::new(right));
            operands += 1;
        }
        Ok(proposition)
    }

    fn parse_proposition_not(&mut self) -> Result<ClickProposition, ClickError> {
        // Unlike `implies`, unary negation has no intervening delimiter that
        // the tokenizer preflight can use as a structural bound. Consume the
        // prefix iteratively and rebuild it after parsing the atom.
        let mut negations = 0;
        while self.peek_ident() == Some("not") {
            if negations >= UNARY_NESTING_LIMIT {
                return Err(self.error(format!(
                    "proposition unary nesting exceeds Click's supported depth of {UNARY_NESTING_LIMIT}"
                )));
            }
            self.position += 1;
            negations += 1;
        }
        let mut proposition = self.parse_proposition_atom()?;
        for _ in 0..negations {
            proposition = ClickProposition::Not(Box::new(proposition));
        }
        Ok(proposition)
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
                click_type: ClickType::C(c_type),
                name: binding.name,
                written_name: None,
                body: Box::new(ClickProposition::And(Box::new(condition), Box::new(body))),
            });
        }

        if matches!(self.peek_ident(), Some("forall" | "exists")) {
            return self.parse_quantifier_chain();
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
            if proposition_at_snapshot.is_ok()
                && !matches!(
                    self.peek(),
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
                    )
                )
            {
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

        if self.peek_ident() == Some("viewable") && self.peek_next() == Some(&Token::LParen) {
            let segment = self.parse_loadable_segment()?;
            return Ok(ClickProposition::Loadable { segment });
        }

        if self.peek_ident() == Some("loadable") && self.peek_next() == Some(&Token::LParen) {
            return Err(self.error(RETIRED_LOADABLE_SPELLING));
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
                Some("address" | "byte_offset" | "sizeof")
            )
            && typed_load_type_from_name(self.peek_ident()).is_none()
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

    fn parse_quantifier_chain(&mut self) -> Result<ClickProposition, ClickError> {
        #[derive(Clone, Copy)]
        enum Operator {
            And,
            Or,
            Implies,
            Scope,
        }
        struct Scope {
            forall: bool,
            click_type: ClickType,
            name: String,
            negations: usize,
            previous_integer_context: bool,
            integer_was_bound: bool,
            integer_let_was_bound: bool,
            c_was_bound: bool,
        }

        let mut scopes = Vec::new();
        let mut scope_groups = Vec::new();
        let mut operands = Vec::new();
        let mut operators = Vec::new();
        let mut expect_operand = true;
        let reduce = |operator: Operator, operands: &mut Vec<ClickProposition>| {
            let right = operands.pop().expect("quantifier expression right operand");
            let left = operands.pop().expect("quantifier expression left operand");
            operands.push(match operator {
                Operator::And => ClickProposition::And(Box::new(left), Box::new(right)),
                Operator::Or => ClickProposition::Or(Box::new(left), Box::new(right)),
                Operator::Implies => ClickProposition::Implies(Box::new(left), Box::new(right)),
                Operator::Scope => unreachable!("scope marker is not a binary operator"),
            });
        };
        let precedence = |operator| match operator {
            Operator::And => 2,
            Operator::Or => 1,
            Operator::Implies => 0,
            Operator::Scope => usize::MAX,
        };

        loop {
            if expect_operand {
                let mut negations = 0;
                while self.peek_ident() == Some("not") {
                    if negations >= UNARY_NESTING_LIMIT {
                        return Err(self.error(format!(
                            "proposition unary nesting exceeds Click's supported depth of {UNARY_NESTING_LIMIT}"
                        )));
                    }
                    self.position += 1;
                    negations += 1;
                }
                if matches!(self.peek_ident(), Some("forall" | "exists")) {
                    let forall = self.peek_ident() == Some("forall");
                    if self.proposition_nesting + scopes.len() >= STRUCTURAL_NESTING_LIMIT {
                        return Err(self.error(format!(
                            "structural proposition nesting exceeds Click's supported depth of {STRUCTURAL_NESTING_LIMIT}"
                        )));
                    }
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let mut group_len = 0;
                    loop {
                        let name = self.expect_ident(if forall {
                            "forall variable name"
                        } else {
                            "exists variable name"
                        })?;
                        if is_c_type_keyword(&name) {
                            return Err(self.error(
                                "Click-native binders use `name: type`, for example `exists (k: int32)`",
                            ));
                        }
                        self.expect(Token::Colon)?;
                        let (click_type, parsed_type) = self.parse_click_type()?;
                        if let Some(parsed_type) = &parsed_type
                            && parsed_type.struct_name.is_some()
                            && !parsed_type.struct_pointer
                        {
                            return Err(self.error("only pointer-to-struct types are supported"));
                        }
                        let previous_integer_context = self.integer_literal_context;
                        let integer_was_bound = self.current_integer_params.contains(&name);
                        let integer_let_was_bound = self.current_integer_lets.contains(&name);
                        let c_was_bound = self.current_contract_bindings.contains(&name);
                        match &click_type {
                            ClickType::Integer => {
                                self.current_contract_bindings.remove(&name);
                                self.current_integer_params.insert(name.clone());
                                self.integer_literal_context = true;
                            }
                            ClickType::C(_) => {
                                self.current_integer_params.remove(&name);
                                self.current_integer_lets.remove(&name);
                                self.current_contract_bindings.remove(&name);
                                self.integer_literal_context = false;
                            }
                            ClickType::Algebraic(_) => {
                                self.current_integer_params.remove(&name);
                                self.current_integer_lets.remove(&name);
                                self.current_contract_bindings.insert(name.clone());
                                self.integer_literal_context = false;
                            }
                            ClickType::Parameter(_) => {
                                return Err(self.error(
                                    "quantifier type must be a concrete C, Integer, or algebraic type",
                                ));
                            }
                        }
                        scopes.push(Scope {
                            forall,
                            click_type,
                            name,
                            negations: if group_len == 0 { negations } else { 0 },
                            previous_integer_context,
                            integer_was_bound,
                            integer_let_was_bound,
                            c_was_bound,
                        });
                        operators.push(Operator::Scope);
                        group_len += 1;
                        if self.peek() != Some(&Token::Comma) {
                            break;
                        }
                        self.position += 1;
                    }
                    self.expect(Token::RParen)?;
                    self.expect(Token::LBrace)?;
                    scope_groups.push(group_len);
                    continue;
                }
                let mut operand = self.parse_proposition_atom()?;
                for _ in 0..negations {
                    operand = ClickProposition::Not(Box::new(operand));
                }
                operands.push(operand);
                expect_operand = false;
                continue;
            }

            let next_operator = match self.peek_ident() {
                Some("and") => Some(Operator::And),
                Some("or") => Some(Operator::Or),
                Some("implies") => Some(Operator::Implies),
                _ => None,
            };
            if let Some(operator) = next_operator {
                self.position += 1;
                while let Some(&top) = operators.last() {
                    if matches!(top, Operator::Scope)
                        || !(precedence(top) > precedence(operator)
                            || (precedence(top) == precedence(operator)
                                && !matches!(operator, Operator::Implies)))
                    {
                        break;
                    }
                    let top = operators.pop().expect("operator stack has a top");
                    reduce(top, &mut operands);
                }
                operators.push(operator);
                expect_operand = true;
                continue;
            }

            if self.peek() == Some(&Token::RBrace) {
                self.position += 1;
                let group_len = scope_groups
                    .pop()
                    .ok_or_else(|| self.error("quantifier body closed without a scope"))?;
                for _ in 0..group_len {
                    loop {
                        let operator = operators
                            .pop()
                            .ok_or_else(|| self.error("quantifier body closed without a scope"))?;
                        if matches!(operator, Operator::Scope) {
                            break;
                        }
                        reduce(operator, &mut operands);
                    }
                    let scope = scopes.pop().expect("quantifier scope marker has a scope");
                    self.integer_literal_context = scope.previous_integer_context;
                    if scope.integer_was_bound {
                        self.current_integer_params.insert(scope.name.clone());
                    } else {
                        self.current_integer_params.remove(&scope.name);
                    }
                    if scope.integer_let_was_bound {
                        self.current_integer_lets.insert(scope.name.clone());
                    } else {
                        self.current_integer_lets.remove(&scope.name);
                    }
                    if scope.c_was_bound {
                        self.current_contract_bindings.insert(scope.name.clone());
                    } else {
                        self.current_contract_bindings.remove(&scope.name);
                    }
                    let body = operands.pop().expect("quantifier body operand");
                    let mut quantifier = if scope.forall {
                        ClickProposition::ForAll {
                            click_type: scope.click_type,
                            name: scope.name,
                            written_name: None,
                            body: Box::new(body),
                        }
                    } else {
                        ClickProposition::Exists {
                            click_type: scope.click_type,
                            name: scope.name,
                            written_name: None,
                            body: Box::new(body),
                        }
                    };
                    for _ in 0..scope.negations {
                        quantifier = ClickProposition::Not(Box::new(quantifier));
                    }
                    operands.push(quantifier);
                }
                if scopes.is_empty() {
                    return Ok(operands.pop().expect("quantifier chain root"));
                }
                expect_operand = false;
                continue;
            }

            return Err(self.error("expected a proposition operator or `}`"));
        }
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
                written_item: None,
                body: Box::new(body),
            }),
            "any" => Ok(ClickProposition::RangeAny {
                start,
                end,
                item,
                written_item: None,
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
        let let_checkpoint = self.proof_let_restores.len();
        let previous_proof_let_names = std::mem::take(&mut self.current_proof_let_names);
        let result = self.parse_by_clause_body();
        self.restore_proof_let_bindings(let_checkpoint);
        self.current_proof_let_names = previous_proof_let_names;
        result
    }

    fn restore_proof_let_bindings(&mut self, checkpoint: usize) {
        while self.proof_let_restores.len() > checkpoint {
            let restore = self
                .proof_let_restores
                .pop()
                .expect("restore above checkpoint");
            if restore.was_integer_let {
                self.current_integer_lets.insert(restore.name.clone());
            } else {
                self.current_integer_lets.remove(&restore.name);
            }
            if restore.was_contract_binding {
                self.current_contract_bindings.insert(restore.name);
            } else {
                self.current_contract_bindings.remove(&restore.name);
            }
        }
    }

    fn parse_by_clause_body(&mut self) -> Result<SourceProof, ClickError> {
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
        self.expect(Token::LBrace)?;
        let mut bindings = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            let slot = self.expect_ident("child slot")?;
            self.expect(Token::Colon)?;
            let name = self.expect_ident("child resource name")?;
            bindings.push((slot, name));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RBrace)?;
        self.bind_resource_child_names(parent, bindings, introduce)
    }

    fn bind_resource_child_names(
        &mut self,
        parent: &ResourceClause,
        bindings: Vec<(String, String)>,
        introduce: bool,
    ) -> Result<Vec<(String, String, Variable)>, ClickError> {
        let ResourceClause::Declared { name: family, .. } = parent else {
            return Err(self.error("child bindings require a declared resource family"));
        };
        let mut result = Vec::new();
        let mut slots = BTreeSet::new();
        let mut names = BTreeSet::new();
        for (slot, name) in bindings {
            if !slots.insert(slot.clone()) || !names.insert(name.clone()) {
                return Err(self.error("duplicate child slot or resource name"));
            }
            if self.current_contract_bindings.contains(&name) {
                return Err(self.error("child resource name conflicts with a C or pure binding"));
            }
            let identity = if let Some((identity, _)) = self.current_resource_bindings.get(&name) {
                // A child slot's resource comes from the parent's matched
                // arm, which the parser cannot resolve; declaration
                // expansion checks the supplied instance against it.
                *identity
            } else if introduce {
                let identity = Variable(self.next_resource_identity);
                self.next_resource_identity += 1;
                identity
            } else {
                return Err(self.error(format!("unknown child resource `{name}`")));
            };
            if introduce {
                self.child_slot_identities.insert(identity);
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
        }
        Ok(result)
    }

    fn parse_let_output_pattern(&mut self) -> Result<CallOutputPattern, ClickError> {
        if self.peek() != Some(&Token::LBrace) {
            return Ok(CallOutputPattern::Single(
                self.expect_ident("let binding name")?,
            ));
        }
        self.position += 1;
        let mut bindings = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            let binder = self.expect_ident("output binder")?;
            self.expect(Token::Colon)?;
            let name = self.expect_ident("output binding name")?;
            bindings.push((binder, name));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RBrace)?;
        Ok(CallOutputPattern::Named(bindings))
    }

    fn parse_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        if self.proof_nesting > STRUCTURAL_NESTING_LIMIT {
            return Err(self.error(format!(
                "structural proof nesting exceeds Click's supported depth of {STRUCTURAL_NESTING_LIMIT}"
            )));
        }
        self.proof_nesting += 1;
        let result = self.parse_proof_tactic_inner();
        self.proof_nesting -= 1;
        result
    }

    fn parse_proof_tactic_inner(&mut self) -> Result<ProofTactic, ClickError> {
        let name = self.expect_ident("tactic")?;
        match name.as_str() {
            "let" => {
                if self.peek() == Some(&Token::LParen) {
                    return self.parse_let_satisfy();
                }
                let output = self.parse_let_output_pattern()?;
                self.expect(Token::Equal)?;
                if self.peek_ident() == Some("step") {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    if !self.call_binder_transport_follows() {
                        return Err(self.error(
                            "a call output binding requires a call and binder map: `let name = step(callee(...), { binder: instance })`",
                        ));
                    }
                    let transport = self.parse_call_binder_transport(Some(output))?;
                    self.expect(Token::RParen)?;
                    self.expect(Token::Semicolon)?;
                    return Ok(ProofTactic::StepCall(transport));
                }
                if self.peek_ident() == Some("unfold") {
                    let CallOutputPattern::Named(bindings) = output else {
                        return Err(self.error(
                            "resource unfold outputs require a labeled pattern: `let { slot: name } = unfold(resource)`",
                        ));
                    };
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let ResourceClause::Named {
                        mut binding,
                        resource,
                    } = self.parse_owned_resource_target()?
                    else {
                        return Err(self.error("resource unfold outputs require a named resource"));
                    };
                    self.expect(Token::RParen)?;
                    binding.child_bindings = Some(
                        self.bind_resource_child_names(&resource, bindings, true)?
                            .into(),
                    );
                    self.expect(Token::Semicolon)?;
                    return Ok(ProofTactic::UnfoldResource(ResourceClause::Named {
                        binding,
                        resource,
                    }));
                }
                let CallOutputPattern::Single(name) = output else {
                    return Err(self.error(
                        "resource construction requires one result name: `let name = fold(resource, { ... })`",
                    ));
                };
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
                if self.current_contract_bindings.contains(&name)
                    || self.current_integer_params.contains(&name)
                    || self.current_integer_lets.contains(&name)
                {
                    return Err(self.error("fold result conflicts with a C or pure binding"));
                }
                let identity = if let Some((identity, previous)) =
                    self.current_resource_bindings.get(&name)
                {
                    if previous != resource_name && !self.child_slot_identities.contains(identity) {
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

    fn parse_let_satisfy(&mut self) -> Result<ProofTactic, ClickError> {
        self.expect(Token::LParen)?;
        let mut bindings = Vec::new();
        loop {
            let name = self.expect_ident("existential binding name")?;
            if is_c_type_keyword(&name)
                || self.current_proof_let_names.contains(&name)
                || bindings.iter().any(|(bound, _)| bound == &name)
            {
                return Err(self.error(format!("`{name}` is already in scope")));
            }
            self.expect(Token::Colon)?;
            let (click_type, parsed_type) = self.parse_click_type()?;
            if parsed_type
                .as_ref()
                .is_some_and(|parsed| parsed.struct_name.is_some() && !parsed.struct_pointer)
            {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            if matches!(click_type, ClickType::Parameter(_)) {
                return Err(self.error(
                    "existential binding type must be a concrete C, Integer, or algebraic type",
                ));
            }
            bindings.push((name, click_type));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        self.expect_ident_spelling("satisfy")?;
        self.expect(Token::LBrace)?;
        let previous_integer_context = self.integer_literal_context;
        for (name, click_type) in &bindings {
            self.proof_let_restores.push(ProofLetParserRestore {
                name: name.clone(),
                was_integer_let: self.current_integer_lets.contains(name),
                was_contract_binding: self.current_contract_bindings.contains(name),
            });
            match click_type {
                ClickType::Integer => {
                    self.current_contract_bindings.remove(name);
                    self.current_integer_lets.insert(name.clone());
                    self.integer_literal_context = true;
                }
                ClickType::C(_) | ClickType::Algebraic(_) => {
                    self.current_integer_lets.remove(name);
                    self.current_contract_bindings.insert(name.clone());
                    self.integer_literal_context = false;
                }
                ClickType::Parameter(_) => unreachable!("rejected above"),
            }
        }
        let body = self.parse_proposition()?;
        self.expect(Token::RBrace)?;
        self.expect(Token::Semicolon)?;
        self.integer_literal_context = previous_integer_context;
        self.current_proof_let_names
            .extend(bindings.iter().map(|(name, _)| name.clone()));
        // The snapshot is independent of the newly bound variables, so
        // `exists x. at(S, P(x))` is stated at the source as
        // `at(S, exists x. P(x))`. This preserves the exact fact identity of
        // an existential recorded at a past program point.
        let (snapshot, body) = match body {
            ClickProposition::At {
                selector,
                proposition,
            } => (Some(selector), *proposition),
            body => (None, body),
        };
        let proposition = bindings
            .iter()
            .rev()
            .fold(body, |body, (name, click_type)| ClickProposition::Exists {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: None,
                body: Box::new(body),
            });
        let proposition = match snapshot {
            Some(selector) => ClickProposition::At {
                selector,
                proposition: Box::new(proposition),
            },
            None => proposition,
        };
        Ok(ProofTactic::LetSatisfy(ProofLetSatisfy {
            bindings,
            proposition,
        }))
    }

    #[inline(never)]
    fn parse_both_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let mut nested_both = 0;
        self.expect(Token::LBrace)?;
        let mut left_tactics = if self.peek_ident() == Some("both") {
            self.position += 1;
            nested_both += 1;
            None
        } else {
            Some(self.parse_tactics_until_rbrace()?)
        };

        while left_tactics.is_none() {
            if self.proof_nesting + nested_both >= STRUCTURAL_NESTING_LIMIT {
                return Err(self.error(format!(
                    "structural proof nesting exceeds Click's supported depth of {STRUCTURAL_NESTING_LIMIT}"
                )));
            }
            self.expect(Token::LBrace)?;
            if self.peek_ident() == Some("both") {
                self.position += 1;
                nested_both += 1;
            } else {
                left_tactics = Some(self.parse_tactics_until_rbrace()?);
            }
        }
        self.expect(Token::RBrace)?;

        let mut current = None;
        for level in 0..=nested_both {
            self.expect_ident_spelling("and")?;
            self.expect(Token::LBrace)?;
            let right_tactics = self.parse_tactics_until_rbrace()?;
            self.expect(Token::RBrace)?;
            let left = if let Some(current) = current.take() {
                vec![current]
            } else {
                left_tactics
                    .take()
                    .expect("the deepest both tactic has a left block")
            };
            current = Some(ProofTactic::Both(ProofBoth {
                left_tactics: left,
                right_tactics,
            }));
            if level < nested_both {
                self.expect(Token::RBrace)?;
            }
        }
        if self.peek() == Some(&Token::Semicolon) {
            self.position += 1;
        }
        Ok(current.expect("the both tactic chain has a root"))
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
                // A proof arm's struct-pointer binding is a memory base in the
                // arm body exactly as a resource arm's is (package A5), so the
                // arm's bindings get their declared types here too. Without
                // this, `id->word` in the body resolves against no layout and
                // lowers as a width-unknown load, which reads a different cell
                // from the `p->word` the same arm's `fact p == id` identifies
                // it with.
                let saved_struct_params = self.current_struct_params.clone();
                let saved_arm_binding_types = std::mem::take(&mut self.current_arm_binding_types);
                self.bind_arm_binding_types(&type_name, &variant, &bindings);
                let tactics = self.parse_possibly_empty_tactic_block();
                self.current_struct_params = saved_struct_params;
                self.current_arm_binding_types = saved_arm_binding_types;
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
        if name == "outcomes" {
            self.expect(Token::LBrace)?;
            self.expect_ident_spelling("returned")?;
            let returned_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect_ident_spelling("threw")?;
            let threw_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect(Token::RBrace)?;
            if self.peek() == Some(&Token::Semicolon) {
                self.position += 1;
            }
            return Ok(ProofTactic::CallOutcomes(ProofCallOutcomes {
                returned_tactics,
                threw_tactics,
            }));
        }
        if name == "loop" {
            let label = if self.peek_ident() == Some("as") {
                self.position += 1;
                Some(self.expect_ident("loop label")?)
            } else {
                None
            };
            // A loop has no signature, so its `diverges` marker sits on the
            // head, where the signature marker sits for a function.
            let diverges = if self.peek_ident() == Some("diverges") {
                self.position += 1;
                true
            } else {
                false
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
                    let resource = self.parse_loop_resource_binding()?;
                    self.expect(Token::Semicolon)?;
                    if let ResourceClause::Named { binding, .. } = &resource
                        && resources.iter().any(|existing| {
                            matches!(existing, ResourceClause::Named { binding: other, .. }
                                if other.name == binding.name)
                        })
                    {
                        return Err(self
                            .error(format!("duplicate loop resource binder `{}`", binding.name)));
                    }
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
                    if diverges {
                        return Err(self.error(format!(
                            "{} is declared `diverges` and cannot also carry a `decreases` clause",
                            loop_clause_description(label.as_deref())
                        )));
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
            if items.is_empty() && decreases.is_none() && resources.is_empty() && !diverges {
                return Err(self
                    .error("`loop` block must contain at least one item or a `decreases` clause"));
            }
            return Ok(ProofTactic::Loop(StructuralClause {
                // The actual loop identity is bound from the execution
                // frontier during check.  This sentinel is never lowered.
                region: CodeRegion::Loop(usize::MAX),
                label,
                decreases,
                diverges,
                items,
                resources,
                initialize_proof,
                preserve_proof,
                scope: BTreeMap::new(),
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
                } else if self.call_binder_transport_follows() {
                    ProofTactic::StepCall(self.parse_call_binder_transport(None)?)
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
                return Err(self.error(
                    "`frame` was removed; ownership frames untouched memory with no tactic",
                ));
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
                } else if let Some(name) = self.peek_ident()
                    && self.current_resource_bindings.contains_key(name)
                {
                    return Err(self.error(format!(
                        "resource instance `{name}` is not available as an unfold target"
                    )));
                } else {
                    let predicate = self.expect_ident("predicate name")?;
                    ProofTactic::UnfoldPredicate(predicate)
                };
                self.expect(Token::RParen)?;
                if self.peek_ident() == Some("using") {
                    let ProofTactic::UnfoldFunction(application) = tactic else {
                        return Err(self
                            .error("`using` requires a pure-function unfold, `unfold(f(args))`"));
                    };
                    let premises = self.parse_exact_premises()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        self.position += 1;
                    }
                    return Ok(ProofTactic::UnfoldFunctionUsing {
                        application,
                        premises,
                    });
                }
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
            "take" | "give" => {
                self.expect(Token::LParen)?;
                let segment = self.parse_current_contract_segment()?;
                self.expect(Token::RParen)?;
                ProofTactic::Iterated(if name == "take" {
                    IteratedTactic::Take(segment)
                } else {
                    IteratedTactic::Give(segment)
                })
            }
            "gather" | "scatter" => {
                self.expect(Token::LParen)?;
                let resource =
                    self.parse_declared_resource_call_with_access(ResourceAccessMode::Own)?;
                self.expect(Token::RParen)?;
                ProofTactic::Iterated(if name == "gather" {
                    IteratedTactic::Gather(resource)
                } else {
                    IteratedTactic::Scatter(resource)
                })
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
                return Err(self.error(
                    "`choose` was removed; write `let (name: Type) satisfy { proposition };` after proving that existential",
                ));
            }
            "assumption" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Assumption
            }
            "sorry" => {
                self.expect_empty_tactic_args(&name)?;
                if !crate::surface::verification::sorry_is_allowed() {
                    return Err(self.error(
                        "`sorry` is a dev-only proof hole; it parses only under `click verify --allow-sorry` and never verifies in the gate",
                    ));
                }
                ProofTactic::Sorry
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
            "arithmetic_certificate" | "integer_certificate" => {
                return self.parse_arithmetic_certificate_tactic();
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
        let tactics = self.parse_tactics_until_rbrace()?;
        self.expect(Token::RBrace)?;
        Ok(tactics)
    }

    fn parse_tactics_until_rbrace(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        let let_checkpoint = self.proof_let_restores.len();
        let previous_proof_let_names = std::mem::take(&mut self.current_proof_let_names);
        let result = (|| {
            let mut tactics = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                tactics.push(self.parse_proof_tactic()?);
            }
            Ok(tactics)
        })();
        self.restore_proof_let_bindings(let_checkpoint);
        self.current_proof_let_names = previous_proof_let_names;
        result
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

    fn parse_arithmetic_certificate_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let previous = std::mem::replace(&mut self.integer_literal_context, true);
        let parsed = if self.peek_ident() == Some("signed_int32") {
            self.position += 1;
            self.parse_signed_int32_certificate_body()
        } else if self.peek_ident() == Some("special") {
            self.position += 1;
            self.parse_special_arithmetic_certificate_body()
        } else {
            self.parse_arithmetic_certificate_body()
        };
        self.integer_literal_context = previous;
        parsed
    }

    fn parse_special_arithmetic_certificate_body(&mut self) -> Result<ProofTactic, ClickError> {
        self.expect(Token::LBrace)?;
        let mut premises = Vec::<Option<ClickProposition>>::new();
        let mut nodes = Vec::new();
        let mut conclusion = None;
        while self.peek() != Some(&Token::RBrace) {
            let keyword = self.expect_ident("special arithmetic certificate node")?;
            match keyword.as_str() {
                "premise" => {
                    let index = self.expect_index("special premise index")?;
                    self.expect(Token::Colon)?;
                    let proposition_start = self.position;
                    let proposition = self.parse_proposition()?;
                    let proposition_end = self.position;
                    self.expect(Token::FatArrow)?;
                    let result_start = self.position;
                    let _result = self.parse_proposition()?;
                    let result_end = self.position;
                    self.expect(Token::Semicolon)?;
                    if !charged_token_equal(
                        &self.tokens[proposition_start..proposition_end],
                        &self.tokens[result_start..result_end],
                    ) {
                        return Err(self.error(format!(
                            "special arithmetic premise {index} must repeat the same proposition on both sides"
                        )));
                    }
                    if index > premises.len() {
                        return Err(self.error(format!(
                            "special arithmetic premise indices must be contiguous; expected {} but found {index}",
                            premises.len()
                        )));
                    }
                    if index == premises.len() {
                        premises.push(None);
                    }
                    if premises[index].replace(proposition).is_some() {
                        return Err(self.error(format!(
                            "special arithmetic premise {index} is declared more than once"
                        )));
                    }
                }
                "pointer_translation" | "pointer_translate" => {
                    self.expect_ident_spelling("relation")?;
                    let relation = self.expect_index("pointer relation node")?;
                    self.expect_ident_spelling("bounds")?;
                    let bounds = self.parse_certificate_index_list("pointer bound node")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::PointerTranslation {
                        relation,
                        bounds,
                        result,
                    });
                }
                "pointer_alignment" | "pointer_align" => {
                    self.expect_ident_spelling("premise")?;
                    let premise = if self.peek_ident() == Some("intrinsic") {
                        self.position += 1;
                        None
                    } else {
                        Some(self.expect_index("pointer alignment premise")?)
                    };
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::PointerAlignment { premise, result });
                }
                "pointer_word_equality" | "pointer_word" => {
                    self.expect_ident_spelling("relation")?;
                    let relation = self.expect_index("pointer word relation node")?;
                    self.expect_ident_spelling("alignments")?;
                    let alignments = self.parse_certificate_index_list("pointer alignment node")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::PointerWordEquality {
                        relation,
                        alignments,
                        result,
                    });
                }
                "pointer_word_from_alignment" | "pointer_word_aligned" => {
                    self.expect_ident_spelling("alignments")?;
                    let alignments = self.parse_certificate_index_list("pointer alignment node")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::PointerWordFromAlignment {
                        alignments,
                        result,
                    });
                }
                "float_reflexive" | "float_reflexivity" => {
                    self.expect_ident_spelling("finite")?;
                    let finite = self.expect_index("finite classification node")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::FloatReflexive { finite, result });
                }
                "conclusion" => {
                    if conclusion.is_some() {
                        return Err(self.error(
                            "special arithmetic certificate may contain only one `conclusion` line",
                        ));
                    }
                    conclusion = Some(self.expect_index("conclusion node")?);
                    self.expect(Token::Semicolon)?;
                }
                _ => {
                    return Err(self.error(format!(
                        "unknown special arithmetic certificate node `{keyword}`"
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let conclusion = conclusion.ok_or_else(|| {
            self.error("special arithmetic certificate must end with `conclusion N;`")
        })?;
        if nodes.is_empty() {
            return Err(self.error("special arithmetic certificate must contain a node"));
        }
        let premises = premises
            .into_iter()
            .enumerate()
            .map(|(index, premise)| {
                premise.ok_or_else(|| {
                    self.error(format!(
                        "special arithmetic premise indices must be contiguous; missing {index}"
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ProofTactic::ArithmeticCertificate(
            ArithmeticCertificate::special(SpecialArithmeticCertificate {
                premises,
                nodes,
                conclusion,
            }),
        ))
    }

    fn parse_certificate_index_list(&mut self, expected: &str) -> Result<Vec<usize>, ClickError> {
        self.expect(Token::LBracket)?;
        let mut indices = Vec::new();
        while self.peek() != Some(&Token::RBracket) {
            indices.push(self.expect_index(expected)?);
            if self.peek() == Some(&Token::Comma) {
                self.position += 1;
            } else {
                break;
            }
        }
        self.expect(Token::RBracket)?;
        Ok(indices)
    }

    fn parse_signed_int32_certificate_body(&mut self) -> Result<ProofTactic, ClickError> {
        self.expect(Token::LBrace)?;
        let mut nodes = Vec::new();
        let mut conclusion = None;
        while self.peek() != Some(&Token::RBrace) {
            let keyword = self.expect_ident("signed_int32 certificate node")?;
            let node = match keyword.as_str() {
                "premise" => {
                    let index = self.expect_index("premise index")?;
                    self.expect(Token::Colon)?;
                    let proposition = self.parse_proposition()?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::Premise {
                        index,
                        proposition,
                        result,
                    }
                }
                "scale" => {
                    let source = self.expect_index("scale source")?;
                    self.expect_ident_spelling("by")?;
                    let coefficient = self.parse_contract_expression()?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::Scale {
                        source,
                        coefficient,
                        result,
                    }
                }
                "add" => {
                    let left = self.expect_index("left node")?;
                    self.expect(Token::Comma)?;
                    let right = self.expect_index("right node")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::Add {
                        left,
                        right,
                        result,
                    }
                }
                "eq_to_le" => {
                    let source = self.expect_index("equality source")?;
                    let reverse = if self.peek_ident() == Some("reverse") {
                        self.position += 1;
                        true
                    } else {
                        false
                    };
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::EqualityToLessEqual {
                        source,
                        reverse,
                        result,
                    }
                }
                "eq_from_bounds" => {
                    let lower = self.expect_index("lower bound")?;
                    self.expect(Token::Comma)?;
                    let upper = self.expect_index("upper bound")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::EqualityFromBounds {
                        lower,
                        upper,
                        result,
                    }
                }
                "lt_from_neq" => {
                    let bound = self.expect_index("non-strict bound")?;
                    self.expect(Token::Comma)?;
                    let disequal = self.expect_index("disequality")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::StrictFromDisequal {
                        bound,
                        disequal,
                        result,
                    }
                }
                "trivial" => {
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::Trivial { result }
                }
                "interval_from_affine" => {
                    let source = self.expect_index("affine source")?;
                    let term = self.parse_contract_expression()?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalFromAffine {
                        source,
                        term,
                        lower,
                        upper,
                    }
                }
                "interval_from_affine_direct" => {
                    let source = self.expect_index("affine source")?;
                    let term = self.parse_contract_expression()?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalFromAffineDirect {
                        source,
                        term,
                        lower,
                        upper,
                    }
                }
                "interval_atom" => {
                    let term = self.parse_contract_expression()?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalAtom { term, lower, upper }
                }
                "defined" => {
                    let index = self.expect_index("defined premise index")?;
                    let term = self.parse_contract_expression()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::DefinedPremise { index, term }
                }
                "interval_intersect" => {
                    let left = self.expect_index("left interval")?;
                    self.expect(Token::Comma)?;
                    let right = self.expect_index("right interval")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalIntersect {
                        left,
                        right,
                        result: SignedInt32Interval { lower, upper },
                    }
                }
                "interval_add" | "interval_add_bounded" => {
                    let left = self.expect_index("left interval")?;
                    self.expect(Token::Comma)?;
                    let right = self.expect_index("right interval")?;
                    let defined = if keyword == "interval_add" {
                        self.expect_index("definedness node")?
                    } else {
                        usize::MAX
                    };
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    let result = SignedInt32Interval { lower, upper };
                    if keyword == "interval_add" {
                        SignedArithmeticStep::IntervalAdd {
                            left,
                            right,
                            defined,
                            result,
                        }
                    } else {
                        SignedArithmeticStep::IntervalAddBounded {
                            left,
                            right,
                            result,
                        }
                    }
                }
                "interval_subtract" | "interval_multiply" => {
                    let left = self.expect_index("left interval")?;
                    self.expect(Token::Comma)?;
                    let right = self.expect_index("right interval")?;
                    let defined = self.expect_index("definedness node")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    let result = SignedInt32Interval { lower, upper };
                    if keyword == "interval_subtract" {
                        SignedArithmeticStep::IntervalSubtract {
                            left,
                            right,
                            defined,
                            result,
                        }
                    } else {
                        SignedArithmeticStep::IntervalMultiply {
                            left,
                            right,
                            defined,
                            result,
                        }
                    }
                }
                "interval_remainder" => {
                    let operand = self.expect_index("operand interval")?;
                    let divisor = i32::try_from(self.expect_signed_i64("remainder divisor")?)
                        .map_err(|_| self.error("remainder divisor must fit in int32"))?;
                    let defined = self.expect_index("definedness node")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalRemainder {
                        operand,
                        divisor,
                        defined,
                        result: SignedInt32Interval { lower, upper },
                    }
                }
                "interval_shift_left" => {
                    let operand = self.expect_index("operand interval")?;
                    let shift = i32::try_from(self.expect_signed_i64("shift amount")?)
                        .map_err(|_| self.error("shift amount must fit in int32"))?;
                    let defined = self.expect_index("definedness node")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalShiftLeft {
                        operand,
                        shift,
                        defined,
                        result: SignedInt32Interval { lower, upper },
                    }
                }
                "interval_arithmetic_shift_right" => {
                    let operand = self.expect_index("operand interval")?;
                    let shift = i32::try_from(self.expect_signed_i64("shift amount")?)
                        .map_err(|_| self.error("shift amount must fit in int32"))?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalArithmeticShiftRight {
                        operand,
                        shift,
                        result: SignedInt32Interval { lower, upper },
                    }
                }
                "interval_bitwise_and" => {
                    let operand = self.expect_index("operand interval")?;
                    let mask = self.expect_number("bitwise mask")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalBitwiseAnd {
                        operand,
                        mask,
                        result: SignedInt32Interval { lower, upper },
                    }
                }
                "interval_sign_bit_flip" => {
                    let operand = self.expect_index("operand interval")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalSignBitFlip {
                        operand,
                        result: SignedInt32Interval { lower, upper },
                    }
                }
                "interval_compare" => {
                    let left = self.expect_index("left interval")?;
                    self.expect(Token::Comma)?;
                    let right = self.expect_index("right interval")?;
                    let comparison = match self.expect_ident("comparison")?.as_str() {
                        "lt" => SignedInt32Comparison::LessThan,
                        "le" => SignedInt32Comparison::LessEqual,
                        "eq" => SignedInt32Comparison::Equal,
                        "ne" => SignedInt32Comparison::Disequal,
                        other => {
                            return Err(
                                self.error(format!("unknown signed_int32 comparison `{other}`"))
                            );
                        }
                    };
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalCompare {
                        left,
                        right,
                        comparison,
                        result,
                    }
                }
                "affine_conclusion" => {
                    let source = self.expect_index("affine source")?;
                    let evidence = self.expect_index("interval evidence")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::AffineConclusion {
                        source,
                        evidence,
                        result,
                    }
                }
                "affine_conclusion_pair" => {
                    let source = self.expect_index("affine source")?;
                    let left_evidence = self.expect_index("left interval evidence")?;
                    let right_evidence = self.expect_index("right interval evidence")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::AffineConclusionWithEvidence {
                        source,
                        left_evidence,
                        right_evidence,
                        result,
                    }
                }
                "conclusion" => {
                    if conclusion.is_some() {
                        return Err(self.error(
                            "signed_int32 certificate may contain only one `conclusion` line",
                        ));
                    }
                    conclusion = Some(self.expect_index("conclusion node")?);
                    self.expect(Token::Semicolon)?;
                    continue;
                }
                _ => {
                    return Err(
                        self.error(format!("unknown signed_int32 certificate node `{keyword}`"))
                    );
                }
            };
            nodes.push(node);
        }
        self.expect(Token::RBrace)?;
        let conclusion = conclusion
            .ok_or_else(|| self.error("signed_int32 certificate must end with `conclusion N;`"))?;
        if nodes.is_empty() {
            return Err(self.error("signed_int32 certificate must contain a node"));
        }
        Ok(ProofTactic::ArithmeticCertificate(ArithmeticCertificate {
            family: ArithmeticCertificateFamily::SignedInt32(SignedInt32Certificate {
                nodes,
                conclusion,
            }),
        }))
    }

    fn parse_arithmetic_certificate_body(&mut self) -> Result<ProofTactic, ClickError> {
        self.expect(Token::LBrace)?;
        let mut nodes = Vec::new();
        let mut conclusion = None;
        while self.peek() != Some(&Token::RBrace) {
            let keyword = self.expect_ident("integer certificate node")?;
            match keyword.as_str() {
                "premise" => {
                    let index = self.expect_index("premise index")?;
                    self.expect(Token::Colon)?;
                    let proposition = self.parse_proposition()?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::Premise {
                        index,
                        proposition,
                        result,
                    });
                }
                "scale" => {
                    let source = self.expect_index("scale source")?;
                    self.expect_ident_spelling("by")?;
                    let coefficient = self.parse_contract_expression()?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::Scale {
                        source,
                        coefficient,
                        result,
                    });
                }
                "add" => {
                    let left = self.expect_index("left node")?;
                    self.expect(Token::Comma)?;
                    let right = self.expect_index("right node")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::Add {
                        left,
                        right,
                        result,
                    });
                }
                "eq_to_le" => {
                    let source = self.expect_index("equality source")?;
                    let reverse = if self.peek_ident() == Some("reverse") {
                        self.position += 1;
                        true
                    } else {
                        false
                    };
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::EqualityToLessEqual {
                        source,
                        reverse,
                        result,
                    });
                }
                "eq_from_bounds" => {
                    let lower = self.expect_index("lower bound")?;
                    self.expect(Token::Comma)?;
                    let upper = self.expect_index("upper bound")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::EqualityFromBounds {
                        lower,
                        upper,
                        result,
                    });
                }
                "trivial" => {
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::Trivial { result });
                }
                "conclusion" => {
                    if conclusion.is_some() {
                        return Err(self
                            .error("integer certificate may contain only one `conclusion` line"));
                    }
                    conclusion = Some(self.expect_index("conclusion node")?);
                    self.expect(Token::Semicolon)?;
                }
                _ => {
                    return Err(self.error(format!("unknown integer certificate node `{keyword}`")));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let conclusion = conclusion
            .ok_or_else(|| self.error("integer certificate must end with `conclusion N;`"))?;
        if nodes.is_empty() {
            return Err(self.error("integer certificate must contain a node"));
        }
        Ok(ProofTactic::ArithmeticCertificate(
            ArithmeticCertificate::integer(IntegerCertificate { nodes, conclusion }),
        ))
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
            Some(Token::Ident(name)) if name == "frame" => {
                return Err(self.error(
                    "`frame` was removed; ownership frames untouched memory with no tactic",
                ));
            }
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
        let first = self.parse_contract_unary()?;
        self.parse_contract_binary_suffix(first)
    }

    // Keep the operator stacks out of the recursive primary-expression
    // parser frame. A nested conditional retains only the small dispatcher
    // above while its child expression is parsed.
    #[inline(never)]
    fn parse_contract_binary_suffix(
        &mut self,
        first: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let mut values = vec![first];
        let mut operators: Vec<(usize, ContractBinaryConstructor)> = Vec::new();
        // Each precedence level has the same independently enforced chain
        // limit as the former recursive-descent level. A lower-precedence
        // operator starts a new higher-precedence segment.
        let mut operands_by_precedence = [0usize; 7];

        while let Some((precedence, constructor)) = self.peek().and_then(contract_binary_operator) {
            let operands = &mut operands_by_precedence[precedence];
            if *operands == 0 {
                *operands = 1;
            }
            self.check_expression_chain_limit(*operands)?;
            *operands += 1;
            operands_by_precedence[(precedence + 1)..].fill(0);

            while operators
                .last()
                .is_some_and(|(pending_precedence, _)| *pending_precedence >= precedence)
            {
                let (_, pending) = operators.pop().expect("the operator stack is nonempty");
                reduce_contract_binary_expression(&mut values, pending);
            }
            self.position += 1;
            operators.push((precedence, constructor));
            values.push(self.parse_contract_unary()?);
        }

        while let Some((_, constructor)) = operators.pop() {
            reduce_contract_binary_expression(&mut values, constructor);
        }
        Ok(values
            .pop()
            .expect("a contract expression has at least one operand"))
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
        self.expect_ident_spelling("viewable")?;
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
        let address = self.peek() == Some(&Token::Amp);
        if address {
            self.position += 1;
        }
        let (mut surface_base, mut base) = if typed_load_type_from_name(self.peek_ident()).is_some()
            && self.peek_next() == Some(&Token::LParen)
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
            ContractExpression::CFragment(CExpression::Cast { pointee_struct, .. }) => {
                pointee_struct.clone()
            }
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
        let mut postfixes = 0;
        while matches!(self.peek(), Some(Token::Arrow | Token::Dot))
            || (self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range())
        {
            self.check_expression_chain_limit(postfixes)?;
            postfixes += 1;
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
                    if field.c_type.is_pointer() && !address {
                        return Err(self.error(format!(
                            "pointer field `{field_name}` requires an explicit range for its contents or `&` for its storage"
                        )));
                    }
                    self.validate_field_place(&field)?;
                    let mut segment = Self::field_segment_from_metadata(
                        base,
                        Some(surface_base.clone()),
                        &field_name,
                        &field,
                    );
                    if let ContractSegmentSurface::Field {
                        address: spelling, ..
                    } = &mut segment.surface
                    {
                        *spelling = address;
                    }
                    return Ok(vec![segment]);
                }
                if let Some(base_struct_name) = &struct_name
                    && self.struct_layouts.contains_key(base_struct_name)
                {
                    let field =
                        self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                    if field.struct_name.is_some() && !field.c_type.is_pointer() {
                        if !allow_aggregates {
                            return Err(
                                self.error("whole-struct views require a declared resource")
                            );
                        }
                        return self.aggregate_field_segments(base, &field_name, &field);
                    }
                    if field.c_type.is_pointer() && !address {
                        return Err(self.error(format!(
                            "pointer field `{field_name}` requires an explicit range for its contents or `&` for its storage"
                        )));
                    }
                    self.validate_field_place(&field)?;
                    let mut segment = Self::field_segment_from_metadata(
                        base,
                        Some(surface_base.clone()),
                        &field_name,
                        &field,
                    );
                    if let ContractSegmentSurface::Field {
                        address: spelling, ..
                    } = &mut segment.surface
                    {
                        *spelling = address;
                    }
                    return Ok(vec![segment]);
                }
                let mut segment =
                    self.resolve_field_segment(base, Some(surface_base.clone()), &field_name)?;
                if let ContractSegmentSurface::Field {
                    address: spelling, ..
                } = &mut segment.surface
                {
                    *spelling = address;
                }
                return Ok(vec![segment]);
            }
            let (
                lowered,
                next_struct_name,
                next_union_name,
                next_array_element_width,
                next_array_shape,
                field_memory_pointer,
                field_offset_bytes,
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
                    field.offset_bytes,
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
                    field.offset_bytes,
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
                    0,
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
                            | CType::Int8Array(_)
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
                offset_bytes: field_offset_bytes,
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
                    address: false,
                    // `surface_base` has already absorbed this field name, so
                    // there is no parent spelling left to print beside it.
                    base: None,
                    name,
                    element_width: Some(element_width),
                    element_type: Some(element_type),
                },
            }]);
        }
        if !address && struct_name.is_some() && self.peek() != Some(&Token::LBracket) {
            return Err(self.error("whole-struct views require a declared resource"));
        }
        if address {
            base = match base {
                CExpression::TypedLoad { pointer, .. } => *pointer,
                CExpression::Value(CValue::Pointer(_)) => {
                    let ContractExpression::CFragment(CExpression::Variable(name)) = &surface_base
                    else {
                        return Err(self.error("cannot take the address of this C expression"));
                    };
                    self.qualified_object(name)
                        .and_then(|object| object.address.clone())
                        .ok_or_else(|| self.error("cannot take the address of this C expression"))?
                }
                expression => CExpression::AddressOf(Box::new(expression)),
            };
            surface_base = ContractExpression::CFragment(CExpression::AddressOf(Box::new(
                contract_expression_as_c_fragment(&surface_base).expect("C segment base"),
            )));
            if self.peek() != Some(&Token::LBracket) {
                return Ok(vec![ContractSegment {
                    state: ContractSegmentState::Current,
                    base,
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                    surface: ContractSegmentSurface::Range {
                        base: surface_base,
                        start: ContractExpression::CFragment(CExpression::Value(int32(0))),
                        end: ContractExpression::CFragment(CExpression::Value(int32(1))),
                    },
                }]);
            }
        }
        self.expect(Token::LBracket)?;
        let start_expression = self.parse_contract_expression()?;
        let mut start = resource_body_c_fragment(&start_expression).ok_or_else(|| {
            self.error(
                "memory segment start must be a current C expression or a scalar field of the resource being defined",
            )
        })?;
        self.expect(Token::DotDot)?;
        let end_expression = self.parse_contract_expression()?;
        let mut end = resource_body_c_fragment(&end_expression).ok_or_else(|| {
            self.error(
                "memory segment end must be a current C expression or a scalar field of the resource being defined",
            )
        })?;
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
                // An aggregate leaf's name is already the whole dotted path
                // from this base, so it prints beside the lowered base.
                None,
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
        surface_base: Option<ContractExpression>,
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
                    address: false,
                    base: surface_base.map(Box::new),
                    name: field_name.to_string(),
                    element_width: None,
                    element_type: None,
                },
            });
        };
        self.validate_field_place(&field)?;
        Ok(Self::field_segment_from_metadata(
            base,
            surface_base,
            field_name,
            &field,
        ))
    }

    fn field_segment_from_metadata(
        base: CExpression,
        surface_base: Option<ContractExpression>,
        field_name: &str,
        field: &ResolvedField,
    ) -> ContractSegment {
        let array = match field.c_type {
            C0Type::Int32Array(length) => Some((length, 4, CType::Int32)),
            C0Type::Int64Array(length) => Some((length, 8, CType::Int64)),
            C0Type::UInt64Array(length) => Some((length, 8, CType::UInt64)),
            C0Type::CharArray(length) | C0Type::UInt8Array(length) => {
                Some((length, 1, CType::UInt8))
            }
            _ => None,
        };
        if let Some((length, element_width, element_type)) = array {
            let field_base = crate::kernel::c_pointer_offset_bytes(base, field.offset_bytes);
            return ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::TypedLoad {
                    pointer: Box::new(field_base),
                    value_type: field.c_type.to_kernel_type(),
                    volatile: false,
                    pointee_constant: field.pointee_constant,
                    source: Default::default(),
                },
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(length)),
                surface: ContractSegmentSurface::Field {
                    address: false,
                    base: surface_base.map(Box::new),
                    name: field_name.to_string(),
                    element_width: Some(element_width),
                    element_type: Some(element_type),
                },
            };
        }
        let element_width = match field.c_type {
            C0Type::Char => 1,
            C0Type::UInt8 => 1,
            C0Type::Int8 => 1,
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
                address: false,
                base: surface_base.map(Box::new),
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
            pointee_constant: field.pointee_constant,
            source: Default::default(),
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
            C0Expression::Cast { struct_name, .. } => struct_name.as_ref(),
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
                        pointee_constant: field.pointee_constant,
                        field_struct_name: None,
                        function_pointer_signature: None,
                        array_shape: None,
                        source: None,
                    }
                }
            } else {
                C0Expression::Field {
                    pointer: Box::new(pointer),
                    field_type: field.c_type,
                    pointee_constant: field.pointee_constant,
                    field_struct_name: field.struct_name,
                    function_pointer_signature: field.function_pointer_signature.clone(),
                    array_shape: field.array_shape,
                    source: None,
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
                pointee_constant: field.pointee_constant,
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
            self.reject_non_struct_arm_base(base_name, field_name)?;
            return Ok(None);
        };
        if !self.struct_layouts.contains_key(struct_name) {
            return Ok(None);
        }
        self.resolve_struct_field_metadata(struct_name, field_name)
            .map(Some)
    }

    /// Finds the struct layout reached by a contract expression, retaining
    /// the layout through an entry-state or recorded-state wrapper. The
    /// pointer value may come from another snapshot while a later field load
    /// still reads the surrounding state.
    fn contract_expression_struct_name(&self, expression: &ContractExpression) -> Option<String> {
        match expression {
            ContractExpression::CFragment(CExpression::Cast { pointee_struct, .. }) => {
                pointee_struct.clone()
            }
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_struct_params
                .get(name)
                .or_else(|| self.current_aggregate_objects.get(name))
                .cloned(),
            ContractExpression::Field { base, field, .. } => {
                let struct_name = self.contract_expression_struct_name(base)?;
                self.resolve_struct_field_metadata(&struct_name, field)
                    .ok()?
                    .struct_name
            }
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.contract_expression_struct_name(inner),
            _ => None,
        }
    }

    /// Refuses a match-arm constructor binding that is not a struct pointer as
    /// the base of a field place. Without this the arm body would keep the
    /// field name for lowering to resolve, which for a binding no later pass
    /// can give a layout means a width-unknown load and a fold that reports
    /// only that it could not evaluate the instance memory body.
    fn reject_non_struct_arm_base(
        &self,
        base_name: &str,
        field_name: &str,
    ) -> Result<(), ClickError> {
        let Some(field) = self.current_arm_binding_types.get(base_name) else {
            return Ok(());
        };
        Err(self.error(format!(
            "match-arm binding `{base_name}` is declared `{}`, so `{base_name}->{field_name}` has no struct layout; only a `struct ...*` binding is a memory base in a match arm body",
            field.describe()
        )))
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
        if field.is_long_double() {
            return Err(
                self.error("long double member value operations need an extended-precision model")
            );
        }
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
            pointee_constant: field.pointee_is_constant(),
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
        if field.is_long_double() {
            return Err(
                self.error("long double member value operations need an extended-precision model")
            );
        }
        Ok(ResolvedField {
            c_type: field.c_type(),
            pointee_constant: field.pointee_is_constant(),
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
            C0Type::Int32Array(_)
                | C0Type::CharArray(_)
                | C0Type::UInt8Array(_)
                | C0Type::Int64Array(_)
                | C0Type::UInt64Array(_)
        ) {
            let width = match field.c_type {
                C0Type::Int64Array(_) | C0Type::UInt64Array(_) => 8,
                C0Type::Int32Array(_) => 4,
                _ => 1,
            };
            if !field.offset_bytes.is_multiple_of(width)
                || field.slot_end_bytes < field.offset_bytes
                || !(field.slot_end_bytes - field.offset_bytes).is_multiple_of(width)
            {
                return Err(self.error("inline array field has an invalid resource extent"));
            }
            return Ok(());
        }
        if matches!(field.c_type, C0Type::Int16 | C0Type::UInt16) {
            if !field.offset_bytes.is_multiple_of(2)
                || field.byte_width != 2
                || field.slot_end_bytes < field.offset_bytes
                || !(field.slot_end_bytes - field.offset_bytes).is_multiple_of(2)
            {
                return Err(self.error("16-bit field places require two-byte alignment and width"));
            }
            return Ok(());
        }
        if matches!(field.c_type, C0Type::Int64 | C0Type::UInt64) {
            if !field.offset_bytes.is_multiple_of(8)
                || field.byte_width != 8
                || field.slot_end_bytes < field.offset_bytes
                || !(field.slot_end_bytes - field.offset_bytes).is_multiple_of(8)
            {
                return Err(
                    self.error("64-bit field places require eight-byte alignment and width")
                );
            }
            return Ok(());
        }
        if matches!(field.c_type, C0Type::Int8 | C0Type::Char | C0Type::UInt8) {
            if field.byte_width != 1 || field.slot_end_bytes < field.offset_bytes {
                return Err(self.error("byte field places require one-byte width"));
            }
            return Ok(());
        }
        if !field.offset_bytes.is_multiple_of(4)
            || !field.byte_width.is_multiple_of(4)
            || !field.slot_end_bytes.is_multiple_of(4)
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

    /// Recognizes `( [const] struct name [const] * )` at the cursor without
    /// consuming it. A struct-pointer cast is the only pointer cast contract
    /// expressions accept; it lets a contract over an opaque `void *`
    /// parameter name the object the C body reaches through the same cast.
    fn peek_struct_pointer_cast(&self) -> Option<StructPointerCast> {
        let mut index = self.position;
        if self.tokens.get(index) != Some(&Token::LParen) {
            return None;
        }
        index += 1;
        let mut pointee_constant = false;
        if matches!(self.tokens.get(index), Some(Token::Ident(name)) if name == "const") {
            pointee_constant = true;
            index += 1;
        }
        if !matches!(self.tokens.get(index), Some(Token::Ident(name)) if name == "struct") {
            return None;
        }
        index += 1;
        let Some(Token::Ident(struct_name)) = self.tokens.get(index) else {
            return None;
        };
        let struct_name = struct_name.clone();
        index += 1;
        if matches!(self.tokens.get(index), Some(Token::Ident(name)) if name == "const") {
            pointee_constant = true;
            index += 1;
        }
        if self.tokens.get(index) != Some(&Token::Star) {
            return None;
        }
        index += 1;
        if self.tokens.get(index) != Some(&Token::RParen) {
            return None;
        }
        Some(StructPointerCast {
            struct_name,
            pointee_constant,
            tokens: index + 1 - self.position,
        })
    }

    fn consume_struct_pointer_cast(&mut self, cast: &StructPointerCast) -> Result<(), ClickError> {
        if !self.struct_layouts.contains_key(&cast.struct_name) {
            return Err(self.error(format!(
                "unknown struct declaration `{}` in pointer cast",
                cast.struct_name
            )));
        }
        self.position += cast.tokens;
        Ok(())
    }

    /// A struct-pointer cast applies to one `void *` parameter of the block
    /// under contract, and a block casts a parameter to one struct only, so
    /// synthesized proof text reads the parameter with a single layout.
    fn record_parameter_struct_cast(
        &mut self,
        operand: Option<&str>,
        struct_name: &str,
    ) -> Result<(), ClickError> {
        let Some(name) = operand.filter(|name| self.current_void_pointer_params.contains(*name))
        else {
            return Err(self.error(
                "a struct pointer cast applies to a `void *` parameter of the function under contract",
            ));
        };
        match self.current_parameter_struct_casts.get(name) {
            Some(previous) if previous != struct_name => Err(self.error(format!(
                "parameter `{name}` is already cast to `struct {previous}`; a contract casts a parameter to one struct"
            ))),
            _ => {
                self.current_parameter_struct_casts
                    .insert(name.to_string(), struct_name.to_string());
                Ok(())
            }
        }
    }

    fn parse_contract_unary(&mut self) -> Result<ContractExpression, ClickError> {
        self.parse_contract_unary_at_depth(0)
    }

    fn parse_contract_unary_at_depth(
        &mut self,
        depth: usize,
    ) -> Result<ContractExpression, ClickError> {
        if let Some(cast) = self.peek_struct_pointer_cast() {
            self.check_unary_nesting_limit(depth)?;
            self.consume_struct_pointer_cast(&cast)?;
            let operand = self.parse_contract_unary_at_depth(depth + 1)?;
            let Some(operand) = contract_expression_as_c_fragment(&operand) else {
                return Err(self.error(
                    "struct pointer cast expects a current C `void *` expression; put old(...) around the whole cast for an entry-state value",
                ));
            };
            let operand_name = match &operand {
                CExpression::Variable(name) => Some(name.as_str()),
                _ => None,
            };
            self.record_parameter_struct_cast(operand_name, &cast.struct_name)?;
            return Ok(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(operand),
                target_type: CType::Int32Pointer,
                pointee_struct: Some(cast.struct_name),
                pointee_volatile: false,
                pointee_constant: cast.pointee_constant,
            }));
        }
        if self.peek() == Some(&Token::LParen)
            && matches!(self.peek_next(), Some(Token::Ident(name)) if name == "uint32")
        {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            let target_type = self.parse_type()?.c_type.to_kernel_type();
            if target_type.is_pointer() {
                return Err(self.error("contract scalar casts do not accept pointer target types"));
            }
            self.expect(Token::RParen)?;
            let operand = self.parse_contract_unary_at_depth(depth + 1)?;
            let Some(expression) = contract_expression_as_c_fragment(&operand) else {
                return Err(self.error("scalar cast expects a current C expression; put old(...) around the whole cast for an entry-state value"));
            };
            return Ok(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(expression),
                target_type,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
            }));
        }
        if self.peek() == Some(&Token::Minus) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            return Ok(ContractExpression::Negate(Box::new(
                self.parse_contract_unary_at_depth(depth + 1)?,
            )));
        }
        if self.peek() == Some(&Token::Tilde) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            return Ok(ContractExpression::BitwiseNot(Box::new(
                self.parse_contract_unary_at_depth(depth + 1)?,
            )));
        }
        if self.peek() == Some(&Token::Star) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            let pointer = self.parse_contract_unary_at_depth(depth + 1)?;
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
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            let expression = self.parse_contract_unary_at_depth(depth + 1)?;
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
            ContractExpression::CFragment(CExpression::Cast { pointee_struct, .. }) => {
                pointee_struct.clone()
            }
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .current_struct_params
                .get(name)
                .or_else(|| self.current_aggregate_objects.get(name))
                .cloned(),
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.contract_expression_struct_name(inner),
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
        let mut postfixes = 0;
        loop {
            if !matches!(
                self.peek(),
                Some(Token::LBracket | Token::Arrow | Token::Dot)
            ) {
                return Ok(expression);
            }
            self.check_expression_chain_limit(postfixes)?;
            postfixes += 1;
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
                        let lowered_base = contract_expression_as_c_fragment(&expression)
                            .ok_or_else(|| {
                                self.error("global array base must be a current C expression")
                            })?;
                        let offset = flatten_array_indices(indexes.clone(), &shape);
                        expression = ContractExpression::ArrayIndex {
                            base: Box::new(expression),
                            indexes,
                            lowered: CExpression::Index(Box::new(lowered_base), Box::new(offset)),
                        };
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
                    let base = match &expression {
                        ContractExpression::Old(inner)
                        | ContractExpression::At {
                            expression: inner, ..
                        } => contract_expression_as_c_fragment(inner),
                        _ => contract_expression_as_c_fragment(&expression),
                    }
                    .ok_or_else(|| self.error("field access requires a C pointer expression"))?;
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
                            offset_bytes: field.offset_bytes,
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
                            offset_bytes: field.offset_bytes,
                        };
                    } else {
                        expression = ContractExpression::Field {
                            base: Box::new(surface_base),
                            field: field_name.clone(),
                            lowered: self.resolve_field_load(base, &field_name)?,
                            offset_bytes: 0,
                        };
                        struct_array_element_width = None;
                        struct_array_shape = None;
                        scalar_array_shape = None;
                    }
                }
                _ => unreachable!("postfix expression token checked above"),
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
        Ok(ContractExpression::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms,
        })
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
        if self.peek_ident() == Some("if") {
            if self.contract_if_nesting >= CONTRACT_IF_NESTING_LIMIT {
                return Err(self.error(format!(
                    "contract conditional expression nesting exceeds Click's supported depth of {CONTRACT_IF_NESTING_LIMIT}"
                )));
            }
            self.contract_if_nesting += 1;
            let result = self.parse_contract_if_expression();
            self.contract_if_nesting -= 1;
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
            return self.parse_contract_sequence_literal();
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
            if self.contract_expression_nesting >= CONTRACT_LET_RECURSION_LIMIT {
                return Err(self.error(format!(
                    "nested contract value binding exceeds Click's supported depth of {CONTRACT_LET_RECURSION_LIMIT}"
                )));
            }
            self.contract_expression_nesting += 1;
            let result = self.parse_contract_value_let_expression();
            self.contract_expression_nesting -= 1;
            return result;
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
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
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

        let typed_load = typed_load_type_from_name(self.peek_ident());
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
                pointee_constant: false,
                source: Default::default(),
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
                if self.current_contract_bindings.contains(&name)
                    || self.current_integer_params.contains(&name)
                    || self.current_integer_lets.contains(&name)
                {
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
            // Keep unsuffixed specification numerals contextual until typing.
            // A surrounding conversion or Integer-valued expression may supply
            // that context even when the enclosing theorem has only C params.
            Some(Token::Number(value)) => Ok(ContractExpression::IntegerLiteral(value.to_string())),
            Some(Token::BigNumber(value)) => Ok(ContractExpression::IntegerLiteral(value)),
            Some(Token::UnsuffixedInt64(value)) => {
                Ok(ContractExpression::IntegerLiteral(value.to_string()))
            }
            Some(Token::UnsuffixedUInt64(value)) => {
                Ok(ContractExpression::IntegerLiteral(value.to_string()))
            }
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

    fn parse_contract_sequence_literal(&mut self) -> Result<ContractExpression, ClickError> {
        let mut frames = vec![Vec::new()];
        self.position += 1;
        loop {
            if self.peek() == Some(&Token::RBracket) {
                self.position += 1;
                let sequence = ContractExpression::SequenceLiteral(
                    frames.pop().expect("sequence literal frame"),
                );
                if let Some(parent) = frames.last_mut() {
                    parent.push(sequence);
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                    }
                    continue;
                }
                return Ok(sequence);
            }

            if self.peek() == Some(&Token::LBracket) {
                self.check_expression_chain_limit(frames.len())?;
                self.position += 1;
                frames.push(Vec::new());
                continue;
            }

            let element = self.parse_contract_expression()?;
            let Some(frame) = frames.last_mut() else {
                unreachable!("sequence literal parser always has a frame")
            };
            frame.push(element);
            match self.peek() {
                Some(Token::Comma) => self.position += 1,
                Some(Token::RBracket) => {}
                Some(token) => {
                    return Err(self.error(format!(
                        "expected `,` or `]` after sequence element, got {token:?}"
                    )));
                }
                None => return Err(self.error("expected `]` after sequence element")),
            }
        }
    }

    fn parse_contract_value_let_expression(&mut self) -> Result<ContractExpression, ClickError> {
        let mut bindings = Vec::new();
        loop {
            if bindings.len() >= CONTRACT_LET_CHAIN_LIMIT {
                return Err(self.error(format!(
                    "contract value-binding chain exceeds Click's supported depth of {CONTRACT_LET_CHAIN_LIMIT}"
                )));
            }
            let binding = self.parse_contract_let_binding()?;
            let ContractLetBindingKind::Value(value) = binding.kind else {
                return Err(self.error("let ... where is a proposition binding, not an expression"));
            };
            let binding_was_in_scope = !self.current_contract_bindings.insert(binding.name.clone());
            let previous_integer_context = self.integer_literal_context;
            let click_type = binding.click_type;
            self.integer_literal_context |= matches!(click_type, Some(ClickType::Integer));
            bindings.push((
                binding.name,
                click_type,
                value,
                binding_was_in_scope,
                previous_integer_context,
            ));
            if self.peek_ident() != Some("let") {
                break;
            }
        }

        let body = self.parse_contract_expression();
        for (name, _, _, binding_was_in_scope, previous_integer_context) in bindings.iter().rev() {
            self.integer_literal_context = *previous_integer_context;
            if !*binding_was_in_scope {
                self.current_contract_bindings.remove(name);
            }
        }
        let mut body = body?;
        for (name, click_type, value, _, _) in bindings.into_iter().rev() {
            body = ContractExpression::Let {
                name,
                click_type,
                value: Box::new(value),
                body: Box::new(body),
            };
        }
        Ok(body)
    }

    fn parse_contract_if_expression(&mut self) -> Result<ContractExpression, ClickError> {
        self.position += 1;
        // These children are boxed in the AST. Box each one as soon as it is
        // parsed so a nested conditional does not retain large enum values in
        // every parser stack frame while parsing its next child.
        let condition = Box::new(self.parse_proposition()?);
        self.expect(Token::LBrace)?;
        let then_branch = Box::new(self.parse_contract_expression()?);
        self.expect(Token::RBrace)?;
        if self.peek_ident() != Some("else") {
            return Err(self.error("expected `else` in `if` expression"));
        }
        self.position += 1;
        self.expect(Token::LBrace)?;
        let else_branch = Box::new(self.parse_contract_expression()?);
        self.expect(Token::RBrace)?;
        Ok(ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        })
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
        if self.peek() == Some(&Token::LessThan) {
            if self.algebraic_type_nesting >= ALGEBRAIC_TYPE_NESTING_LIMIT {
                return Err(self.error(format!(
                    "algebraic datatype nesting exceeds Click's supported depth of {ALGEBRAIC_TYPE_NESTING_LIMIT}"
                )));
            }
            self.algebraic_type_nesting += 1;
            let result = self.parse_algebraic_type_application_arguments(name);
            self.algebraic_type_nesting -= 1;
            return result;
        }
        Ok(AlgebraicTypeApplication {
            rigid: false,
            name,
            arguments: Vec::new(),
        })
    }

    fn parse_algebraic_type_application_arguments(
        &mut self,
        name: String,
    ) -> Result<AlgebraicTypeApplication, ClickError> {
        self.position += 1;
        let mut arguments = Vec::new();
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
        let mut operands = 1;
        while self.peek() == Some(&Token::Pipe) {
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_bitwise_xor()?;
            expression = C0Expression::BitwiseOr(Box::new(expression), Box::new(right));
            operands += 1;
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_xor(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_and()?;
        let mut operands = 1;
        while self.peek() == Some(&Token::Caret) {
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_bitwise_and()?;
            expression = C0Expression::BitwiseXor(Box::new(expression), Box::new(right));
            operands += 1;
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_and(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_shift()?;
        let mut operands = 1;
        while self.peek() == Some(&Token::Amp) {
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_shift()?;
            expression = C0Expression::BitwiseAnd(Box::new(expression), Box::new(right));
            operands += 1;
        }
        Ok(expression)
    }

    fn parse_ensure_shift(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_add()?;
        let mut operands = 1;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    operands += 1;
                    C0Expression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    operands += 1;
                    C0Expression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_add(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_multiply()?;
        let mut operands = 1;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    operands += 1;
                    C0Expression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    operands += 1;
                    C0Expression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_multiply(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_unary()?;
        let mut operands = 1;
        while let Some(operator) = self.peek() {
            let constructor = match operator {
                Token::Star => C0Expression::Multiply,
                Token::Slash => C0Expression::Divide,
                Token::Percent => C0Expression::Remainder,
                _ => break,
            };
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_unary()?;
            operands += 1;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_unary(&mut self) -> Result<C0Expression, ClickError> {
        self.parse_ensure_unary_at_depth(0)
    }

    fn parse_ensure_unary_at_depth(&mut self, depth: usize) -> Result<C0Expression, ClickError> {
        if self.peek() == Some(&Token::Minus) {
            self.check_unary_nesting_limit(depth)?;
            if let Some(value) = self.peek_next().and_then(negatable_int32_magnitude) {
                self.position += 2;
                return Ok(C0Expression::Int32Literal(0u32.wrapping_sub(value)));
            }
            self.position += 1;
            return Ok(C0Expression::Subtract(
                Box::new(C0Expression::Int32Literal(0)),
                Box::new(self.parse_ensure_unary_at_depth(depth + 1)?),
            ));
        }
        if self.peek() == Some(&Token::Tilde) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            return Ok(C0Expression::BitwiseNot(Box::new(
                self.parse_ensure_unary_at_depth(depth + 1)?,
            )));
        }
        if self.peek() == Some(&Token::Amp) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            return Ok(C0Expression::AddressOf(Box::new(
                self.parse_ensure_unary_at_depth(depth + 1)?,
            )));
        }

        self.parse_ensure_postfix()
    }

    fn parse_ensure_postfix(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_primary()?;
        let mut postfixes = 0;
        loop {
            if !matches!(
                self.peek(),
                Some(Token::LBracket | Token::Arrow | Token::Dot)
            ) {
                return Ok(expression);
            }
            self.check_expression_chain_limit(postfixes)?;
            postfixes += 1;
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
                _ => unreachable!("postfix expression token checked above"),
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
                self.position -= 1;
                if let Some(cast) = self.peek_struct_pointer_cast() {
                    self.consume_struct_pointer_cast(&cast)?;
                    let operand = self.parse_ensure_unary()?;
                    let operand_name = match &operand {
                        C0Expression::Variable(name) => Some(name.as_str()),
                        _ => None,
                    };
                    self.record_parameter_struct_cast(operand_name, &cast.struct_name)?;
                    return Ok(C0Expression::Cast {
                        expression: Box::new(operand),
                        c_type: C0Type::Int32Pointer,
                        struct_name: Some(cast.struct_name),
                        pointee_volatile: false,
                        pointee_constant: cast.pointee_constant,
                    });
                }
                self.position += 1;
                let expression = self.parse_ensure_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected result expression, got {token:?}"))),
            None => Err(self.error("expected result expression, got end of input")),
        }
    }

    fn check_expression_chain_limit(&self, operands: usize) -> Result<(), ClickError> {
        if operands >= EXPRESSION_CHAIN_LIMIT {
            Err(self.error(format!(
                "expression operator nesting exceeds Click's supported depth of {EXPRESSION_CHAIN_LIMIT}"
            )))
        } else {
            Ok(())
        }
    }

    fn check_unary_nesting_limit(&self, depth: usize) -> Result<(), ClickError> {
        if depth >= UNARY_NESTING_LIMIT {
            Err(self.error(format!(
                "expression unary nesting exceeds Click's supported depth of {UNARY_NESTING_LIMIT}"
            )))
        } else {
            Ok(())
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

    fn expect_signed_i64(&mut self, expected: &str) -> Result<i64, ClickError> {
        let parenthesized = if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            true
        } else {
            false
        };
        let negative = if self.peek() == Some(&Token::Minus) {
            self.position += 1;
            true
        } else {
            false
        };
        let at = self.error_context();
        let value = match self.next() {
            Some(Token::Number(value)) => i64::from(value),
            Some(Token::UnsuffixedInt64(value) | Token::Int64Number(value)) => value,
            Some(Token::UnsuffixedUInt64(value) | Token::UInt64Number(value)) => {
                i64::try_from(value).map_err(|_| {
                    self.error_at(at.clone(), format!("expected {expected} to fit in int64"))
                })?
            }
            Some(Token::BigNumber(value)) => value.parse::<i64>().map_err(|_| {
                self.error_at(at.clone(), format!("expected {expected} to fit in int64"))
            })?,
            Some(token) => {
                return Err(self.error_at(
                    at.clone(),
                    format!("expected {expected}, got {}", token.describe()),
                ));
            }
            None => {
                return Err(
                    self.error_at(at.clone(), format!("expected {expected}, got end of input"))
                );
            }
        };
        let value = if negative {
            value.checked_neg().ok_or_else(|| {
                self.error_at(at.clone(), format!("expected {expected} to fit in int64"))
            })
        } else {
            Ok(value)
        }?;
        if parenthesized {
            self.expect(Token::RParen)?;
        }
        Ok(value)
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
            .cloned()
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
            .cloned()
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
            .cloned()
    }

    /// Captures the position of the next unconsumed token so an error can
    /// still point at it after the token is consumed.
    fn error_context(&self) -> Option<SourcePosition> {
        self.here()
    }

    fn error_at(&self, at: Option<SourcePosition>, message: impl Into<String>) -> ClickError {
        match at {
            Some(position) => ClickError::new(format!("{position}: {}", message.into()))
                .with_kind(ClickErrorKind::Syntax),
            None => ClickError::new(message).with_kind(ClickErrorKind::Syntax),
        }
    }

    fn error(&self, message: impl Into<String>) -> ClickError {
        self.error_at(self.here(), message)
    }
}

/// How a diagnostic names one `loop` clause. A loop has no signature, so its
/// own label is the only name it can carry at parse time.
fn loop_clause_description(label: Option<&str>) -> String {
    match label {
        Some(label) => format!("the loop `{label}`"),
        None => "the loop".to_string(),
    }
}

fn typed_load_type_from_name(name: Option<&str>) -> Option<CType> {
    match name {
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
        borrowed,
        condition,
    } = clause;
    match ensure {
        Ensure::Resource(resource) => expand_aggregate_resource_clause(resource)
            .into_iter()
            .map(|resource| EnsureClause {
                name: name.clone(),
                ensure: Ensure::Resource(resource),
                proof: proof.clone(),
                borrowed,
                condition: condition.clone(),
            })
            .collect(),
        ensure => vec![EnsureClause {
            name,
            ensure,
            proof,
            borrowed,
            condition,
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
        Token::Int64Number(value) | Token::UnsuffixedInt64(value)
            if *value == i32::MAX as i64 + 1 =>
        {
            Some(i32::MAX as u32 + 1)
        }
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
            pointee_constant: field.pointee_constant,
            source: Default::default(),
        }
    }
}

fn field_has_direct_memory_place(field: &ResolvedField) -> bool {
    if field.struct_name.is_some() || field.union_name.is_some() {
        return false;
    }
    matches!(
        field.c_type,
        C0Type::Int8
            | C0Type::Int16
            | C0Type::Int32
            | C0Type::Char
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64
            | C0Type::UInt64
            | C0Type::Int32Array(_)
            | C0Type::Int64Array(_)
            | C0Type::UInt64Array(_)
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
        C0Type::Int64Array(_) => Some((8, CType::Int64)),
        C0Type::UInt64Array(_) => Some((8, CType::UInt64)),
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
    let mut structural_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut quantifier_depth = 0usize;
    let mut proof_depth = 0usize;
    let mut pending_quantifier = false;
    let mut pending_proof_blocks = 0usize;
    let mut brace_kinds = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        match token {
            Token::Ident(name) if matches!(name.as_str(), "forall" | "exists") => {
                pending_quantifier = true;
            }
            Token::Ident(name)
                if name == "by" && matches!(tokens.get(index + 1), Some(Token::LBrace)) =>
            {
                pending_proof_blocks = pending_proof_blocks.saturating_add(1);
            }
            Token::LParen => {
                structural_depth += 1;
                openings.push(index);
                if openings.len() > PARENTHESIS_NESTING_LIMIT {
                    let message = format!(
                        "parenthesis nesting exceeds Click's supported depth of {PARENTHESIS_NESTING_LIMIT}"
                    );
                    return Err(match positions.get(index) {
                        Some(position) => ClickError::new(format!("{position}: {message}")),
                        None => ClickError::new(message),
                    }
                    .with_kind(ClickErrorKind::Syntax));
                }
                if structural_depth > DELIMITER_NESTING_LIMIT {
                    return Err(delimiter_nesting_error(index, positions));
                }
            }
            Token::LBracket => {
                structural_depth += 1;
                bracket_depth += 1;
                if bracket_depth >= STRUCTURAL_NESTING_LIMIT {
                    return Err(source_nesting_error(
                        index,
                        positions,
                        "bracket",
                        STRUCTURAL_NESTING_LIMIT,
                    ));
                }
                if structural_depth > DELIMITER_NESTING_LIMIT {
                    return Err(delimiter_nesting_error(index, positions));
                }
            }
            Token::LBrace => {
                structural_depth += 1;
                let quantifier = pending_quantifier;
                pending_quantifier = false;
                let parent_is_proof = brace_kinds
                    .last()
                    .is_some_and(|(_, parent_proof)| *parent_proof);
                let proof = pending_proof_blocks != 0 || parent_is_proof;
                pending_proof_blocks = pending_proof_blocks.saturating_sub(1);
                brace_kinds.push((quantifier, proof));
                if quantifier {
                    if quantifier_depth + 1 >= STRUCTURAL_NESTING_LIMIT {
                        return Err(source_nesting_error(
                            index,
                            positions,
                            "quantifier",
                            STRUCTURAL_NESTING_LIMIT,
                        ));
                    }
                    quantifier_depth += 1;
                }
                if proof {
                    if proof_depth + 1 >= STRUCTURAL_NESTING_LIMIT {
                        return Err(source_nesting_error(
                            index,
                            positions,
                            "proof",
                            STRUCTURAL_NESTING_LIMIT,
                        ));
                    }
                    proof_depth += 1;
                }
                if structural_depth > DELIMITER_NESTING_LIMIT {
                    return Err(delimiter_nesting_error(index, positions));
                }
            }
            Token::RParen => {
                structural_depth = structural_depth.saturating_sub(1);
                if let Some(open) = openings.pop() {
                    matching[open] = Some(index);
                    matching[index] = Some(open);
                }
            }
            Token::RBracket => {
                structural_depth = structural_depth.saturating_sub(1);
                bracket_depth = bracket_depth.saturating_sub(1);
            }
            Token::RBrace => {
                structural_depth = structural_depth.saturating_sub(1);
                if let Some((quantifier, proof)) = brace_kinds.pop() {
                    if quantifier {
                        quantifier_depth = quantifier_depth.saturating_sub(1);
                    }
                    if proof {
                        proof_depth = proof_depth.saturating_sub(1);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(matching)
}

fn delimiter_nesting_error(index: usize, positions: &[SourcePosition]) -> ClickError {
    source_nesting_error_message("delimiter", DELIMITER_NESTING_LIMIT, index, positions)
}

fn source_nesting_error(
    index: usize,
    positions: &[SourcePosition],
    kind: &str,
    limit: usize,
) -> ClickError {
    source_nesting_error_message(kind, limit, index, positions)
}

fn source_nesting_error_message(
    kind: &str,
    limit: usize,
    index: usize,
    positions: &[SourcePosition],
) -> ClickError {
    let message = format!("{kind} nesting exceeds Click's supported depth of {limit}");
    match positions.get(index) {
        Some(position) => ClickError::new(format!("{position}: {message}")),
        None => ClickError::new(message),
    }
    .with_kind(ClickErrorKind::Syntax)
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
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
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

#[cfg(test)]
mod integer_quantifier_parser_tests {
    use super::*;

    #[test]
    fn parses_integer_forall_and_restores_literal_context() {
        let mut parser =
            Parser::new("forall (z: Integer) { z + 100000000000000000000 > z }").unwrap();
        let proposition = parser.parse_proposition().unwrap();
        assert!(matches!(
            proposition,
            ClickProposition::ForAll {
                click_type: ClickType::Integer,
                ..
            }
        ));
        assert!(parser.current_integer_params.is_empty());
        assert!(!parser.integer_literal_context);
    }

    #[test]
    fn nested_c_binder_restores_integer_shadowing() {
        let mut parser =
            Parser::new("forall (z: Integer) { exists (z: int32) { z == 0 } }").unwrap();
        let proposition = parser.parse_proposition().unwrap();
        assert!(matches!(
            proposition,
            ClickProposition::ForAll {
                click_type: ClickType::Integer,
                ..
            }
        ));
        assert!(parser.current_integer_params.is_empty());
        assert!(parser.current_contract_bindings.is_empty());
    }

    #[test]
    fn c_shadow_preserves_wide_literal_provenance_for_validation() {
        let mut rejected =
            Parser::new("forall (z: Integer) { exists (z: int32) { z == 100000000000000000000 } }")
                .unwrap();
        // Literal provenance is retained through parsing.  The C-range
        // rejection belongs to semantic lowering, where the binder type is
        // available, rather than to the parser's context-sensitive grammar.
        assert!(rejected.parse_proposition().is_ok());

        let mut restored =
            Parser::new("forall (z: Integer) { exists (z: int32) { z == 0 } and z > 0 }").unwrap();
        assert!(restored.parse_proposition().is_ok());
    }

    #[test]
    fn function_integer_let_scope_is_available_then_restored() {
        let source = r#"
            int32 first(int32 x) {
                let saved: Integer = to_integer(x);
                ensures saved == saved;
            }
            int32 second(int32 saved) {
                ensures saved == saved;
            }
        "#;
        let file = Parser::new(source)
            .unwrap()
            .parse_file_items()
            .expect("adjacent function contracts should parse");
        let Ensure::Proposition(ClickProposition::Comparison { left, .. }) =
            file.function_blocks()[0].ensures()[0].ensure()
        else {
            panic!("expected the first function's proposition");
        };
        assert!(matches!(
            left,
            ContractExpression::Let { body, .. }
                if matches!(body.as_ref(), ContractExpression::Binding(name) if name == "saved")
        ));
        let Ensure::Proposition(ClickProposition::Comparison { left, .. }) =
            file.function_blocks()[1].ensures()[0].ensure()
        else {
            panic!("expected the second function's proposition");
        };
        assert!(matches!(
            left,
            ContractExpression::CFragment(CExpression::Variable(name)) if name == "saved"
        ));
    }

    #[test]
    fn snapshot_of_pure_call_can_continue_into_comparison() {
        let source = r#"
            function identity(x: int32) -> int32 { x }
            theorem snapshot_call(x: int32) {
                ensures x == x by {
                    have at(saved, identity(x)) == at(saved, 1) by { assumption(); }
                    assumption();
                }
            }
        "#;
        Parser::new(source)
            .unwrap()
            .parse_file_items()
            .expect("an expression snapshot must not parse as a proposition snapshot");
    }
}
