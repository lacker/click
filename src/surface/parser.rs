mod cpp_class_objects;
mod cpp_generic_templates;
mod cpp_model;
mod cpp_syntax;
mod name_table;
mod rust_generic_functions;
mod rust_generic_resources;
mod rust_generic_traits;
mod rust_literals;
use super::names;
mod rust_syntax;
mod rust_trait_objects;
pub(crate) use rust_trait_objects::implementation_interface_contract;
pub(super) mod tokenizer;
use cpp_model::rewrite_model_accessors;
use name_table::{NameKind, NameScope, NameTable, ShadowRestore};
use rust_syntax::rust_signature_hint;

use crate::languages::SourceLanguage;
use tokenizer::tokenize;

/// A written parser token and its exact source span. Source tools retain the
/// original spelling rather than reconstructing literals from their values.
#[derive(Clone, Debug)]
pub(in crate::surface) struct SourceToken {
    pub text: String,
    pub span: std::ops::Range<usize>,
    /// Where the token starts, as the parser numbers source positions.
    pub start: SourcePosition,
}

pub(in crate::surface) fn source_tokens(source: &str) -> Result<Vec<SourceToken>, ClickError> {
    source_tokens_in_container(source, None)
}

pub(in crate::surface) fn source_tokens_in_container(
    source: &str,
    container: Option<&crate::source::SourceContainer>,
) -> Result<Vec<SourceToken>, ClickError> {
    let (_, positions, spans) = tokenizer::tokenize_with_spans(source, container)
        .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
    Ok(spans
        .into_iter()
        .zip(positions)
        .map(|(span, start)| SourceToken {
            text: source[span.clone()].to_string(),
            span,
            start,
        })
        .collect())
}

/// Smart search may synthesize kernel values that diagnostics can print but
/// source cannot name. Check the rendered candidate without resolving names
/// or scanning any ambient declarations. Quoted text remains ordinary syntax.
pub(super) fn has_valid_source_tokens(source: &str) -> bool {
    crate::instrumentation::record_deterministic_work(source.len());
    !crate::instrumentation::deadline_exceeded() && tokenize(source, None).is_ok()
}

use super::*;
use claim_labels::{ClaimClauseKind, flattened_claim_ids};

/// Modules brought into scope by full library paths, before declaration
/// parsing. Expansion can replace a qualified resource with its bare name,
/// so it must preserve this part of the original file's library context.
pub(super) fn library_path_modules(source: &str) -> Result<BTreeSet<&'static str>, ClickError> {
    let (tokens, positions) = tokenizer::tokenize(source, None)?;
    names::resolve_library_paths(tokens, positions, None).map(|resolved| resolved.path_modules)
}

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

/// `guarded_by` associated a resource with a mutex field by declaration. A
/// mutex's protected resource now comes from its checked initialization, so
/// the spelling is refused with that direction.
const RETIRED_GUARDED_BY: &str = "`guarded_by` is retired: a mutex protects the resource its checked `pthread_mutex_init` step deposits, so remove the clause and pass the resource to that step";
/// `special` named the pointer, finite-float, definedness, and exact
/// Integer rule family of `arithmetic_certificate`; the family is now spelled
/// `rules`, and the old spelling is refused with that direction.
const RETIRED_SPECIAL_CERTIFICATE: &str =
    "`arithmetic_certificate special` is retired: write `arithmetic_certificate rules { ... }`";

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

/// [`parse_for_target`] under the default target, for tests.
#[cfg(test)]
pub(super) fn parse(source: &str) -> Result<ClickFile, ClickError> {
    parse_for_target(source, crate::languages::c::target::CTarget::SUPPORTED)
}

/// [`parse`] under a selected C target, which fixes plain `char`.
pub(super) fn parse_for_target(
    source: &str,
    target: crate::languages::c::target::CTarget,
) -> Result<ClickFile, ClickError> {
    let mut parser =
        Parser::new(source).map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
    parser.plain_char = Some(target.plain_char());
    parser.int64_t_rank = target.int64_t_rank();
    parser.parse_file()
}

/// Source-language metadata for one function: its execution identity and the
/// automatic-local layouts a sidecar cannot infer from its signature.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(in crate::surface) struct FunctionLocals {
    /// Exact C execution identity; absent when the source spelling is ambiguous.
    pub(in crate::surface) execution_name: Option<String>,
    /// The struct name of each local of struct-pointer type.
    pub(in crate::surface) struct_pointers: BTreeMap<String, String>,
    /// The locals of reference type, which a proof names by their referent
    /// as it names a reference parameter.
    pub(in crate::surface) references: BTreeSet<String>,
}

/// The program facts a sidecar is parsed against: its struct and union
/// layouts, and by function, the objects a contract may name and the locals
/// that are memory-backed.
#[derive(Clone, Default)]
pub(in crate::surface) struct ProgramLayouts {
    /// A C definition's execution name, indexed by translation unit and source spelling.
    pub(in crate::surface) qualified_functions: BTreeMap<(String, String), String>,
    pub(in crate::surface) c_object_names: BTreeMap<String, std::sync::Arc<BTreeSet<String>>>,
    /// The other members of each function's recursive C component, for the
    /// functions in a component of two or more. An expression `decreases`
    /// measure ranks calls to these functions too.
    pub(in crate::surface) recursion_peers: BTreeMap<String, Vec<String>>,
    pub(in crate::surface) struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    pub(in crate::surface) union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    /// Each function's address-backed aggregate objects, with their structs.
    pub(in crate::surface) aggregate_objects: BTreeMap<String, BTreeMap<String, String>>,
    /// Each function's aggregate objects that are arrays.
    pub(in crate::surface) aggregate_array_objects: BTreeMap<String, BTreeSet<String>>,
    /// The shapes of the arrays each function's contract may index.
    pub(in crate::surface) global_array_shapes:
        BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    /// By translation unit, the globals and function statics a contract may
    /// name, `name` or `function::name`.
    pub(in crate::surface) qualified_objects:
        BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>,
    /// Each function's locals of struct-pointer or reference type, by its
    /// source spelling.
    pub(in crate::surface) local_struct_pointers: BTreeMap<String, FunctionLocals>,
    /// The signedness the program's C target gives plain `char`. `None` for
    /// a program with no C target, where spelling plain `char` is refused.
    pub(in crate::surface) plain_char: Option<syntax::PlainChar>,
    /// The rank the program's C target gives `int64_t` and `uint64_t`;
    /// `None` reads them as `long`.
    pub(in crate::surface) int64_t_rank: Option<LongRank>,
    /// The language of a prepared program's import, which decides the
    /// sidecar's spelling where its `verifying` path does not: a C++ import
    /// may verify a `.h` header.
    pub(in crate::surface) language: Option<SourceLanguage>,
    /// The Click library modules the program's C declarations bring, such
    /// as `click::c::string` for a declared `memcpy`.
    pub(in crate::surface) library_modules: BTreeSet<&'static str>,
    /// Each closure's captured variables, by the closure's function name.
    /// A sidecar head names only the closure's own parameters; the captures
    /// lead its signature, so its contract reads them by name.
    pub(in crate::surface) closure_captures: BTreeMap<String, Vec<FunctionParameter>>,
    /// Each C++ override with the virtual method it overrides, by their
    /// sidecar names: the override inherits that method's interface.
    pub(in crate::surface) virtual_overrides: Vec<(String, String)>,
    /// Each dispatch a C++ importer names for a call through a reference to
    /// a class another derives from, with the virtual method it stands for,
    /// by their sidecar names: without a contract of its own, it has the
    /// method's.
    pub(in crate::surface) virtual_dispatches: Vec<(String, String)>,
    /// Each instance of a generic Rust function the import declares, with
    /// the generic function and the instance's parameter and result types:
    /// it has the generic function's contract at those types.
    pub(in crate::surface) rust_generic_instances: Vec<(String, String, Vec<C0Type>, C0Type)>,
    /// The instances of each generic crate trait the import declares an
    /// interface of, by the trait's importer name.
    pub(in crate::surface) rust_trait_instances: BTreeMap<String, BTreeSet<Vec<String>>>,
    /// The type of each crate enum a Rust import's signatures take or
    /// return, by its name: a sidecar signature names it as Rust does.
    pub(in crate::surface) rust_enum_types: BTreeMap<String, crate::kernel::TypeParameterName>,
    /// Each C++ function's calls of methods on a receiver that may be an
    /// object of a derived class, by sidecar names: the function called, and
    /// the reference parameter the receiver is, or `None` for `this`.
    pub(in crate::surface) receiver_calls: BTreeMap<String, Vec<(String, Option<String>)>>,
    /// The layout name of each C++ record a head spells otherwise, by that
    /// spelling: `Stored<long long>` is `Stored__long_long`.
    pub(in crate::surface) record_spellings: BTreeMap<String, String>,
    /// The typedef names of the verified C sources a function head may
    /// write, with their types.
    pub(in crate::surface) c_typedefs: BTreeMap<String, syntax::C0HeadTypedef>,
}

/// A braced proof block as the parser read it: the positions of its braces
/// and of the first token of each tactic in it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::surface) struct ProofBlockSpan {
    pub(in crate::surface) open: SourcePosition,
    pub(in crate::surface) close: SourcePosition,
    pub(in crate::surface) tactics: Vec<SourcePosition>,
}

/// A proof written as one tactic without braces, `by T(args);`, as the
/// parser read it: the positions of the tactic's first and last tokens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::surface) struct ImplicitProofSpan {
    pub(in crate::surface) first: SourcePosition,
    pub(in crate::surface) last: SourcePosition,
}

/// A proof clause as the parser read it: `by` and the proof after it, or the
/// `;` of a clause left to its default proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::surface) struct ProofClauseSpan {
    /// The `by`, or the default clause's `;`.
    pub(in crate::surface) start: SourcePosition,
    /// The clause's last token: the `}` or `;` that ends its proof, or the
    /// default clause's `;`.
    pub(in crate::surface) last: SourcePosition,
    /// The keyword the clause proves, where its reader named one: a loop's
    /// `initialize` or `preserve`.
    pub(in crate::surface) owner: Option<SourcePosition>,
}

/// Where the parser read a declaration's clauses: the brace that opens them,
/// and the first token of each written claim clause (`ensures`, `owns` or
/// `produces`, in source order). It records where the declaration was read,
/// not what it declares, so it never makes two declarations unequal.
#[derive(Clone, Debug, Default)]
pub struct DeclarationBody {
    pub(in crate::surface) open: Option<SourcePosition>,
    /// The brace that closes the clauses.
    pub(in crate::surface) close: Option<SourcePosition>,
    pub(in crate::surface) clauses: Vec<Option<SourcePosition>>,
    /// The `exceptional` token of each `exceptional ensures` clause.
    pub(in crate::surface) exceptional_clauses: Vec<Option<SourcePosition>>,
    /// The unbraced one-tactic proofs read inside the declaration.
    pub(in crate::surface) implicit_proofs: Vec<ImplicitProofSpan>,
    /// The proof clauses read inside the declaration and its grouped proof.
    pub(in crate::surface) proof_clauses: Vec<ProofClauseSpan>,
}

impl PartialEq for DeclarationBody {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for DeclarationBody {}

/// Where the parser read a file's proofs, in that file's own text. Like
/// [`DeclarationBody`], it records where the file was read, not what it
/// declares, so it never makes two files unequal.
#[derive(Clone, Debug, Default)]
pub(in crate::surface) struct SourceSpans {
    pub(in crate::surface) proof_blocks: Vec<ProofBlockSpan>,
    pub(in crate::surface) proof_clauses: Vec<ProofClauseSpan>,
    pub(in crate::surface) implicit_proofs: Vec<ImplicitProofSpan>,
}

impl PartialEq for SourceSpans {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for SourceSpans {}

/// Where the parser reads `source`'s proofs.
#[cfg(test)]
pub(in crate::surface) fn parsed_source_spans(
    source: &str,
    layouts: ProgramLayouts,
) -> Result<SourceSpans, ClickError> {
    let mut parser = Parser::with_program_layouts(source, layouts, None)?;
    parser.plain_char = Some(crate::languages::c::target::CTarget::SUPPORTED.plain_char());
    Ok(SourceSpans::clone(
        parser.parse_file_items()?.source_spans(),
    ))
}

pub(super) fn parse_with_layouts_and_aggregate_objects(
    source: &str,
    layouts: ProgramLayouts,
) -> Result<ClickFile, ClickError> {
    Parser::with_program_layouts(source, layouts, None)?.parse_file()
}

/// Whether a Click source declares only definitions for importers:
/// imports, specification types, predicates, pure functions, and resources,
/// with no `verifying` or `target` source, no `runtime`, no theorem, no
/// named contract, and no C function proof. Such a module has no claim of
/// its own to verify; it is checked where it is imported, in the importer's
/// C layouts. Anything this scan does not recognize (including a source that
/// does not tokenize) counts as an entry, so a module is never skipped by
/// mistake for a file that owns a proof.
pub(super) fn declares_only_definitions(source: &str) -> bool {
    let Ok((tokens, _)) = tokenizer::tokenize(source, None) else {
        return false;
    };
    let mut depth = 0_usize;
    let mut item_start = true;
    for token in &tokens {
        match token {
            Token::LBrace | Token::LParen | Token::LBracket => {
                item_start = false;
                depth += 1;
            }
            Token::RBrace | Token::RParen | Token::RBracket => {
                let Some(inner) = depth.checked_sub(1) else {
                    return false;
                };
                depth = inner;
                item_start = depth == 0 && *token == Token::RBrace;
            }
            Token::Semicolon if depth == 0 => item_start = true,
            Token::Ident(name) if depth == 0 && item_start => {
                if !matches!(
                    name.as_str(),
                    "import"
                        | "spec"
                        | "predicate"
                        | "function"
                        | "resource"
                        | "abstract"
                        | "authorized"
                ) {
                    return false;
                }
                item_start = false;
            }
            _ if depth == 0 && item_start => return false,
            _ => {}
        }
    }
    true
}

/// Parses file items under the default target, for tests.
#[cfg(test)]
pub(super) fn parse_file_items(source: &str) -> Result<ClickFile, ClickError> {
    let mut parser =
        Parser::new(source).map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
    parser.plain_char = Some(crate::languages::c::target::CTarget::SUPPORTED.plain_char());
    parser.parse_file_items()
}

pub(in crate::surface) enum ImportedCallee<'a> {
    Function(&'a FunctionBlock),
    Contract(&'a ContractDefinition),
}

pub(super) fn parse_file_items_for_module(
    source: &str,
    identity: &str,
    line_offset: usize,
    imported_algebraic_types: &[AlgebraicTypeDefinition],
    imported_callees: &[ImportedCallee<'_>],
    imported_resources: &[&ResourceDefinition],
    imported_declarations: &[(names::DeclarationKind, String)],
    imported_integer_functions: &BTreeSet<String>,
    layouts: ProgramLayouts,
) -> Result<ClickFile, ClickError> {
    let mut parser = Parser::with_program_layouts(
        source,
        layouts,
        Some(&crate::source::SourceContainer::new(identity, line_offset)),
    )?;
    parser.symbols.import_declarations(imported_declarations)?;
    let imported_tactics = parser
        .symbols
        .imported_names(names::DeclarationKind::Tactic)
        .map(str::to_string)
        .collect::<Vec<_>>();
    parser.tactic_names.extend(imported_tactics);
    // Under `arithmetic "integer";` an imported `-> Integer` result is an
    // exact Integer operand, as a local one is.
    parser
        .integer_function_names
        .extend(imported_integer_functions.iter().cloned());
    for callee in imported_callees {
        let (named_contract, block) = match callee {
            ImportedCallee::Function(block) => (false, *block),
            ImportedCallee::Contract(definition) => {
                parser.contract_proof_bindings.insert(
                    definition.name().to_string(),
                    definition.proof_parameters.clone().unwrap_or_default(),
                );
                (true, definition.function_block())
            }
        };
        parser.in_contract_definition = named_contract;
        if named_contract {
            parser
                .contract_resource_binders
                .entry(block.signature().name().to_string())
                .or_default();
        }
        let parameters = block
            .signature()
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<Vec<_>>();
        for requirement in block.requires() {
            if let Requirement::Resource(resource) = requirement {
                parser.record_callee_resource_binder(
                    block.signature().name(),
                    resource,
                    &parameters,
                    CalleeResourceBinderKind::Supplied,
                );
            }
        }
        for ensure in block.ensures() {
            if !ensure.borrowed()
                && let Ensure::Resource(resource) = ensure.ensure()
            {
                parser.record_callee_resource_binder(
                    block.signature().name(),
                    resource,
                    &parameters,
                    CalleeResourceBinderKind::Produced,
                );
            }
        }
    }
    parser.in_contract_definition = false;
    for definition in imported_resources {
        if let Some(body) = definition.composite_body() {
            parser
                .declared_resource_child_slots
                .insert(definition.name().to_string(), body.child_slot_resources());
        }
    }
    for definition in imported_algebraic_types {
        for variant in definition.variants() {
            parser.algebraic_variant_fields.insert(
                (definition.name().to_string(), variant.name().to_string()),
                variant.fields().to_vec(),
            );
        }
    }
    parser.parse_file_items()
}

/// Whether `name` is the leading word of a built-in tactic or proof form, which
/// a user-defined tactic may not shadow.
fn is_builtin_tactic_spelling(name: &str) -> bool {
    matches!(name, "let" | "by" | "sorry" | "auto")
        || crate::surface::PUBLIC_TACTIC_FORMS.iter().any(|form| {
            form.id != "user-tactic"
                && form
                    .syntax
                    .split(|character: char| !(character.is_alphanumeric() || character == '_'))
                    .next()
                    == Some(name)
        })
}

/// Turn the default `have P;` simplification into the same one-step script
/// as an explicit `have P by simp();`. Out of line to keep recursive frames small.
#[inline(never)]
fn have_proof_as_written_in_full(proof: SourceProof) -> SourceProof {
    if proof == SourceProof::Tactic(SmartTactic::Simp) {
        SourceProof::Script(vec![ProofTactic::Simp])
    } else {
        proof
    }
}

fn is_tactic_name(name: &str) -> bool {
    matches!(name, "auto" | "simp")
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Token {
    Ident(String),
    Number(u32),
    // Keep literal metadata shared so adding Rust forms does not enlarge
    // every token in C and C++ sidecars too.
    RustInteger(std::sync::Arc<rust_literals::IntegerLiteral>),
    BigNumber(String),
    UnsuffixedInt64(i64),
    UnsuffixedUInt64(u64),
    UInt8Number(u8),
    UInt32Number(u32),
    Int64Number(i64),
    Int64MinimumMagnitude,
    UInt64Number(u64),
    CharLiteral(u8),
    /// A Rust lifetime, `'a`, by its name without the quote.
    Lifetime(String),
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

/// Diagnostics print a token as [`Token::describe`] spells it, never as its
/// Debug form.
impl std::fmt::Display for Token {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.describe())
    }
}

impl Token {
    /// A human-readable rendering for diagnostics, such as `` identifier `x` ``
    /// or `` `;` ``.
    fn describe(&self) -> String {
        match self {
            Self::Ident(name) => format!("identifier `{name}`"),
            Self::Number(value) => format!("number `{value}`"),
            Self::RustInteger(literal) => literal.describe(),
            Self::BigNumber(value) => format!("number `{value}`"),
            Self::UnsuffixedInt64(value) => format!("number `{value}`"),
            Self::UnsuffixedUInt64(value) => format!("number `{value}`"),
            Self::UInt8Number(value) => format!("uint8 number `{value}u8`"),
            Self::UInt32Number(value) => format!("uint32 number `{value}u32`"),
            Self::Int64Number(value) => format!("int64 number `{value}i64`"),
            Self::Int64MinimumMagnitude => {
                "int64 minimum magnitude `9223372036854775808i64`".into()
            }
            Self::UInt64Number(value) => format!("uint64 number `{value}u64`"),
            Self::CharLiteral(value) => {
                format!("character literal `{}`", (*value as char).escape_default())
            }
            Self::Lifetime(name) => format!("lifetime `'{name}`"),
            Self::String(value) => format!("string literal `\"{value}\"`"),
            other => format!("`{}`", other.spelling()),
        }
    }

    fn spelling(&self) -> &'static str {
        match self {
            Self::Ident(_)
            | Self::Number(_)
            | Self::RustInteger(_)
            | Self::BigNumber(_)
            | Self::UnsuffixedInt64(_)
            | Self::UnsuffixedUInt64(_)
            | Self::UInt8Number(_)
            | Self::UInt32Number(_)
            | Self::Int64Number(_)
            | Self::Int64MinimumMagnitude
            | Self::UInt64Number(_)
            | Self::CharLiteral(_)
            | Self::Lifetime(_)
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
            Token::RustInteger(literal) => literal.digits.len(),
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

struct Parser {
    c_object_names_by_function: BTreeMap<String, std::sync::Arc<BTreeSet<String>>>,
    recursion_peers_by_function: BTreeMap<String, Vec<String>>,
    /// Click library modules the program's C declarations bring.
    implied_library_modules: BTreeSet<&'static str>,
    /// Whether this parser reads a Click library module, which never looks
    /// up the library's own declarations while the library is loading.
    library_module: bool,
    /// The theorems the file declares, which a citation by bare name names
    /// before any library theorem of that name. Empty in a library module.
    symbols: names::SymbolTable,
    source_aliases: BTreeMap<String, String>,
    qualified_functions: BTreeMap<(String, String), String>,
    qualified_objects: Option<BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>>,
    /// Set while a `tactic` declaration's signature is parsed: the name
    /// follows directly, the parameters use Click's `name: type` spelling,
    /// and the implicit result is `void`.
    pending_tactic_signature: bool,
    /// Every user-defined tactic declared so far in this file, so a proof
    /// can tell `name(args)` applying one from other syntax.
    tactic_names: BTreeSet<String>,
    contract_proof_bindings: BTreeMap<String, Vec<ResourceClause>>,
    next_resource_identity: u64,
    /// Instances introduced by `let { slot: name } = unfold(parent)`. The slot's
    /// resource is declared by the parent's matched arm, which may not be
    /// parsed yet, so the recorded family is the parent's and every family
    /// comparison against these instances is left to declaration expansion.
    child_slot_identities: BTreeSet<Variable>,
    in_resource_definition: bool,
    /// The fields of each resource declared so far, hidden ones included.
    declared_resource_fields: BTreeMap<String, Vec<ResourceFieldDefinition>>,
    /// The named child slots of each resource declared so far, across its
    /// unmatched body and every match arm, with the resource each owns when
    /// the arms agree ([`CompositeResourceBody::child_slot_resources`]). A
    /// `fold` may leave out a slot whose child is the in-scope resource of
    /// the same name.
    declared_resource_child_slots: BTreeMap<String, BTreeMap<String, Option<String>>>,
    /// The language of the `verifying` sources. Rust admits a Rust
    /// signature (`fn name(a: T) -> T`).
    language: SourceLanguage,
    /// The signedness the selected C target gives plain `char`, or `None`
    /// where no C target applies; plain `char` is then refused.
    plain_char: Option<syntax::PlainChar>,
    /// The rank a function head's `int64_t` and `uint64_t` have on the
    /// target. Only heads keep a rank: see `exact_long_rank`.
    int64_t_rank: LongRank,
    /// Set while a function head is parsed. A head restates a C
    /// declaration, so it keeps the C type exactly, `long` apart from
    /// `long long`; a specification type elsewhere names a representation.
    exact_long_rank: bool,
    /// The slice parameters of the Rust signature being parsed. Each is one
    /// name in the sidecar and a pointer with a `name_len` length underneath.
    rust_slice_params: BTreeSet<String>,
    /// The type of the `impl` block being parsed: its methods are the
    /// functions `Type_name`, and `self` is their receiver.
    rust_impl_type: Option<String>,
    /// The suffix a trait's type argument gives its methods' names, inside
    /// `impl Trait<Arg> for Type`: `MulAssign<u32>` names `Type_mul_assign_u32`.
    rust_impl_method_suffix: Option<String>,
    /// The module of the `impl` block being read, as the importer names
    /// it, when the block is an inherent one for a type named by a path.
    rust_impl_module: Option<String>,
    /// The crate trait the `impl` block being read implements, as the
    /// importer names it: its methods are `<Type as Trait>::name`.
    rust_impl_trait: Option<String>,
    /// The crate trait whose `trait` block is being read: its methods are
    /// the interfaces `Trait::name`, external declarations of the methods
    /// a call through the trait reaches.
    rust_trait_interface: Option<String>,
    /// The type parameters of the Rust signature being parsed that a crate
    /// trait bounds, `T` of `<T: traits::Shape>`: a reference to one is a
    /// reference to a value of a type the function does not know.
    rust_trait_type_parameters: BTreeSet<String>,
    /// The type parameters of the generic `trait` block being read, `T` of
    /// `trait p::Scale<T>`: a value of one is an abstract value.
    rust_abstract_type_parameters: BTreeSet<String>,
    /// The generic Rust function instances the import declares, as the
    /// layouts give them.
    rust_generic_instances: Vec<(String, String, Vec<C0Type>, C0Type)>,
    /// The index of each `fn` token of a generic function's instance the
    /// parser wrote out: only these may name an instance.
    rust_written_instances: BTreeSet<usize>,
    /// The methods of generic C++ class templates' instances, which the
    /// sidecar does not write: each is written out from its generic method.
    cpp_generic_instances: BTreeSet<String>,
    /// Each crate trait method implementation read, by name, with the
    /// interface it inherits.
    rust_trait_implementations: Vec<(String, String)>,
    cpp_dispatches: Vec<(String, String)>,
    cpp_receiver_calls: BTreeMap<String, Vec<(String, Option<String>)>>,
    /// The crate traits whose objects carry state, by importer name: the
    /// token rewrite already gave their implementations their interfaces.
    rust_object_traits: BTreeSet<String>,
    /// The importer names of the methods of C++ classes whose objects carry
    /// state: an override of one is stated on its own memory.
    cpp_object_methods: cpp_class_objects::ObjectMethods,
    /// See [`ProgramLayouts::record_spellings`].
    record_spellings: BTreeMap<String, String>,
    /// See [`ProgramLayouts::c_typedefs`].
    c_typedefs: BTreeMap<String, syntax::C0HeadTypedef>,
    match_nesting: usize,
    proposition_nesting: usize,
    proof_nesting: usize,
    contract_expression_nesting: usize,
    contract_if_nesting: usize,
    algebraic_type_nesting: usize,
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    /// Every braced proof block parsed so far, in parse order: the block's
    /// braces and the first token of each tactic it holds.
    proof_block_spans: Vec<ProofBlockSpan>,
    proof_clause_spans: Vec<ProofClauseSpan>,
    /// The owner the next proof clause records, taken as the clause starts.
    proof_clause_owner: Option<SourcePosition>,
    implicit_proof_spans: Vec<ImplicitProofSpan>,
    matching_parentheses: Vec<Option<usize>>,
    position: usize,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    /// See [`ProgramLayouts::rust_enum_types`].
    rust_enum_types: BTreeMap<String, crate::kernel::TypeParameterName>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
    /// The struct name of each automatic struct-pointer local of each C
    /// function, from the C parser. A contract's own parameters come from its
    /// signature; these are the body's locals, so a `have` or `fact` that
    /// names one has the same layout the parameter would have. A parameter of
    /// the same spelling wins: the contract is written against the signature.
    local_struct_pointers_by_function: BTreeMap<String, FunctionLocals>,
    current_reference_result: bool,
    /// The lexical names bound at the cursor that carry no further data:
    /// contract bindings, Integer parameters and lets, theorem parameters
    /// and proof binders (see [`NameKind`]).
    names: NameTable,
    /// The pure functions of this module that take a slice, indexed with
    /// their names: each one's written parameter count and the positions of
    /// its `name: &[T]` parameters. A call passes such a parameter a slice,
    /// which stands for its pointer and its length.
    pure_function_slices: BTreeMap<String, (usize, Vec<usize>)>,
    /// Pure functions declared `-> Integer`, whose calls are Integer operands
    /// for `arithmetic "integer";`.
    integer_function_names: BTreeSet<String>,
    /// The casts written as `address(p)`, which convert a C pointer to its
    /// `uint64` address. Under `arithmetic "integer";` arithmetic on them is
    /// pointer-word arithmetic, such as a tag added to an aligned address,
    /// and keeps its C meaning as a pointer operand does.
    address_casts: std::collections::HashSet<CExpression>,
    /// The slice parameters of the pure function whose parameter list is
    /// being parsed; `None` in any other parameter list, where a slice is
    /// not a parameter type.
    pending_slice_params: Option<Vec<String>>,
    /// Set immediately before an `if`, `match` or `let` expression that is
    /// the value of a `bool` context, and taken by that expression's parser:
    /// its branches are then `bool` values too.
    bool_value_context: bool,
    /// Declared field types of every `spec enum` variant in the file, keyed by
    /// datatype and variant name and indexed before any item is parsed. A
    /// resource's match arm types its constructor bindings from this index, so
    /// a struct-pointer binding is a memory base whether its datatype is
    /// declared above or below the resource: declaration order does not create
    /// scope.
    algebraic_variant_fields: BTreeMap<(String, String), Vec<AlgebraicFieldType>>,
    /// Whether specification comparisons with arithmetic are Integer
    /// comparisons (`arithmetic "integer";`).
    integer_arithmetic: bool,
    /// Quantifier variables open at the cursor, innermost last. Each hides
    /// a fact of the same name inside its body.
    quantifier_binders: Vec<String>,
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
    contract_resource_binders: BTreeMap<String, BTreeMap<String, CalleeResourceBinder>>,
    /// Set while a `contract` block's embedded function block is parsed: its
    /// signature names an interface, not a callable C function.
    in_contract_definition: bool,
    /// Each closure's captured variables, by the closure's function name.
    closure_captures: BTreeMap<String, Vec<FunctionParameter>>,
    /// The value parameters a named contract's body declares with
    /// `let name: type;`, in declaration order, while its block is parsed.
    contract_value_parameters: Vec<FunctionParameter>,
    /// Each named contract's value parameter names, in declaration order,
    /// for resolving `Name(f, { name: value })`.
    contract_value_parameter_names: BTreeMap<String, Vec<String>>,
    in_function_block: bool,
}

/// One `owns`, `consumes`, or `produces` instance binder of a C function
/// block, recorded so a caller's `step(callee(...), { ... })` can bind it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CalleeResourceBinder {
    identity: Variable,
    // None denotes a supplied resource assertion parameter. Its concrete
    // family is checked by the instantiated runtime contract in the kernel.
    family: Option<String>,
    /// The named resource clause as written by the callee. A call output needs
    /// this richer target, not just the family used for binder transport, so
    /// later `unfold(name)` can recover the resource body and its arguments.
    resource: Option<ResourceClause>,
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
    /// A runtime binder that names a resource type, not an instance:
    /// `atomic_init`'s `payload`.
    Type,
    /// A value binder, `views s: R(a, _);`: the caller may name the instance
    /// it selects with a resource term or one of its own value binders, or
    /// leave it to the call.
    Value,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
    struct_pointer: bool,
    constant: bool,
    pointee_constant: bool,
    /// Written `T&`: `c_type` is the pointer that carries the reference.
    reference: bool,
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
            | "int128"
            | "uint128"
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
            | C0Type::CharArray(_, _)
            | C0Type::UInt8Array(_)
            | C0Type::UInt16Array(_)
            | C0Type::UInt32Array(_)
            | C0Type::Int128Array(_)
            | C0Type::Int64Array(_, _)
            | C0Type::UInt128Array(_)
            | C0Type::UInt64Array(_, _)
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
    reference_params: BTreeSet<String>,
    declared_loadable_bytes: Vec<(String, u32)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedFunctionSignature {
    signature: FunctionSignature,
    struct_params: BTreeMap<String, String>,
    struct_array_params: BTreeSet<String>,
    reference_params: BTreeSet<String>,
    return_struct_name: Option<String>,
}

/// Give a concrete replacement for scalar and slice signatures. Record and
/// method contracts need an `impl` and the imported type identity instead.
impl Parser {
    fn verifies_rust(&self) -> bool {
        self.language == SourceLanguage::Rust
    }
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
            ClickType::Parameter(_)
            | ClickType::C(_)
            | ClickType::CObjectPointer { .. }
            | ClickType::Integer => None,
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
    /// `let name: type;` in a named contract: a value parameter, bound where
    /// the contract is attached to a function.
    Parameter,
}

impl ContractLetBinding {
    /// `let name = value;`, as a value binder's parameter names its argument.
    pub(in crate::surface) fn value_binding(name: String, value: ContractExpression) -> Self {
        Self {
            name,
            click_type: None,
            kind: ContractLetBindingKind::Value(value),
        }
    }

    pub(super) fn value(&self) -> Option<&ContractExpression> {
        match &self.kind {
            ContractLetBindingKind::Value(value) => Some(value),
            ContractLetBindingKind::Where(_) | ContractLetBindingKind::Parameter => None,
        }
    }

    pub(super) fn where_condition(&self) -> Option<&ClickProposition> {
        match &self.kind {
            ContractLetBindingKind::Value(_) | ContractLetBindingKind::Parameter => None,
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
            None,
            &BTreeMap::new(),
        )
    }

    /// A parser for `source` against a program's layouts and objects.
    fn with_program_layouts(
        source: &str,
        layouts: ProgramLayouts,
        container: Option<&crate::source::SourceContainer>,
    ) -> Result<Self, ClickError> {
        let mut parser = Self::new_with_layouts_and_aggregate_objects(
            source,
            layouts.struct_layouts,
            layouts.union_layouts,
            layouts.aggregate_objects,
            layouts.aggregate_array_objects,
            layouts.global_array_shapes,
            container,
            &layouts.rust_trait_instances,
        )
        .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
        parser.c_object_names_by_function = layouts.c_object_names;
        parser.rust_enum_types = layouts.rust_enum_types;
        parser.recursion_peers_by_function = layouts.recursion_peers;
        parser
            .implied_library_modules
            .extend(layouts.library_modules);
        parser.qualified_objects = Some(layouts.qualified_objects);
        parser.qualified_functions = layouts.qualified_functions;
        parser.local_struct_pointers_by_function = layouts.local_struct_pointers;
        parser.closure_captures = layouts.closure_captures;
        parser.rust_generic_instances = layouts.rust_generic_instances;
        // A generic function's instances are written out at their types.
        let mut function_instances = BTreeMap::<String, BTreeSet<Vec<String>>>::new();
        let mut impl_instances = BTreeMap::<String, BTreeSet<Vec<String>>>::new();
        for (instance, generic, _, _) in &parser.rust_generic_instances {
            if let Some(arguments) =
                crate::languages::rust::names::instance_type_arguments(instance, generic)
            {
                function_instances
                    .entry(generic.clone())
                    .or_default()
                    .insert(arguments);
            } else if let Some((record, arguments)) =
                crate::languages::rust::names::impl_instance_arguments(instance, generic)
            {
                impl_instances.entry(record).or_default().insert(arguments);
            }
        }
        // An instance is only ever written out: one the sidecar writes is
        // refused, whatever the import declares.
        if parser.language == SourceLanguage::Rust {
            // A crate function named as a value, `Doubling(crate_name::f)`, is
            // its address, as C writes `&f`.
            let (tokens, positions) = rust_syntax::rewrite_function_values(
                std::mem::take(&mut parser.tokens),
                std::mem::take(&mut parser.positions),
                &parser.local_struct_pointers_by_function,
            );
            parser.tokens = tokens;
            parser.positions = positions;
            let (tokens, positions, written) = rust_generic_functions::expand_generic_functions(
                std::mem::take(&mut parser.tokens),
                std::mem::take(&mut parser.positions),
                &function_instances,
                &impl_instances,
            )?;
            // A generic resource is written out at each type argument list
            // its uses name, the written function instances' included.
            let (tokens, positions, written) = rust_generic_resources::expand_generic_resources(
                tokens,
                positions,
                written,
                rust_generic_resources::rust_concrete,
            )?;
            parser.matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
            parser.tokens = tokens;
            parser.positions = positions;
            parser.rust_written_instances = written;
        }
        parser.plain_char = layouts.plain_char;
        parser.int64_t_rank = layouts.int64_t_rank.unwrap_or(LongRank::Long);
        parser.c_typedefs = layouts.c_typedefs;
        if layouts.language == Some(SourceLanguage::Cpp) {
            // A sidecar verifying a C++ header is C++ by its import, which
            // its `verifying` path does not say: its class object state is
            // rewritten here.
            if parser.language != SourceLanguage::Cpp {
                let (tokens, positions) = cpp_syntax::rewrite_function_references(
                    std::mem::take(&mut parser.tokens),
                    std::mem::take(&mut parser.positions),
                );
                let (tokens, positions, methods) =
                    cpp_class_objects::rewrite_class_objects(tokens, positions)?;
                parser.matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
                parser.tokens = tokens;
                parser.positions = positions;
                parser.cpp_object_methods = methods;
            }
            parser.language = SourceLanguage::Cpp;
            // A generic class template's method is written out at each of
            // its instances the import declares.
            let mut method_instances = BTreeMap::<String, BTreeSet<Vec<String>>>::new();
            for (instance, generic, _, _) in &parser.rust_generic_instances {
                let arguments =
                    cpp_generic_templates::instance_arguments(instance).ok_or_else(|| {
                        ClickError::new(format!(
                            "the C++ generic instance `{instance}` names no class template instance"
                        ))
                    })?;
                method_instances
                    .entry(generic.clone())
                    .or_default()
                    .insert(arguments);
                parser.cpp_generic_instances.insert(instance.clone());
            }
            let (tokens, positions, written) = cpp_generic_templates::expand_generic_methods(
                std::mem::take(&mut parser.tokens),
                std::mem::take(&mut parser.positions),
                &method_instances,
            )?;
            // A generic resource is written out at each type argument list
            // its uses name, the written method instances' included.
            let (tokens, positions, written) = rust_generic_resources::expand_generic_resources(
                tokens,
                positions,
                written,
                rust_generic_resources::cpp_concrete,
            )?;
            parser.matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
            parser.tokens = tokens;
            parser.positions = positions;
            parser.rust_written_instances = written;
            parser.rust_trait_implementations = layouts.virtual_overrides;
            parser.cpp_dispatches = layouts.virtual_dispatches;
            parser.cpp_receiver_calls = layouts.receiver_calls;
            parser.record_spellings = layouts.record_spellings;
        }
        Ok(parser)
    }

    fn new_with_layouts_and_aggregate_objects(
        source: &str,
        struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
        union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
        aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
        aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
        global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
        container: Option<&crate::source::SourceContainer>,
        rust_trait_instances: &BTreeMap<String, BTreeSet<Vec<String>>>,
    ) -> Result<Self, ClickError> {
        let (tokens, positions) = tokenize(source, container)?;
        let (tokens, positions) = rewrite_model_accessors(tokens, positions, &struct_layouts);
        let names::ResolvedLibraryTokens {
            tokens,
            positions,
            path_modules: path_library_modules,
            symbols,
        } = names::resolve_library_paths(
            tokens,
            positions,
            container.map(|container| &*container.filename),
        )?;
        // A cited theorem the file does not declare is a library theorem,
        // named by its qualified identity. A library module cites every
        // library theorem that way, its own included.
        let library_module =
            container.is_some_and(|container| container.filename.starts_with("library/"));
        // `arithmetic "integer";` decides how every specification comparison
        // in the file reads, wherever the directive appears.
        let integer_arithmetic = tokens.windows(2).any(|pair| {
            matches!(pair, [Token::Ident(keyword), Token::String(value)]
                if keyword == "arithmetic" && value == "integer")
        });
        // Source clauses may follow declarations. Choose the spelling for the
        // whole file so moving the clause cannot bypass a Rust syntax check.
        let language =
            SourceLanguage::of_sources(tokens.windows(2).filter_map(|pair| match pair {
                [Token::Ident(keyword), Token::String(path)] if keyword == "verifying" => {
                    Some(path.as_str())
                }
                _ => None,
            }));
        let mut tokens = tokens;
        if language == SourceLanguage::Rust {
            rust_literals::normalize_tokens(&mut tokens);
        } else if let Some(index) = tokens
            .iter()
            .position(|token| matches!(token, Token::RustInteger(_)))
        {
            return Err(ClickError::new(format!(
                "{}: Rust integer literal syntax requires a Rust sidecar",
                positions[index]
            )));
        }
        // A Rust sidecar's trait object state is rewritten into contracts
        // over abstract resources before anything is parsed.
        // Its generic crate traits are written out at each instance first.
        let (tokens, positions, rust_object_traits) = if language == SourceLanguage::Rust {
            let (tokens, positions) = rust_generic_traits::expand_generic_traits(
                tokens,
                positions,
                rust_trait_instances,
            )?;
            rust_trait_objects::rewrite_trait_objects(tokens, positions)?
        } else {
            (tokens, positions, BTreeSet::new())
        };
        // So is a C++ sidecar's class object state.
        let (tokens, positions, cpp_object_methods) = if language == SourceLanguage::Cpp {
            let (tokens, positions) = cpp_syntax::rewrite_function_references(tokens, positions);
            cpp_class_objects::rewrite_class_objects(tokens, positions)?
        } else {
            (
                tokens,
                positions,
                cpp_class_objects::ObjectMethods::default(),
            )
        };
        let matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
        Ok(Self {
            rust_object_traits,
            cpp_object_methods,
            record_spellings: BTreeMap::new(),
            c_typedefs: BTreeMap::new(),
            source_aliases: BTreeMap::new(),
            qualified_functions: BTreeMap::new(),
            qualified_objects: None,
            pending_tactic_signature: false,
            tactic_names: BTreeSet::new(),
            contract_proof_bindings: BTreeMap::new(),
            next_resource_identity: 0,
            child_slot_identities: BTreeSet::new(),
            in_resource_definition: false,
            declared_resource_fields: BTreeMap::new(),
            declared_resource_child_slots: BTreeMap::new(),
            language,
            plain_char: None,
            int64_t_rank: LongRank::Long,
            exact_long_rank: false,
            rust_slice_params: BTreeSet::new(),
            rust_impl_type: None,
            rust_impl_method_suffix: None,
            rust_impl_module: None,
            rust_impl_trait: None,
            rust_trait_interface: None,
            rust_trait_type_parameters: BTreeSet::new(),
            rust_abstract_type_parameters: BTreeSet::new(),
            rust_generic_instances: Vec::new(),
            rust_written_instances: BTreeSet::new(),
            cpp_generic_instances: BTreeSet::new(),
            rust_trait_implementations: Vec::new(),
            cpp_dispatches: Vec::new(),
            cpp_receiver_calls: BTreeMap::new(),
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
            rust_enum_types: BTreeMap::new(),
            union_layouts,
            c_object_names_by_function: BTreeMap::new(),
            recursion_peers_by_function: BTreeMap::new(),
            implied_library_modules: path_library_modules,
            library_module,
            symbols,
            aggregate_objects_by_function,
            aggregate_array_objects_by_function,
            global_array_shapes_by_function,
            local_struct_pointers_by_function: BTreeMap::new(),
            current_reference_result: false,
            names: NameTable::default(),
            pure_function_slices: BTreeMap::new(),
            integer_function_names: BTreeSet::new(),
            address_casts: std::collections::HashSet::new(),
            pending_slice_params: None,
            bool_value_context: false,
            algebraic_variant_fields: BTreeMap::new(),
            integer_arithmetic,
            quantifier_binders: Vec::new(),
            callee_resource_binders: BTreeMap::new(),
            contract_resource_binders: BTreeMap::new(),
            in_contract_definition: false,
            contract_value_parameters: Vec::new(),
            closure_captures: BTreeMap::new(),
            contract_value_parameter_names: BTreeMap::new(),
            in_function_block: false,
            integer_literal_context: false,
            proof_block_spans: Vec::new(),
            proof_clause_spans: Vec::new(),
            proof_clause_owner: None,
            implicit_proof_spans: Vec::new(),
        })
    }

    fn parse_file(mut self) -> Result<ClickFile, ClickError> {
        let file = self.parse_file_items()?;
        let mut file = super::validation::expand_declared_resource_clauses_for_project(file)
            .map_err(|error| {
                error
                    .with_kind(ClickErrorKind::Type)
                    .located_by_ambient_declaration()
            })?;
        super::validation::validate_click_definitions(&file).map_err(|error| {
            error
                .with_kind(ClickErrorKind::Type)
                .located_by_ambient_declaration()
        })?;
        super::lowering::check_resource_field_schemas(&mut file).map_err(|error| {
            error
                .with_kind(ClickErrorKind::Type)
                .located_by_ambient_declaration()
        })?;
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
        crate::instrumentation::record_deterministic_work(self.tokens.len());
        let declarations = names::top_level_declarations(&self.tokens);
        self.symbols.declare_file(&declarations);
        for declaration in declarations {
            match declaration.kind {
                names::DeclarationKind::Enum
                    if declaration.at >= 2
                        && matches!(&self.tokens[declaration.at - 2], Token::Ident(spec) if spec == "spec") =>
                {
                    // A datatype that does not parse is left to the item
                    // loop, which reports it in source order.
                    self.position = declaration.at - 2;
                    if let Ok(definition) = self.parse_algebraic_type_definition() {
                        for variant in definition.variants() {
                            self.algebraic_variant_fields
                                .entry((definition.name().to_string(), variant.name().to_string()))
                                .or_insert_with(|| variant.fields().to_vec());
                        }
                    }
                }
                names::DeclarationKind::Function => {
                    let name = declaration.name;
                    // A generic function's parameters follow its type
                    // parameters, `length<T>(xs: List<T>)`.
                    let mut parameters = declaration.at + 1;
                    if self.tokens.get(parameters) == Some(&Token::LessThan)
                        && let Some(close) = self.tokens[parameters..]
                            .iter()
                            .position(|token| *token == Token::GreaterThan)
                    {
                        parameters += close + 1;
                    }
                    if self.declares_integer_result(parameters) {
                        self.integer_function_names.insert(name.clone());
                    }
                    if let Some(slices) = self.written_slice_parameters(parameters) {
                        self.pure_function_slices.insert(name, slices);
                    }
                }
                _ => {}
            }
        }
        for index in shift_rights {
            self.tokens[index] = Token::ShiftRight;
        }
        self.position = resume;
    }

    /// The written parameter count and the slice parameter positions of the
    /// pure function whose parameter list opens at or after `start`, when
    /// it takes a slice. Reads tokens only.
    fn written_slice_parameters(&self, start: usize) -> Option<(usize, Vec<usize>)> {
        let open = start
            + self.tokens[start..]
                .iter()
                .position(|token| *token == Token::LParen)?;
        let mut depth = 0usize;
        let mut count = 0;
        let mut slices = Vec::new();
        let mut parameter_start = true;
        for index in open + 1..self.tokens.len() {
            let token = &self.tokens[index];
            if depth == 0 && parameter_start && *token != Token::RParen {
                count += 1;
                // `name: &[T]` or `name: &mut [T]`, not `&[T; N]`.
                let mut at = index + 2;
                if self.tokens.get(index + 1) == Some(&Token::Colon)
                    && self.tokens.get(at) == Some(&Token::Amp)
                {
                    at += 1;
                    if self.tokens.get(at) == Some(&Token::Ident("mut".into())) {
                        at += 1;
                    }
                    if self.tokens.get(at) == Some(&Token::LBracket)
                        && self.tokens.get(at + 2) == Some(&Token::RBracket)
                    {
                        slices.push(count - 1);
                    }
                }
            }
            parameter_start = false;
            match token {
                Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
                Token::RParen if depth == 0 => break,
                Token::RParen | Token::RBracket | Token::GreaterThan => {
                    depth = depth.saturating_sub(1)
                }
                Token::Comma if depth == 0 => parameter_start = true,
                _ => {}
            }
        }
        (!slices.is_empty()).then_some((count, slices))
    }

    /// The arguments of a call to a pure function that takes a slice, with
    /// each slice argument written as the pointer and the length it stands
    /// for. A call that already writes them, as printed proofs do, is left
    /// as it is.
    fn spread_slice_arguments(
        &self,
        name: &str,
        arguments: Vec<ContractExpression>,
    ) -> Result<Vec<ContractExpression>, ClickError> {
        let Some((count, slices)) = self.pure_function_slices.get(name) else {
            return Ok(arguments);
        };
        if arguments.len() != *count {
            return Ok(arguments);
        }
        let mut spread = Vec::with_capacity(count + slices.len());
        for (index, argument) in arguments.into_iter().enumerate() {
            if !slices.contains(&index) {
                spread.push(argument);
                continue;
            }
            let ContractExpression::CFragment(CExpression::Variable(slice)) = &argument else {
                return Err(self.error(format!(
                    "argument {} of `{name}` is a slice; pass a slice parameter, such as `bytes`, or its pointer and length",
                    index + 1
                )));
            };
            if !self.rust_slice_params.contains(slice) {
                return Err(self.error(format!(
                    "argument {} of `{name}` is a slice, but `{slice}` is not a slice parameter; pass one, or a pointer and a length",
                    index + 1
                )));
            }
            let length =
                ContractExpression::CFragment(CExpression::Variable(format!("{slice}_len")));
            spread.push(argument);
            spread.push(length);
        }
        Ok(spread)
    }

    fn parse_file_items(&mut self) -> Result<ClickFile, ClickError> {
        self.index_algebraic_variant_fields();
        let mut imports = Vec::new();
        let mut verifying_sources = Vec::new();
        let mut c_target_name = None;
        let mut c_mode = None;
        let mut integer_arithmetic = false;
        let mut thread_runtime = None;
        let mut algebraic_type_definitions = Vec::new();
        let mut predicate_definitions = Vec::new();
        let mut click_function_definitions = Vec::new();
        let mut resource_definitions = Vec::new();
        let mut theorem_definitions = Vec::new();
        let mut deferred_theorems = Vec::new();
        let mut contract_definitions = Vec::new();
        let mut function_blocks = Vec::new();
        let mut tactic_definitions = Vec::new();
        let mut library_imports = self
            .implied_library_modules
            .iter()
            .map(|identity| (*identity).to_string())
            .collect::<Vec<_>>();

        while self.peek().is_some() {
            // An instance name ended in an earlier declaration's proof is
            // no name here at all.
            self.names.ended_instance_names.clear();
            if self.peek_ident() == Some("import")
                && matches!(self.peek_next(), Some(Token::Ident(_)))
            {
                let import = self.parse_library_import()?;
                if !library_imports.contains(&import) {
                    library_imports.push(import);
                }
            } else if self.peek_ident() == Some("import") {
                imports.push(self.parse_import()?);
            } else if self.peek_ident() == Some("verifying") {
                verifying_sources.push(self.parse_verifying_source()?);
            } else if let Some(directive @ ("target" | "mode")) =
                self.peek_ident().map(str::to_owned).as_deref()
                && matches!(self.peek_next(), Some(Token::String(_)))
            {
                let slot = if directive == "target" {
                    &mut c_target_name
                } else {
                    &mut c_mode
                };
                if slot.is_some() {
                    return Err(
                        self.error(format!("a Click file declares more than one `{directive}`"))
                    );
                }
                *slot = Some(self.parse_c_target_directive(directive)?);
            } else if self.peek_ident() == Some("arithmetic")
                && matches!(self.peek_next(), Some(Token::String(_)))
            {
                self.expect_ident_spelling("arithmetic")?;
                let at = self.error_context();
                let name = self.expect_string("specification arithmetic")?;
                self.expect(Token::Semicolon)?;
                if name != "integer" {
                    return Err(self.error_at(
                        at,
                        format!("unknown specification arithmetic `{name}`; the accepted value is `integer`"),
                    ));
                }
                if integer_arithmetic {
                    return Err(self.error("a Click file declares `arithmetic` more than once"));
                }
                integer_arithmetic = true;
            } else if self.peek_ident() == Some("runtime")
                && matches!(self.peek_next(), Some(Token::String(_)))
            {
                let runtime = self.parse_thread_runtime()?;
                if thread_runtime.is_some() {
                    return Err(self.error("a Click file declares more than one `runtime`"));
                }
                self.record_runtime_resource_binders(runtime);
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
            } else if self.peek_ident() == Some("tactic")
                && matches!(self.peek_next(), Some(Token::Ident(_)))
            {
                tactic_definitions.push(self.parse_tactic_definition()?);
            } else if self.peek_ident() == Some("authorized")
                && matches!(self.peek_next(), Some(Token::Ident(next)) if next == "resource" || next == "abstract")
            {
                self.position += 1;
                let is_abstract = self.peek_ident() == Some("abstract");
                let mut definition = self.parse_resource_definition(is_abstract)?;
                definition.authorized = true;
                resource_definitions.push(definition);
            } else if self.peek_ident() == Some("abstract") {
                resource_definitions.push(self.parse_resource_definition(true)?);
            } else if self.peek_ident() == Some("resource") {
                resource_definitions.push(self.parse_resource_definition(false)?);
            } else if self.peek_ident() == Some("extern") {
                function_blocks.push(self.parse_function_block(true)?);
            } else if self.verifies_cpp() && self.peek_ident() == Some("template") {
                function_blocks.push(self.parse_cpp_template_method()?);
            } else if self.verifies_rust() && self.peek_ident() == Some("impl") {
                self.parse_rust_impl_block(&mut function_blocks)?;
            } else if self.verifies_rust() && self.peek_ident() == Some("trait") {
                self.parse_rust_trait_block(&mut function_blocks)?;
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
        // A crate trait method's implementation, or a C++ override, inherits
        // its interface, which the sidecar may declare before or after it: a
        // trait's method, external or a default method with its proof, or the
        // virtual method overridden, whose contract a call through it assumes.
        let cpp = self.language == SourceLanguage::Cpp;
        for (implementation, interface) in std::mem::take(&mut self.rust_trait_implementations) {
            // An override of a method of a class whose object carries state, or
            // of a defining class's method, is stated on its own memory, by its
            // class's definitions.
            if cpp
                && (self.cpp_object_methods.interfaces.contains(&interface)
                    || self.cpp_object_methods.on_memory.contains(&interface))
            {
                // A defining class's override the sidecar does not state has
                // no contract, which verification refuses.
                let class = crate::languages::cpp::names::cpp_display_name(&implementation)
                    .and_then(|path| Some(path.rsplit_once("::")?.0.to_string()));
                if !self.cpp_object_methods.on_memory.contains(&implementation)
                    && !class.is_some_and(|class| self.cpp_object_methods.defining.contains(&class))
                {
                    let overridden = if self.cpp_object_methods.on_memory.contains(&interface) {
                        "a method of a class that defines its object's state"
                    } else {
                        "whose class's object carries state"
                    };
                    return Err(ClickError::new(format!(
                        "`{implementation}` overrides `{interface}`, {overridden}: its class \
                         defines that state on its own memory, `class Derived : Base {{ \
                         function f(this) -> T {{ ... }} }}`"
                    ))
                    .at_declaration(&implementation));
                }
                continue;
            }
            let Some(interface) = function_blocks
                .iter()
                .find(|block| block.signature().name() == interface)
                .cloned()
            else {
                continue;
            };
            if let Some(block) = function_blocks
                .iter_mut()
                .find(|block| !block.is_external() && block.signature().name() == implementation)
            {
                let source = if cpp {
                    "the method it overrides"
                } else {
                    "the trait's interface"
                };
                block
                    .inherit_interface(&interface, source)
                    .map_err(|message| {
                        let what = if cpp {
                            "the interface of the virtual method it overrides"
                        } else {
                            "its trait's interface"
                        };
                        ClickError::new(format!(
                            "`{}` cannot inherit {what}: {message}",
                            crate::languages::display_source_names(&implementation)
                        ))
                        .at_declaration(&implementation)
                    })?;
            }
        }
        // A generic function's instance the sidecar does not state has the
        // generic function's contract at its types.
        for (instance, generic, parameter_types, return_type) in
            std::mem::take(&mut self.rust_generic_instances)
        {
            if function_blocks
                .iter()
                .any(|block| block.signature().name() == instance)
            {
                continue;
            }
            let Some(block) = function_blocks
                .iter()
                .find(|block| !block.is_external() && block.signature().name() == generic)
            else {
                continue;
            };
            let alias = block
                .generic_instance_alias(&instance, &parameter_types, return_type)
                .map_err(|message| ClickError::new(message).at_declaration(&generic))?;
            function_blocks.push(alias);
        }
        // A dispatch the sidecar does not state has the contract of the
        // method it stands for.
        for (dispatch, method) in std::mem::take(&mut self.cpp_dispatches) {
            if function_blocks
                .iter()
                .any(|block| block.signature().name() == dispatch)
            {
                continue;
            }
            if let Some(block) = function_blocks
                .iter()
                .find(|block| block.signature().name() == method)
            {
                let alias = block.dispatch_alias(&dispatch);
                function_blocks.push(alias);
            }
        }
        // A method of a class another derives from holds its memory, and a
        // reference to it holds the object class's object: a call that needs
        // the other is refused here, naming what each holds.
        let methods = &self.cpp_object_methods;
        for (caller, calls) in &self.cpp_receiver_calls {
            let caller_class = crate::languages::cpp::names::cpp_display_name(caller)
                .and_then(|path| Some(path.rsplit_once("::")?.0.to_string()));
            for (callee, holder) in calls {
                let message = match holder {
                    None => {
                        let (Some((class, method)), Some((_, (root, derived)))) = (
                            methods.dispatches.get(callee),
                            caller_class
                                .as_ref()
                                .and_then(|class| methods.derived_from.get_key_value(class)),
                        ) else {
                            continue;
                        };
                        format!(
                            "`{caller}` calls `{class}::{method}` through `this`, which may be \
                             an object of a class deriving from its class, such as `{derived}`: \
                             the call runs whichever override the object's class selects, which \
                             needs `{root}`'s object, and `{caller}`, stated on its class's \
                             memory, does not hold that object; a qualified call, \
                             `this->{class}::{method}(...)`, runs `{class}::{method}` itself"
                        )
                    }
                    Some(parameter) => {
                        let Some(class) = methods
                            .object_parameters
                            .get(caller)
                            .and_then(|parameters| parameters.get(parameter))
                        else {
                            continue;
                        };
                        if !methods.on_memory.contains(callee) {
                            continue;
                        }
                        let (root, derived) = &methods.derived_from[class];
                        format!(
                            "`{caller}` calls `{callee}` on `{parameter}`, a reference to \
                             `{class}`, which may be an object of a class deriving from it, such \
                             as `{derived}`: `{parameter}` holds `{root}`'s object, not \
                             `{class}`'s memory, on which `{callee}` is stated"
                        )
                    }
                };
                return Err(ClickError::new(
                    crate::languages::display_source_names(&message).into_owned(),
                )
                .at_declaration(&crate::languages::display_source_names(caller)));
            }
        }
        let end = self.position;
        for position in deferred_theorems {
            self.position = position;
            theorem_definitions.push(self.parse_theorem_definition()?);
        }
        self.position = end;
        let mut c_function_names = self
            .local_struct_pointers_by_function
            .iter()
            .filter_map(|(source, info)| {
                info.execution_name
                    .as_ref()
                    .map(|target| (source.clone(), target.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        for block in &function_blocks {
            let signature = block.signature();
            if let Some(source) = &signature.c_source {
                let (_, name) = signature
                    .name()
                    .rsplit_once("::")
                    .expect("qualified C head");
                if let Some(target) = self
                    .qualified_functions
                    .get(&(source.clone(), name.to_string()))
                {
                    c_function_names.insert(signature.name().to_string(), target.clone());
                }
            }
        }
        let c_target = self.resolve_c_target(c_target_name, c_mode)?;
        let file = ClickFile {
            c_function_names: std::sync::Arc::new(c_function_names),
            imports,
            library_imports,
            verifying_sources,
            c_target,
            thread_runtime: thread_runtime.unwrap_or_default(),
            integer_arithmetic,
            algebraic_type_definitions,
            predicate_definitions,
            click_function_definitions,
            resource_definitions,
            theorem_definitions,
            contract_definitions,
            function_blocks,
            tactic_definitions,
            declaration_owners: BTreeMap::new(),
            entry_module: None,
            source_spans: std::sync::Arc::new(SourceSpans {
                proof_blocks: std::mem::take(&mut self.proof_block_spans),
                proof_clauses: std::mem::take(&mut self.proof_clause_spans),
                implicit_proofs: std::mem::take(&mut self.implicit_proof_spans),
            }),
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

    /// `import click::a::b;`: the Click library module `library/a/b.click`.
    fn parse_library_import(&mut self) -> Result<String, ClickError> {
        self.expect_ident_spelling("import")?;
        let at = self.error_context();
        let mut segments = vec![self.expect_ident("a Click library module path")?];
        let mut selected = Vec::new();
        while self.peek() == Some(&Token::ColonColon) {
            self.expect(Token::ColonColon)?;
            // `click::list::{append, length}` selects names of the module.
            if self.peek() == Some(&Token::LBrace) {
                self.expect(Token::LBrace)?;
                loop {
                    selected.push(self.expect_ident("a declaration name to import")?);
                    if self.peek() == Some(&Token::Comma) {
                        self.expect(Token::Comma)?;
                        continue;
                    }
                    break;
                }
                self.expect(Token::RBrace)?;
                break;
            }
            segments.push(self.expect_ident("a Click library module name")?);
        }
        self.expect(Token::Semicolon)?;
        let spelling = segments.join("::");
        if segments.len() < 2 || segments[0] != "click" {
            return Err(self.error_at(
                at,
                format!(
                    "`import {spelling};` names no Click library module; library modules are \
                     written `click::name`, and a project file is imported by a quoted path"
                ),
            ));
        }
        let identity = format!("library/{}.click", segments[1..].join("/"));
        if super::CLICK_LIBRARY_MODULES
            .iter()
            .all(|(module, _)| *module != identity)
        {
            let available = super::CLICK_LIBRARY_MODULES
                .iter()
                .map(|(module, _)| super::library_module_path(module))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(self.error_at(
                at,
                format!("unknown Click library module `{spelling}`; the library has {available}"),
            ));
        }
        for name in &selected {
            if !names::module_declares(&identity, name) {
                return Err(self.error_at(
                    at.clone(),
                    format!("Click library module `{spelling}` declares no `{name}` to import"),
                ));
            }
        }
        Ok(identity)
    }

    /// `tactic name(p: type, ...) { clauses } by { proof }`.
    ///
    /// The clauses are a function contract's, parsed by the function-block
    /// parser so binders, `old`, and `decreases` mean what they mean there.
    /// A tactic runs no code, so it has no result, no exceptional outcome,
    /// and may not diverge; it must be proved by its own `by` block.
    fn parse_tactic_definition(&mut self) -> Result<TacticDefinition, ClickError> {
        self.expect_ident_spelling("tactic")?;
        let start = self.error_context();
        if is_builtin_tactic_spelling(self.peek_ident().unwrap_or_default()) {
            return Err(self.error(format!(
                "tactic `{}` would shadow the built-in tactic of the same name",
                self.peek_ident().unwrap_or_default()
            )));
        }
        // A tactic's own name is applicable inside its body: a recursive
        // application is the induction hypothesis, ranked by its `decreases`.
        // Only earlier tactics and itself are applicable, so tactics cannot
        // be mutually recursive.
        let declared_name = self.peek_ident().unwrap_or_default().to_string();
        if !self.tactic_names.insert(declared_name.clone()) {
            return Err(self.error_at(
                start.clone(),
                format!("tactic `{declared_name}` is declared twice"),
            ));
        }
        self.pending_tactic_signature = true;
        let function_block = self.parse_function_block(false);
        self.pending_tactic_signature = false;
        let function_block = function_block?;
        let name = function_block.signature().name().to_string();
        let refuse = |parser: &Self, message: &str| {
            Err(parser.error_at(start.clone(), format!("tactic `{name}`: {message}")))
        };
        if function_block.signature().diverges() {
            return refuse(
                self,
                "a tactic may not declare `diverges`; a tactic that need not terminate could prove anything",
            );
        }
        if function_block.grouped_proof().is_none() {
            return refuse(self, "a tactic must be proved by a `by { ... }` block");
        }
        if !function_block.constructs().is_empty()
            || !function_block.exceptional_ensures().is_empty()
        {
            return refuse(
                self,
                "a tactic runs no code, so it has no `constructs` or `exceptional ensures` clauses",
            );
        }
        if function_block
            .ensures()
            .iter()
            .any(|clause| !matches!(clause.proof(), SourceProof::Default))
        {
            return refuse(
                self,
                "an `ensures` of a tactic is proved by the tactic's `by` block, not by its own",
            );
        }
        Ok(TacticDefinition::new(function_block))
    }

    fn parse_contract_definition(&mut self) -> Result<ContractDefinition, ClickError> {
        self.expect_ident_spelling("contract")?;
        // The retired form put proof parameters before the C signature:
        // `contract Read(cell: marked_cell(p)) for int32(int32* p)`. A name
        // followed directly by `(` can only be that form, since a C head
        // starts with its return type.
        if let Some(name) = self.peek_ident()
            && self.peek_next() == Some(&Token::LParen)
        {
            return Err(self.error(format!(
                "`contract {name}(...) for ...` is retired; write the C declaration and \
                 declare each resource handle in the body, as in \
                 `contract int32 {name}(int32* p) {{ owns cell: marked_cell(p); ... }}`"
            )));
        }
        let previous_in_contract = std::mem::replace(&mut self.in_contract_definition, true);
        self.contract_value_parameters.clear();
        let function_block = self.parse_function_block(false);
        self.in_contract_definition = previous_in_contract;
        let function_block = function_block?;
        let value_parameters = std::mem::take(&mut self.contract_value_parameters)
            .into_iter()
            .map(|parameter| parameter.name)
            .collect::<Vec<_>>();
        self.contract_value_parameter_names.insert(
            function_block.signature().name().to_string(),
            value_parameters.clone(),
        );
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
        self.contract_resource_binders
            .entry(function_block.signature().name().to_string())
            .or_default();
        // A named `owns` or `consumes` clause declares one of the contract's
        // resource handles. In declaration order they are the contract's
        // proof parameters, which an application binds by name. Named produced
        // slots also need typed identities in an execution-certificate proof;
        // call output patterns introduce their actual returned instances.
        let proof_parameters = function_block
            .requires()
            .iter()
            .filter_map(|requirement| match requirement {
                Requirement::Resource(parameter @ ResourceClause::Named { .. }) => {
                    Some(parameter.clone())
                }
                _ => None,
            })
            .chain(
                function_block
                    .ensures()
                    .iter()
                    .filter_map(|clause| match clause.ensure() {
                        Ensure::Resource(parameter @ ResourceClause::Named { .. })
                            if !clause.borrowed() =>
                        {
                            Some(parameter.clone())
                        }
                        _ => None,
                    }),
            )
            .collect::<Vec<_>>();
        let bindings = proof_parameters.clone();
        self.contract_proof_bindings
            .insert(function_block.signature().name().to_string(), bindings);
        Ok(ContractDefinition {
            proof_parameters: (!proof_parameters.is_empty()).then_some(proof_parameters),
            value_parameters,
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
        let rust_type = if self
            .peek_ident()
            .is_some_and(|name| type_parameters.iter().any(|parameter| parameter == name))
        {
            None
        } else {
            self.parse_rust_click_type()?
        };
        let name = match &rust_type {
            Some(_) => String::new(),
            None => self
                .peek_ident()
                .ok_or_else(|| self.error("expected algebraic variant field type"))?
                .to_string(),
        };
        if rust_type.is_none() && type_parameters.iter().any(|parameter| parameter == &name) {
            self.position += 1;
            return Ok(AlgebraicFieldType::Parameter(name));
        }
        if rust_type.is_some() || is_c_type_keyword(&name) {
            let parsed = match rust_type {
                Some(parsed) => parsed,
                None => self.parse_type()?,
            };
            if !algebraic_field_c_type_supported(parsed.c_type) {
                return Err(self.error(
                    "algebraic datatype fields must be C scalar, data-pointer, or algebraic values",
                ));
            }
            // Only a declared `struct tag*` records a tag: a bare
            // `struct tag` is not a pointer to a laid-out object and a
            // `struct tag**` does not point at one either, so neither is a
            // memory base in a match arm.
            let object_class = self.declared_object_class(&parsed);
            let struct_name = if parsed.struct_pointer && parsed.c_type == C0Type::Int32Pointer {
                parsed.struct_name
            } else {
                None
            };
            return Ok(AlgebraicFieldType::C {
                c_type: parsed.c_type,
                struct_name,
                object_class,
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
        if SourceLanguage::of_source_path(&source_path) == SourceLanguage::Rust {
            self.language = SourceLanguage::Rust;
        }
        Ok(source_path)
    }

    /// Parses `target "x86_64-unknown-linux-gnu";` or
    /// `mode "kernel";`, which together select the C implementation
    /// target this file's C sources are preprocessed and verified under. The
    /// pair resolves through `CTarget::from_parts` once the file is parsed,
    /// as the pre-parse scan in `expansion` resolves it, so the two never
    /// drift apart.
    fn parse_c_target_directive(
        &mut self,
        directive: &str,
    ) -> Result<(String, Option<SourcePosition>), ClickError> {
        self.expect_ident_spelling(directive)?;
        let at = self.error_context();
        let name = self.expect_string(if directive == "target" {
            "C target name"
        } else {
            "C mode name"
        })?;
        self.expect(Token::Semicolon)?;
        Ok((name, at))
    }

    /// Resolves the file's `target` and `mode` directives, each with
    /// where it was written, so a refused name points at its own directive.
    fn resolve_c_target(
        &self,
        target: Option<(String, Option<SourcePosition>)>,
        mode: Option<(String, Option<SourcePosition>)>,
    ) -> Result<Option<crate::languages::c::target::CTarget>, ClickError> {
        use crate::languages::c::target::CTarget;
        if target.is_none() && mode.is_none() {
            return Ok(None);
        }
        if let Some((name, at)) = &target {
            CTarget::from_parts(Some(name), None)
                .map_err(|error| self.error_at(at.clone(), error))?;
        }
        CTarget::from_parts(
            target.as_ref().map(|(name, _)| name.as_str()),
            mode.as_ref().map(|(name, _)| name.as_str()),
        )
        .map(Some)
        .map_err(|error| self.error_at(mode.and_then(|(_, at)| at), error))
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
        if let Some(written) = self
            .here()
            .and_then(|position| self.symbols.written_path(&position))
        {
            return written
                .split_once("::")
                .is_some_and(|(alias, _)| self.source_aliases.contains_key(alias));
        }
        self.peek_next() == Some(&Token::ColonColon)
            && self
                .peek_ident()
                .is_some_and(|name| self.source_aliases.contains_key(name))
    }

    fn parse_qualified_c_name(&mut self) -> Result<(String, CExpression), ClickError> {
        let written = self.expect_c_declaration_ident("C source alias")?;
        let (alias, mut name) = match written.split_once("::") {
            Some((alias, name)) => (alias.to_string(), name.to_string()),
            None => {
                self.expect(Token::ColonColon)?;
                (written, self.expect_ident("C declaration name")?)
            }
        };
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
        let expression = self
            .parse_ensure_primary()?
            .to_kernel_specification_expression();
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
            .names
            .global_array_shapes
            .get(name)
            .and_then(|array| array.element_type.pointer_to())
        {
            Some(target_type) => CExpression::Cast {
                expression: Box::new(expression.clone()),
                target_type,
                integer_mode: crate::kernel::CIntegerCastMode::Standard,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
            None => expression.clone(),
        }
    }

    fn parse_predicate_definition(&mut self) -> Result<PredicateDefinition, ClickError> {
        self.expect_ident_spelling("predicate")?;
        let name = self.expect_ident("predicate name")?;
        let type_parameters = self.parse_click_type_parameters()?;
        let previous_type_parameters = self.names.replace(
            NameKind::TypeParameter,
            type_parameters.iter().cloned().collect(),
        );
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;
        let previous_struct_params = std::mem::replace(
            &mut self.names.struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = self.names.replace(
            NameKind::StructArrayParameter,
            parsed_parameters.struct_array_params,
        );
        let previous_reference_params = self.names.replace(
            NameKind::ReferenceParameter,
            parsed_parameters.reference_params,
        );
        let previous_algebraic_params = std::mem::replace(
            &mut self.names.algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let body = self.parse_proposition()?;
        self.names.struct_params = previous_struct_params;
        self.names
            .replace(NameKind::StructArrayParameter, previous_struct_array_params);
        self.names
            .replace(NameKind::ReferenceParameter, previous_reference_params);
        self.names.algebraic_params = previous_algebraic_params;
        self.names
            .replace(NameKind::TypeParameter, previous_type_parameters);
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
        let previous_type_parameters = self.names.replace(
            NameKind::TypeParameter,
            type_parameters.iter().cloned().collect(),
        );
        self.expect(Token::LParen)?;
        self.pending_slice_params = Some(Vec::new());
        let parsed_parameters = self.parse_click_parameters();
        let slice_params = self.pending_slice_params.take().unwrap_or_default();
        let parsed_parameters = parsed_parameters?;
        self.expect(Token::RParen)?;
        // A slice parameter reads as one: `bytes.len()` and `*bytes`.
        let previous_slice_params = std::mem::replace(
            &mut self.rust_slice_params,
            slice_params.into_iter().collect(),
        );
        self.expect(Token::Arrow)?;
        let (return_type, parsed_c_return_type) = self.parse_click_type()?;
        let return_object_class = parsed_c_return_type
            .as_ref()
            .and_then(|parsed| self.declared_object_class(parsed));
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
            &mut self.names.struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = self.names.replace(
            NameKind::StructArrayParameter,
            parsed_parameters.struct_array_params,
        );
        let previous_reference_params = self.names.replace(
            NameKind::ReferenceParameter,
            parsed_parameters.reference_params,
        );
        let previous_algebraic_params = std::mem::replace(
            &mut self.names.algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let body = self.parse_branch_value(return_type == ClickType::C(C0Type::Bool))?;
        self.names.struct_params = previous_struct_params;
        self.names
            .replace(NameKind::StructArrayParameter, previous_struct_array_params);
        self.names
            .replace(NameKind::ReferenceParameter, previous_reference_params);
        self.names.algebraic_params = previous_algebraic_params;
        self.names
            .replace(NameKind::TypeParameter, previous_type_parameters);
        self.rust_slice_params = previous_slice_params;
        self.expect(Token::RBrace)?;
        Ok(ClickFunctionDefinition {
            name,
            type_parameters,
            parameters: parsed_parameters.parameters,
            return_type,
            return_object_class,
            decreases,
            body,
        })
    }

    fn parse_resource_definition(
        &mut self,
        is_abstract: bool,
    ) -> Result<ResourceDefinition, ClickError> {
        // A generic resource's instance binds its abstract arguments, which
        // its parameters and body read as abstract types.
        let previous_abstract = self.rust_abstract_type_parameters.clone();
        let definition = self.parse_resource_definition_binding(is_abstract);
        self.rust_abstract_type_parameters = previous_abstract;
        definition
    }

    fn parse_resource_definition_binding(
        &mut self,
        is_abstract: bool,
    ) -> Result<ResourceDefinition, ClickError> {
        if is_abstract {
            self.expect_ident_spelling("abstract")?;
        }
        self.expect_ident_spelling("resource")?;
        let name = self.expect_ident("resource name")?;
        if self.verifies_rust()
            && self.peek() == Some(&Token::LessThan)
            && !self.parse_rust_generic_parameters()?.is_empty()
        {
            return Err(self.error("a resource's type parameters are abstract types"));
        }
        // A C++ generic resource's instance at abstract arguments binds them,
        // `resource nodes_A1_T<T>(...)`.
        if self.verifies_cpp() && self.peek() == Some(&Token::LessThan) {
            self.position += 1;
            loop {
                let parameter = self.expect_ident("resource type parameter")?;
                self.rust_abstract_type_parameters.insert(parameter);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::GreaterThan)?;
        }
        self.expect(Token::LParen)?;
        // The definition's instances and hidden fields are its own: they are
        // bound in a scope that ends with it, over tables it starts empty.
        let definition_scope = self.names.scope();
        let previous_resource_bindings = std::mem::take(&mut self.names.resource_bindings);
        let previous_resource_targets = std::mem::take(&mut self.names.resource_targets);
        let (parsed_parameters, resource_parameters) = self.parse_resource_parameters()?;
        self.expect(Token::RParen)?;
        for parameter in &resource_parameters {
            let ResourceClause::Named { binding, .. } = parameter else {
                unreachable!()
            };
            if parsed_parameters
                .parameters
                .iter()
                .any(|ordinary| ordinary.name() == binding.name)
            {
                return Err(self.error(format!("duplicate resource parameter `{}`", binding.name)));
            }
        }
        let previous_struct_params = std::mem::replace(
            &mut self.names.struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = self.names.replace(
            NameKind::StructArrayParameter,
            parsed_parameters.struct_array_params,
        );
        let previous_reference_params = self.names.replace(
            NameKind::ReferenceParameter,
            parsed_parameters.reference_params,
        );
        let previous_algebraic_params = std::mem::replace(
            &mut self.names.algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let previous_contract_bindings = self.names.take(NameKind::ContractBinding);
        let previous_definition = std::mem::replace(&mut self.in_resource_definition, true);
        let previous_hidden = std::mem::take(&mut self.names.hidden_child_fields);
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
            // An abstract resource may declare fields, and nothing else: its
            // instances carry them, but it has no body to fold or unfold.
            Some(Token::LBrace) => {
                let body = self.parse_composite_resource_body(&name)?;
                if body.fields.is_empty()
                    || !body.children.is_empty()
                    || body.matched.is_some()
                    || body.condition.is_some()
                    || !body.contains.is_empty()
                    || !body.facts.is_empty()
                    || !body.witnesses.is_empty()
                {
                    return Err(self.error(
                        "an `abstract resource` body declares only fields: it has no clauses of its own",
                    ));
                }
                Some(body)
            }
            Some(token) => {
                return Err(self.error(format!("expected resource body, got {token}")));
            }
            None => {
                return Err(self.error("expected resource body, got end of input"));
            }
        };
        self.in_resource_definition = previous_definition;
        self.names.end_declaration(definition_scope);
        self.names.hidden_child_fields = previous_hidden;
        if let Some(body) = &composite_body {
            self.declared_resource_fields
                .insert(name.clone(), body.fields.clone());
            self.declared_resource_child_slots
                .insert(name.clone(), body.child_slot_resources());
        }
        self.names.struct_params = previous_struct_params;
        self.names
            .replace(NameKind::StructArrayParameter, previous_struct_array_params);
        self.names
            .replace(NameKind::ReferenceParameter, previous_reference_params);
        self.names.algebraic_params = previous_algebraic_params;
        self.names.resource_bindings = previous_resource_bindings;
        self.names.resource_targets = previous_resource_targets;
        self.names
            .replace(NameKind::ContractBinding, previous_contract_bindings);
        Ok(ResourceDefinition {
            name,
            parameters: parsed_parameters.parameters,
            resource_parameters,
            sealed: is_abstract && composite_body.is_some(),
            composite_body,
            field_schema: None,
            authorized: false,
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
            // The binding shadows any enclosing name for the arm, so an outer
            // struct parameter must not keep lending it a layout.
            self.names
                .set_scoped_struct_param(binding, field.struct_pointer_name().map(str::to_string));
            self.names.arm_binding_types.insert(binding.clone(), field);
        }
    }

    /// The hidden parent field that holds `owner.field`, as an expression.
    /// Out of line: the caller is the recursive postfix parser, whose frame
    /// every temporary enlarges.
    #[inline(never)]
    fn hidden_child_field(&self, owner: &str, field: &str) -> Option<ContractExpression> {
        if self.names.hidden_child_fields.is_empty() {
            return None;
        }
        self.names
            .hidden_child_fields
            .get(&(owner.to_string(), field.to_string()))
            .cloned()
            .map(ContractExpression::ResourceField)
    }

    /// `fact child.field == parent_field;` is the equation that says where a
    /// named child's field is kept. Once it is written, a later `child.field`
    /// in the body reads that parent field, so the body may state further
    /// facts about it, as a resource with a hidden record may.
    #[inline(never)]
    fn note_child_field_equation(&mut self, fact: &ClickProposition) {
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = fact
        else {
            return;
        };
        let (ContractExpression::ResourceField(one), ContractExpression::ResourceField(other)) =
            (left, right)
        else {
            return;
        };
        let is_parent = |access: &ResourceFieldAccess| {
            access.owner == "__body" && access.identity == Variable(u64::MAX)
        };
        let (child, parent) = match (is_parent(one), is_parent(other)) {
            (false, true) => (one, other),
            (true, false) => (other, one),
            _ => return,
        };
        if !child.children.is_empty() {
            return;
        }
        let key = (child.owner.clone(), child.field.clone());
        if !self.names.hidden_child_fields.contains_key(&key) {
            self.names.bind_hidden_child_field(key, parent.clone());
        }
    }

    /// Gives a resource that declares no fields one hidden field per field of
    /// the child it names, with the equation that ties the two. A later
    /// `child.field` in the body reads the hidden field, so the body may
    /// state any number of facts about it. The child's fields then survive a
    /// fold of the parent exactly as a declared field's value does.
    #[inline(never)]
    fn hold_child_fields_in_a_hidden_record(
        &mut self,
        resource_name: &str,
        clause: &ResourceClause,
        fields: &mut Vec<ResourceFieldDefinition>,
        facts: &mut Vec<ClickProposition>,
    ) -> Result<(), ClickError> {
        let ResourceClause::Named { binding, resource } = clause else {
            return Ok(());
        };
        let ResourceClause::Declared { name: child, .. } = resource.as_ref() else {
            return Ok(());
        };
        let Some(child_fields) = self.declared_resource_fields.get(child).cloned() else {
            return Err(self.error(format!(
                "resource `{child}` must be declared before `{resource_name}` names it as the child `{}`",
                binding.name
            )));
        };
        for child_field in child_fields {
            let hidden_name = format!("{}.{}", binding.name, child_field.name);
            let hidden = ResourceFieldAccess {
                owner: "__body".into(),
                resource_name: resource_name.into(),
                identity: Variable(u64::MAX),
                children: vec![],
                field: hidden_name.clone(),
                field_index: fields.len(),
                click_type: Some(child_field.click_type.clone()),
            };
            fields.push(ResourceFieldDefinition {
                name: hidden_name,
                click_type: child_field.click_type.clone(),
            });
            facts.push(ClickProposition::Comparison {
                left: ContractExpression::ResourceField(ResourceFieldAccess {
                    owner: binding.name.clone(),
                    resource_name: child.clone(),
                    identity: binding.identity,
                    children: vec![],
                    field: child_field.name.clone(),
                    field_index: 0,
                    click_type: None,
                }),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ResourceField(hidden.clone()),
            });
            self.names
                .bind_hidden_child_field((binding.name.clone(), child_field.name), hidden);
        }
        Ok(())
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
        let previous_resource_fields = self.names.resource_fields.clone();
        if !fields.is_empty() {
            self.names.resource_fields = fields
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
        if self.peek_ident() == Some("guarded_by") {
            return Err(self.error(RETIRED_GUARDED_BY));
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
                let scope = self.names.scope();
                for name in &bindings {
                    self.names.set_scoped(NameKind::ContractBinding, name, true);
                }
                self.match_nesting += 1;
                let saved_arm_binding_types = std::mem::take(&mut self.names.arm_binding_types);
                self.bind_arm_binding_types(&type_name, &variant, &bindings);
                let body = self.parse_composite_resource_body(resource_name);
                self.names.arm_binding_types = saved_arm_binding_types;
                self.names.end(scope);
                self.match_nesting -= 1;
                let body = body?;
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
            self.names.resource_fields = previous_resource_fields;
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
        // A resource that declares no fields keeps a named child's fields in
        // a record of its own that the author does not write.
        let hidden_record = fields.is_empty() && self.match_nesting == 0;
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("guarded_by") => return Err(self.error(RETIRED_GUARDED_BY)),
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
                    if witnesses.iter().any(|witness| witness.name() == binding.name) {
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
                    return Err(self.error(
                        "a child resource is owned like any other resource; write `owns inner(p);`, not `contains inner(p);`",
                    ));
                }
                Some("owns") => {
                    self.position += 1;
                    let clause = self.parse_owned_resource_binding()?;
                    if hidden_record {
                        self.hold_child_fields_in_a_hidden_record(
                            resource_name,
                            &clause,
                            &mut fields,
                            &mut facts,
                        )?;
                    }
                    contains.push(clause);
                    self.expect(Token::Semicolon)?;
                }
                Some("views") => {
                    self.position += 1;
                    contains.push(self.parse_resource_target(ResourceAccessMode::View)?);
                    self.expect(Token::Semicolon)?;
                }
                Some("fact") => {
                    self.position += 1;
                    // Nothing names a resource's fact: a fold that cannot
                    // establish one prints the fact itself.
                    if matches!(self.peek(), Some(Token::Ident(_)))
                        && self.peek_next() == Some(&Token::Colon)
                    {
                        return Err(self.error(
                            "a `fact` clause takes no label; a failed fold names the fact by its proposition",
                        ));
                    }
                    let fact = self.parse_proposition()?;
                    self.note_child_field_equation(&fact);
                    facts.push(fact);
                    self.expect(Token::Semicolon)?;
                }
                Some("forall") => {
                    contains.push(self.parse_iterated_resource_clause(resource_name)?);
                }
                Some(name) => {
                    return Err(self.error(format!(
                        "expected `owns`, `views`, `fact`, `forall`, or `let` in resource body, got `{name}`"
                    )));
                }
                None => {
                    return Err(self.error(
                        "expected `owns`, `views`, `fact`, `forall`, or `let` in resource body, got end of input",
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
        self.names.resource_fields = previous_resource_fields;
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
        let integer_was_bound = self.names.remove(NameKind::IntegerParameter, &binder);
        let integer_let_was_bound = self.names.remove(NameKind::IntegerLet, &binder);
        let c_was_bound = self.names.remove(NameKind::ContractBinding, &binder);
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
            self.names
                .insert(NameKind::IntegerParameter, binder.clone());
        }
        if integer_let_was_bound {
            self.names.insert(NameKind::IntegerLet, binder.clone());
        }
        if c_was_bound {
            self.names.insert(NameKind::ContractBinding, binder.clone());
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

    fn parse_click_parameters(&mut self) -> Result<ParsedParameters, ClickError> {
        self.parse_parameters_with_resources(false)
            .map(|(parameters, _)| parameters)
    }

    fn parse_resource_parameters(
        &mut self,
    ) -> Result<(ParsedParameters, Vec<ResourceClause>), ClickError> {
        self.parse_parameters_with_resources(true)
    }

    fn parse_parameters_with_resources(
        &mut self,
        allow_resources: bool,
    ) -> Result<(ParsedParameters, Vec<ResourceClause>), ClickError> {
        let mut resource_parameters = Vec::new();
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        let mut struct_array_params = BTreeSet::new();
        let mut reference_params = BTreeSet::new();
        let mut declared_loadable_bytes = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok((
                ParsedParameters {
                    parameters,
                    struct_params,
                    struct_array_params,
                    reference_params,
                    declared_loadable_bytes,
                },
                resource_parameters,
            ));
        }

        loop {
            let resource_parameter = allow_resources
                && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(name)) if !is_c_type_keyword(name))
                && self.tokens.get(self.position + 3) == Some(&Token::LParen);
            if resource_parameter {
                let parameter = self.parse_owned_resource_binding()?;
                if !matches!(parameter, ResourceClause::Named { .. }) {
                    return Err(self.error("resource parameters use `name: resource(...)`"));
                }
                resource_parameters.push(parameter);
            } else {
                if !resource_parameters.is_empty() {
                    return Err(self.error("ordinary parameters must precede resource parameters"));
                }
                let name = self.expect_ident("Click parameter name")?;
                self.refuse_bool_literal_binder(&name)?;
                if is_c_type_keyword(&name) {
                    return Err(self.error(
                        "Click-native binders use `name: type`, for example `value: int32`",
                    ));
                }
                self.expect(Token::Colon)?;
                if self.pending_slice_params.is_some()
                    && self.verifies_rust()
                    && let Some(element) = self.parse_rust_slice_type()?
                {
                    // `bytes: &[T]` is a pointer and a `bytes_len` length, as
                    // in a `fn` signature.
                    let length = format!("{name}_len");
                    if let Some(slices) = &mut self.pending_slice_params {
                        slices.push(name.clone());
                    }
                    parameters.push(self.parse_parameter_array_suffix(name, element)?.parameter);
                    parameters.push(FunctionParameter {
                        click_type: ClickType::C(C0Type::UInt64(LongRank::Long)),
                        name: length,
                        struct_name: None,
                        function_pointer_signature: None,
                        constant: false,
                        pointee_constant: false,
                        reference: false,
                    });
                } else {
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
                                    reference: false,
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
                                reference: false,
                            },
                            struct_name: None,
                            declared_bytes: None,
                            struct_array: false,
                        }
                    };
                    if let Some(struct_name) = parsed_parameter.struct_name {
                        if parsed_parameter.parameter.click_type
                            == ClickType::C(C0Type::Int32PointerPointer)
                        {
                            struct_params.insert(
                                struct_pointer_pointer_key(&parsed_parameter.parameter.name),
                                struct_name.clone(),
                            );
                        }
                        struct_params.insert(parsed_parameter.parameter.name.clone(), struct_name);
                    }
                    if parsed_parameter.struct_array {
                        struct_array_params.insert(parsed_parameter.parameter.name.clone());
                    }
                    if parsed_parameter.parameter.is_reference() {
                        reference_params.insert(
                            syntax::referent_of_carrier(&parsed_parameter.parameter.name)
                                .unwrap_or(&parsed_parameter.parameter.name)
                                .to_string(),
                        );
                    }
                    if let Some(bytes) = parsed_parameter.declared_bytes {
                        declared_loadable_bytes
                            .push((parsed_parameter.parameter.name.clone(), bytes));
                    }
                    parameters.push(parsed_parameter.parameter);
                }
            }

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => {
                    return Ok((
                        ParsedParameters {
                            parameters,
                            struct_params,
                            struct_array_params,
                            reference_params,
                            declared_loadable_bytes,
                        },
                        resource_parameters,
                    ));
                }
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    fn parse_theorem_definition(&mut self) -> Result<TheoremDefinition, ClickError> {
        self.expect_ident_spelling("theorem")?;
        let name = self.expect_ident("theorem name")?;
        let type_parameters = self.parse_click_type_parameters()?;
        let previous_type_parameters = self.names.replace(
            NameKind::TypeParameter,
            type_parameters.iter().cloned().collect(),
        );
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        let previous_integer_params = self.names.replace(
            NameKind::IntegerParameter,
            parsed_parameters
                .parameters
                .iter()
                .filter(|parameter| matches!(parameter.click_type(), ClickType::Integer))
                .map(|parameter| parameter.name().to_string())
                .collect(),
        );
        let previous_integer_literal_context =
            std::mem::replace(&mut self.integer_literal_context, false);
        let previous_integer_lets = self.names.take(NameKind::IntegerLet);
        let mut execution_struct_params = BTreeMap::new();
        let mut execution_struct_array_params = BTreeSet::new();
        let mut executed_reference_params = BTreeSet::new();
        let executes = if self.peek_ident() == Some("executes") {
            self.position += 1;
            let callback = self.expect_ident("callback parameter")?;
            self.expect(Token::LParen)?;
            let call_parameters = self.parse_parameters()?;
            self.expect(Token::RParen)?;
            execution_struct_params = call_parameters.struct_params;
            execution_struct_array_params = call_parameters.struct_array_params;
            // The proof names the executed function's parameters, so its
            // references are referents there too.
            executed_reference_params = call_parameters.reference_params;
            Some(TheoremExecution {
                callback,
                parameters: call_parameters.parameters,
                target_instances: Vec::new(),
            })
        } else {
            None
        };
        let mut target_instances = Vec::new();
        let body_open = self.here();
        let first_implicit_proof = self.implicit_proof_spans.len();
        let first_proof_clause = self.proof_clause_spans.len();
        self.expect(Token::LBrace)?;

        let parameter_names = parsed_parameters
            .parameters
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<BTreeSet<_>>();
        let previous_theorem_param_names = self
            .names
            .replace(NameKind::TheoremParameter, parameter_names.clone());
        let previous_struct_params = std::mem::replace(
            &mut self.names.struct_params,
            parsed_parameters.struct_params,
        );
        let previous_struct_array_params = self.names.replace(
            NameKind::StructArrayParameter,
            parsed_parameters.struct_array_params,
        );
        let mut theorem_reference_params = parsed_parameters.reference_params;
        theorem_reference_params.extend(executed_reference_params);
        let previous_reference_params = self
            .names
            .replace(NameKind::ReferenceParameter, theorem_reference_params);
        let previous_algebraic_params = std::mem::replace(
            &mut self.names.algebraic_params,
            algebraic_parameter_types(&parsed_parameters.parameters),
        );
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut ensure_kinds = Vec::new();
        let mut clause_positions = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            let clause_start = self.here();
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
                        ContractLetBindingKind::Parameter => {
                            return Err(self.error(
                                "`let name: type;` declares a value parameter only in a named contract",
                            ));
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
                        self.names.insert(
                            NameKind::IntegerLet,
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
                    ensure_kinds.push(ClaimClauseKind::Owns);
                    clause_positions.push(clause_start.clone());
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                proof_bindings: Vec::new(),
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
                    ensure_kinds.push(ClaimClauseKind::Produces);
                    clause_positions.push(clause_start.clone());
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                proof_bindings: Vec::new(),
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
                        // Executed arguments are in scope in this proof block,
                        // including the record metadata needed for field paths.
                        let scope = self.names.scope();
                        for (name, layout) in &execution_struct_params {
                            self.names
                                .set_scoped_struct_param(name, Some(layout.clone()));
                        }
                        for name in &execution_struct_array_params {
                            self.names
                                .set_scoped(NameKind::StructArrayParameter, name, true);
                        }
                        let parsed = self.parse_ensure_clause_with_execution_scope(Some(&names));
                        self.names.end(scope);
                        let (ensure, introduced) = parsed?;
                        target_instances.extend(introduced);
                        ensure
                    } else {
                        self.parse_ensure_clause()?
                    };
                    ensure_kinds.push(ClaimClauseKind::Ensures);
                    clause_positions.push(clause_start.clone());
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
        let body_close = self.here();
        self.expect(Token::RBrace)?;
        self.names.struct_params = previous_struct_params;
        self.names
            .replace(NameKind::StructArrayParameter, previous_struct_array_params);
        self.names
            .replace(NameKind::ReferenceParameter, previous_reference_params);
        self.names.algebraic_params = previous_algebraic_params;
        self.names
            .replace(NameKind::TypeParameter, previous_type_parameters);
        self.names
            .replace(NameKind::TheoremParameter, previous_theorem_param_names);
        self.names
            .replace(NameKind::IntegerParameter, previous_integer_params);
        self.names
            .replace(NameKind::IntegerLet, previous_integer_lets);
        self.integer_literal_context = previous_integer_literal_context;

        let requires: Vec<Requirement> = requires
            .into_iter()
            .flat_map(expand_aggregate_requirement)
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
        let ensure_claim_ids = flattened_claim_ids(&ensure_kinds, &ensure_source_clauses);
        Ok(TheoremDefinition {
            body: DeclarationBody {
                open: body_open,
                close: body_close,
                clauses: clause_positions,
                exceptional_clauses: Vec::new(),
                implicit_proofs: self.implicit_proof_spans[first_implicit_proof..].to_vec(),
                proof_clauses: self.proof_clause_spans[first_proof_clause..].to_vec(),
            },
            name,
            type_parameters,
            parameters: parsed_parameters.parameters,
            executes: executes.map(|execution| TheoremExecution {
                target_instances,
                ..execution
            }),
            requires,
            ensures,
            ensure_claim_ids,
        })
    }

    /// Whether the `sizeof` at `index` is the whole size of an allocation,
    /// `allocation(p, sizeof(Node<T>))`: the size an instance's `new`
    /// allocates, at each instance its own, which a proof cannot otherwise
    /// read.
    fn whole_allocation_size_at(&self, index: usize) -> bool {
        let Some(close) = self.matching_parentheses.get(index + 1).cloned().flatten() else {
            return false;
        };
        if index < 3
            || self.tokens.get(index - 1) != Some(&Token::Comma)
            || self.tokens.get(close + 1) != Some(&Token::RParen)
        {
            return false;
        }
        // The `(` the size's argument list opens with, found by walking back
        // over the allocation's first argument only.
        let mut depth = 0usize;
        let mut at = index - 1;
        while at > 0 {
            at -= 1;
            match self.tokens[at] {
                Token::RParen | Token::RBracket | Token::RBrace => depth += 1,
                Token::LBracket | Token::LBrace => depth = depth.saturating_sub(1),
                Token::LParen if depth > 0 => depth -= 1,
                Token::LParen => {
                    return at > 0
                        && self.matching_parentheses.get(at).cloned().flatten() == Some(close + 1)
                        && matches!(&self.tokens[at - 1], Token::Ident(name) if name == "allocation");
                }
                _ => {}
            }
        }
        false
    }

    /// Whether the record `name` holds a value of an abstract type, directly
    /// or in an embedded record.
    fn layout_holds_abstract_value(&self, name: &str) -> bool {
        let mut pending = vec![name.to_string()];
        let mut seen = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let Some(layout) = self.struct_layouts.get(&name) else {
                continue;
            };
            for field in layout.fields().values() {
                match (field.c_type(), field.struct_name()) {
                    (C0Type::Parameter(_), _) => return true,
                    (C0Type::Int32, Some(embedded)) => pending.push(embedded.to_string()),
                    _ => {}
                }
            }
        }
        false
    }

    /// A method of a class template verified once for every type argument,
    /// `template<class T> void Cell<T>::set(T v) { ... } by { ... }`: its
    /// type parameters are abstract types in its head, contract and proof.
    fn parse_cpp_template_method(&mut self) -> Result<FunctionBlock, ClickError> {
        self.expect_ident_spelling("template")?;
        self.expect(Token::LessThan)?;
        let mut names = Vec::new();
        loop {
            match self.peek_ident() {
                Some("class" | "typename") => self.position += 1,
                _ => return Err(self.error("a template parameter is a type, `class T`")),
            }
            names.push(self.expect_ident("template parameter name")?);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::GreaterThan)?;
        let previous_abstract = self.rust_abstract_type_parameters.clone();
        self.rust_abstract_type_parameters.extend(names);
        let block = self.parse_function_block_in_scope(false);
        self.rust_abstract_type_parameters = previous_abstract;
        block
    }

    fn parse_function_block(&mut self, external: bool) -> Result<FunctionBlock, ClickError> {
        // A generic Rust function's abstract type parameters, which its
        // signature declares, are in scope for its contract too.
        let previous_abstract = self.rust_abstract_type_parameters.clone();
        let block = self.parse_function_block_in_scope(external);
        self.rust_abstract_type_parameters = previous_abstract;
        block
    }

    fn parse_function_block_in_scope(
        &mut self,
        external: bool,
    ) -> Result<FunctionBlock, ClickError> {
        let previous_function_block = std::mem::replace(&mut self.in_function_block, true);
        let block_scope = self.names.scope();
        let previous_resource_targets = std::mem::take(&mut self.names.resource_targets);
        let previous_resource_bindings = std::mem::take(&mut self.names.resource_bindings);
        let previous_value_binders = std::mem::take(&mut self.names.value_binders);
        let previous_value_binder_order = std::mem::take(&mut self.names.value_binder_order);
        let written_instance = self.rust_written_instances.contains(&self.position);
        // A crate trait's method is declared without `extern`, as Rust
        // writes it in the `trait` block.
        if external && self.rust_trait_interface.is_none() {
            self.expect_ident_spelling("extern")?;
        }
        let ParsedFunctionSignature {
            signature,
            mut struct_params,
            struct_array_params,
            mut reference_params,
            return_struct_name,
        } = {
            let previous = std::mem::replace(&mut self.exact_long_rank, true);
            let signature = self.parse_function_signature();
            self.exact_long_rank = previous;
            signature?
        };
        if self.verifies_cpp()
            && !written_instance
            && self.cpp_generic_instances.contains(signature.name())
        {
            return Err(self.error(format!(
                "`{}` is an instance of a generic class template's method, whose contract \
                 it has at its types; write the contract once, on the method in \
                 `template<class T>`",
                crate::languages::display_source_names(signature.name())
            )));
        }
        let table_name = signature
            .c_source
            .as_ref()
            .and_then(|path| {
                let (_, name) = signature.name().rsplit_once("::")?;
                self.qualified_functions
                    .get(&(path.clone(), name.to_string()))
            })
            .map(String::as_str)
            .unwrap_or_else(|| signature.name())
            .to_string();
        if let Some(struct_name) = return_struct_name {
            struct_params.insert("result".to_string(), struct_name);
        }
        // A local of reference type names its referent in this function's
        // proof, as a reference parameter does. The signature wins a shared
        // spelling: a parameter of that name that is not a reference keeps
        // its own reading.
        for name in self
            .local_struct_pointers_by_function
            .get(&table_name)
            .into_iter()
            .flat_map(|locals| &locals.references)
        {
            if !signature
                .parameters()
                .iter()
                .any(|parameter| parameter.name() == name)
            {
                reference_params.insert(name.clone());
            }
        }
        let body_open = self.here();
        let first_implicit_proof = self.implicit_proof_spans.len();
        let first_proof_clause = self.proof_clause_spans.len();
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
        let previous_integer_params = self.names.take(NameKind::IntegerParameter);
        let previous_integer_lets = self.names.take(NameKind::IntegerLet);
        let previous_integer_literal_context =
            std::mem::replace(&mut self.integer_literal_context, false);
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut decreases = None;
        let mut constructs = Vec::new();
        let mut ensures = Vec::new();
        // The kind each written postcondition clause was written as, which
        // its claim label counts it among.
        let mut ensure_kinds = Vec::new();
        let mut clause_positions = Vec::new();
        let mut exceptional_ensures = Vec::new();
        let mut exceptional_positions = Vec::new();
        // A local of struct-pointer type is a memory base in this function's
        // proof just as a parameter is. The signature wins a shared spelling.
        for (name, struct_name) in self
            .local_struct_pointers_by_function
            .get(&table_name)
            .into_iter()
            .flat_map(|locals| &locals.struct_pointers)
        {
            struct_params
                .entry(name.clone())
                .or_insert_with(|| struct_name.clone());
        }
        let previous_struct_params =
            std::mem::replace(&mut self.names.struct_params, struct_params);
        let previous_void_pointer_params = self.names.replace(
            NameKind::VoidPointerParameter,
            signature
                .parameters()
                .iter()
                .filter(|parameter| parameter.c_type() == C0Type::VoidPointer)
                .map(|parameter| parameter.name().to_string())
                .collect(),
        );
        let previous_c_object_names = std::mem::replace(
            &mut self.names.c_object_names,
            self.c_object_names_by_function.get(&table_name).cloned(),
        );
        let previous_c_parameter_types = std::mem::replace(
            &mut self.names.c_parameter_types,
            signature
                .parameters()
                .iter()
                .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
                .collect(),
        );
        let previous_parameter_struct_casts =
            std::mem::take(&mut self.names.parameter_struct_casts);
        let aggregate_objects = self
            .aggregate_objects_by_function
            .get(&table_name)
            .cloned()
            .unwrap_or_default();
        let previous_aggregate_objects =
            std::mem::replace(&mut self.names.aggregate_objects, aggregate_objects);
        // A parameter shadowing a file-scope array hides it inside this
        // function, for indexing shapes and element widths alike.
        let global_array_shapes = self
            .global_array_shapes_by_function
            .get(&table_name)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|(name, _)| !parameter_names.contains(name))
            .collect();
        let previous_global_array_shapes =
            std::mem::replace(&mut self.names.global_array_shapes, global_array_shapes);
        let mut visible_struct_array_params = struct_array_params;
        if let Some(aggregate_array_objects) =
            self.aggregate_array_objects_by_function.get(&table_name)
        {
            visible_struct_array_params.extend(
                aggregate_array_objects
                    .iter()
                    .filter(|name| !parameter_names.contains(*name))
                    .cloned(),
            );
        }
        let previous_struct_array_params = self
            .names
            .replace(NameKind::StructArrayParameter, visible_struct_array_params);
        let previous_reference_params = self
            .names
            .replace(NameKind::ReferenceParameter, reference_params);
        let previous_reference_result = std::mem::replace(
            &mut self.current_reference_result,
            signature.returns_reference(),
        );
        while self.peek() != Some(&Token::RBrace) {
            let clause_start = self.here();
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
                    if binding.kind == ContractLetBindingKind::Parameter {
                        let c_type = binding
                            .click_type
                            .as_ref()
                            .and_then(ClickType::c_type)
                            .filter(|c_type| !c_type.is_pointer() && *c_type != C0Type::Void)
                            .ok_or_else(|| {
                                self.error(format!(
                                    "contract value parameter `{}` must have a scalar type",
                                    binding.name
                                ))
                            })?;
                        self.contract_value_parameters.push(FunctionParameter {
                            click_type: ClickType::C(c_type),
                            name: binding.name.clone(),
                            struct_name: None,
                            function_pointer_signature: None,
                            constant: false,
                            pointee_constant: false,
                            reference: false,
                        });
                        continue;
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
                        ContractLetBindingKind::Parameter => {
                            return Err(self.error(
                                "`let name: type;` declares a value parameter only in a named contract",
                            ));
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
                        self.names.insert(
                            NameKind::IntegerLet,
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
                        let produces_start = self.here();
                        self.position += 1;
                        let resource = self.parse_owned_resource_binding()?;
                        if matches!(resource, ResourceClause::Named { .. }) {
                            return Err(self.error(
                                "conditional `produces` clauses cannot introduce named resource instances yet",
                            ));
                        }
                        let proof = self.parse_proof_clause_or_default()?;
                        ensure_kinds.push(ClaimClauseKind::Produces);
                        clause_positions.push(produces_start.clone());
                        ensures.push(
                            apply_contract_lets_to_ensure_clause(
                                EnsureClause {
                                    proof_bindings: Vec::new(),
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
                    // A parenthesized list of two or more components is a
                    // lexicographic tuple, the loop slot's syntax; a single
                    // parenthesized expression stays one expression.
                    let substitutions = contract_let_substitutions(&contract_lets);
                    let mut components = Vec::new();
                    if self.peek() == Some(&Token::LParen) {
                        let start = self.position;
                        self.position += 1;
                        let first = self.parse_contract_expression()?;
                        if self.peek() == Some(&Token::Comma) {
                            components.push(first);
                            while self.peek() == Some(&Token::Comma) {
                                self.position += 1;
                                components.push(self.parse_contract_expression()?);
                            }
                            self.expect(Token::RParen)?;
                        } else {
                            self.position = start;
                        }
                    }
                    if components.is_empty() {
                        let measure = self.parse_contract_expression()?;
                        self.expect(Token::Semicolon)?;
                        decreases = Some(CFunctionDecrease::Unresolved(
                            substitute_contract_expression(&measure, &substitutions)
                                .map_err(|message| self.error(message))?,
                        ));
                    } else {
                        self.expect(Token::Semicolon)?;
                        decreases = Some(CFunctionDecrease::Lexicographic(
                            components
                                .iter()
                                .map(|component| {
                                    substitute_contract_expression(component, &substitutions)
                                })
                                .collect::<Result<Vec<_>, _>>()
                                .map_err(|message| self.error(message))?,
                        ));
                    }
                }
                Some("owns") => {
                    self.position += 1;
                    let resource = if self.value_binder_follows(false) {
                        self.parse_value_binder(
                            ResourceAccessMode::Own,
                            signature.name(),
                            &parameter_names,
                            requires.len(),
                        )?
                    } else {
                        self.parse_owned_resource_binding()?
                    };
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
                    ensure_kinds.push(ClaimClauseKind::Owns);
                    clause_positions.push(clause_start.clone());
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                proof_bindings: Vec::new(),
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
                    let resource = if self.value_binder_follows(true) {
                        self.parse_value_binder(
                            ResourceAccessMode::View,
                            signature.name(),
                            &parameter_names,
                            requires.len(),
                        )?
                    } else {
                        self.parse_resource_target(ResourceAccessMode::View)?
                    };
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
                    let resource = if self.value_binder_follows(false) {
                        self.parse_value_binder(
                            ResourceAccessMode::Own,
                            signature.name(),
                            &parameter_names,
                            requires.len(),
                        )?
                    } else {
                        self.parse_owned_resource_binding()?
                    };
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
                    ensure_kinds.push(ClaimClauseKind::Produces);
                    clause_positions.push(clause_start.clone());
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(
                            EnsureClause {
                                proof_bindings: Vec::new(),
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
                    ensure_kinds.push(ClaimClauseKind::Ensures);
                    clause_positions.push(clause_start.clone());
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
                    exceptional_positions.push(clause_start.clone());
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
        let body_close = self.here();
        self.expect(Token::RBrace)?;
        let grouped_proof = if self.peek_ident() == Some("by") {
            let proof = self.parse_by_clause()?;
            // The grouped proof proves every claim without its own `by`; one
            // that would prove none is refused rather than silently unused.
            let mut claims = ensures.iter().chain(exceptional_ensures.iter()).peekable();
            if claims.peek().is_some()
                && claims.all(|clause| !matches!(clause.proof(), SourceProof::Default))
            {
                return Err(self.error(
                    "this grouped function proof proves no claim: every postcondition has its own `by`",
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
        if signature.exceptional_type().is_some()
            && (!constructs.is_empty()
                || requires
                    .iter()
                    .any(|requirement| matches!(requirement, Requirement::Resource(_)))
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
        let c_object_names = self
            .c_object_names_by_function
            .get(&table_name)
            .cloned()
            .unwrap_or_else(|| {
                std::sync::Arc::new(
                    self.names
                        .aggregate_objects
                        .keys()
                        .chain(self.names.global_array_shapes.keys())
                        .cloned()
                        .collect(),
                )
            });
        self.names.struct_params = previous_struct_params;
        self.names
            .replace(NameKind::VoidPointerParameter, previous_void_pointer_params);
        self.names.c_parameter_types = previous_c_parameter_types;
        self.names.c_object_names = previous_c_object_names;
        let parameter_struct_casts = std::mem::replace(
            &mut self.names.parameter_struct_casts,
            previous_parameter_struct_casts,
        );
        self.in_function_block = previous_function_block;
        self.names.end_declaration(block_scope);
        self.names.resource_bindings = previous_resource_bindings;
        self.names.resource_targets = previous_resource_targets;
        let mut value_binders_by_name =
            std::mem::replace(&mut self.names.value_binders, previous_value_binders);
        let value_binders = std::mem::replace(
            &mut self.names.value_binder_order,
            previous_value_binder_order,
        )
        .into_iter()
        .filter_map(|name| value_binders_by_name.remove(&name))
        .collect::<Vec<_>>();
        self.names.aggregate_objects = previous_aggregate_objects;
        self.names.global_array_shapes = previous_global_array_shapes;
        self.names
            .replace(NameKind::StructArrayParameter, previous_struct_array_params);
        self.names
            .replace(NameKind::ReferenceParameter, previous_reference_params);
        self.current_reference_result = previous_reference_result;
        self.names
            .replace(NameKind::IntegerParameter, previous_integer_params);
        self.names
            .replace(NameKind::IntegerLet, previous_integer_lets);
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
        let ensure_claim_ids = flattened_claim_ids(&ensure_kinds, &ensure_source_clauses);

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

        let mut parameter_field_places: BTreeMap<_, _> = signature
            .parameters()
            .iter()
            .filter_map(|parameter| {
                let layout = self.struct_layouts.get(parameter.struct_name()?)?;
                Some((
                    parameter.name().to_string(),
                    super::scalar_field_places(layout, &self.struct_layouts),
                ))
            })
            .collect();
        // A local of struct-pointer type is printed as a parameter is. The
        // signature wins a shared spelling.
        for (name, struct_name) in self
            .local_struct_pointers_by_function
            .get(&table_name)
            .into_iter()
            .flat_map(|locals| &locals.struct_pointers)
        {
            if signature
                .parameters()
                .iter()
                .all(|parameter| parameter.name() != name)
                && let Some(layout) = self.struct_layouts.get(struct_name)
            {
                parameter_field_places.insert(
                    name.clone(),
                    super::scalar_field_places(layout, &self.struct_layouts),
                );
            }
        }
        let pointee_field_places =
            super::pointee_field_places(parameter_field_places.values(), &self.struct_layouts);
        let recursion_peers = self
            .recursion_peers_by_function
            .get(&table_name)
            .cloned()
            .unwrap_or_default();
        // A named contract's value parameters follow its C parameters, so its
        // clauses read them as they read the C parameters.
        let mut signature = signature;
        if self.in_contract_definition {
            signature
                .parameters
                .extend(self.contract_value_parameters.iter().cloned());
        }
        // A closure's captures lead its signature, as they lead its function.
        if !external && let Some(captures) = self.closure_captures.get(&table_name) {
            let mut parameters = captures.clone();
            parameters.append(&mut signature.parameters);
            signature.parameters = parameters;
        }
        Ok(FunctionBlock {
            body: DeclarationBody {
                open: body_open,
                close: body_close,
                clauses: clause_positions,
                exceptional_clauses: exceptional_positions,
                implicit_proofs: self.implicit_proof_spans[first_implicit_proof..].to_vec(),
                proof_clauses: self.proof_clause_spans[first_proof_clause..].to_vec(),
            },
            c_object_names,
            recursion_peers,
            signature,
            external,
            one_call_proof: false,
            tactic_procedure: false,
            requires,
            requirement_source_clauses,
            decreases,
            structural_clauses: StructuralClauses::default(),
            constructs,
            ensures,
            exceptional_ensures,
            ensure_source_clauses,
            ensure_claim_ids,
            grouped_proof: grouped_proof.map(std::sync::Arc::new),
            parameter_struct_casts,
            parameter_field_places,
            pointee_field_places,
            value_binders,
            witness_count: 0,
        })
    }

    fn parse_contract_let_binding(&mut self) -> Result<ContractLetBinding, ClickError> {
        self.expect_ident_spelling("let")?;
        let name = self.expect_ident("let binding name")?;
        self.refuse_bool_literal_binder(&name)?;
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
        } else if self.in_contract_definition
            && self.peek() == Some(&Token::Semicolon)
            && click_type.is_some()
        {
            ContractLetBindingKind::Parameter
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
        if std::mem::take(&mut self.pending_tactic_signature) {
            let name = self.expect_ident("tactic name")?;
            self.expect(Token::LParen)?;
            let parsed_parameters = self.parse_click_parameters()?;
            self.expect(Token::RParen)?;
            if let Some(parameter) = parsed_parameters
                .parameters
                .iter()
                .find(|parameter| parameter.click_type().c_type().is_none())
            {
                return Err(self.error(format!(
                    "tactic parameter `{}` has a mathematical type; tactic parameters are C \
                     scalars and pointers in this release",
                    parameter.name()
                )));
            }
            if matches!(self.peek_ident(), Some("throws" | "diverges")) {
                return Err(self.error(format!(
                    "a tactic runs no code, so its signature cannot declare `{}`",
                    self.peek_ident().unwrap_or_default()
                )));
            }
            return Ok(ParsedFunctionSignature {
                signature: FunctionSignature {
                    c_source: None,
                    return_type: C0Type::Void,
                    return_struct_name: None,
                    return_pointee_constant: false,
                    return_reference: false,
                    name,
                    parameters: parsed_parameters.parameters,
                    exceptional_type: None,
                    diverges: false,
                    declared_loadable_bytes: parsed_parameters.declared_loadable_bytes,
                    rust_spelling: Default::default(),
                },
                struct_params: parsed_parameters.struct_params,
                struct_array_params: parsed_parameters.struct_array_params,
                reference_params: parsed_parameters.reference_params,
                return_struct_name: None,
            });
        }
        self.rust_slice_params.clear();
        if self.peek_ident() == Some("fn") {
            return self.parse_rust_function_signature();
        }
        // A C++ head is the C++ declaration: `static` marks a static member,
        // and a constructor or destructor has no return type.
        let is_static = self.verifies_cpp() && self.peek_ident() == Some("static");
        if is_static {
            self.position += 1;
        }
        let returnless = self.verifies_cpp() && self.cpp_returnless_declarator_follows();
        let parsed_return_type = if returnless {
            ParsedType {
                c_type: C0Type::Void,
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            }
        } else {
            self.parse_type()?
        };
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
        let mut c_source = None;
        let (name, receiver) = if self.verifies_cpp() {
            let declarator = self.parse_cpp_declarator(is_static)?;
            if declarator.returnless != returnless {
                return Err(self.error(if declarator.returnless {
                    "a constructor or destructor has no return type"
                } else {
                    "a C++ head needs its return type"
                }));
            }
            (declarator.name, declarator.receiver)
        } else {
            let alias = self.expect_c_declaration_ident("function name")?;
            let name =
                if let Some((alias, name)) = alias.split_once("::") {
                    c_source =
                        Some(self.source_aliases.get(alias).cloned().ok_or_else(|| {
                            self.error(format!("unknown C source alias `{alias}`"))
                        })?);
                    format!("{alias}::{name}")
                } else if self.peek() == Some(&Token::ColonColon) {
                    self.position += 1;
                    let name = self.expect_ident("C function name")?;
                    c_source =
                        Some(self.source_aliases.get(&alias).cloned().ok_or_else(|| {
                            self.error(format!("unknown C source alias `{alias}`"))
                        })?);
                    format!("{alias}::{name}")
                } else {
                    alias
                };
            (name, None)
        };
        self.expect(Token::LParen)?;
        let mut parsed_parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        // A named contract describes a function type, whose receiver is an
        // ordinary parameter; a verified or `extern` head leaves `this`
        // implicit. A member of a class template instance, whose mangled
        // name (`__`) a head does not yet spell natively, keeps its explicit
        // receiver.
        if self.verifies_cpp()
            && !self.in_contract_definition
            && !name.contains("__")
            && parsed_parameters
                .parameters
                .iter()
                .any(|parameter| parameter.name == "this")
        {
            return Err(self.error(
                "a C++ member function's `this` is implicit; write the C++ declaration, as \
                 `void Rec::method(int x)`, `Rec::Rec(int x)` or `Rec::~Rec()`",
            ));
        }
        if let Some(record) = receiver {
            // `Rec::m(...) const` reads through a `const Rec* this`.
            let constant = self.peek_ident() == Some("const");
            if constant {
                self.position += 1;
            }
            let this = self.parse_parameter_array_suffix(
                "this".into(),
                ParsedType {
                    c_type: C0Type::Int32Pointer,
                    struct_name: Some(record.clone()),
                    struct_pointer: true,
                    constant: false,
                    pointee_constant: constant,
                    reference: false,
                },
            )?;
            parsed_parameters.parameters.insert(0, this.parameter);
            parsed_parameters
                .struct_params
                .insert("this".into(), record);
        }
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
        let reference_params = parsed_parameters.reference_params;

        let parsed = ParsedFunctionSignature {
            signature: FunctionSignature {
                c_source,
                return_type,
                return_struct_name: parsed_return_type.struct_name.clone(),
                return_pointee_constant: parsed_return_type.pointee_constant,
                return_reference: parsed_return_type.reference,
                name,
                parameters: parsed_parameters.parameters,
                exceptional_type,
                diverges,
                declared_loadable_bytes: parsed_parameters.declared_loadable_bytes,
                rust_spelling: Default::default(),
            },
            struct_params,
            struct_array_params,
            reference_params,
            return_struct_name: parsed_return_type.struct_name,
        };
        if self.verifies_rust() && !self.in_contract_definition {
            let replacement = rust_signature_hint(&parsed)
                .map(|signature| format!("write `{signature}`"))
                .unwrap_or_else(|| {
                    "write a `fn` signature, with methods in an `impl` block".into()
                });
            return Err(self.error(format!(
                "a Rust source's function contract uses Rust syntax; {replacement}"
            )));
        }
        Ok(parsed)
    }

    /// The index between brackets. Out of line, with the two helpers below:
    /// their callers are the recursive expression parsers, whose frames every
    /// temporary enlarges.
    #[inline(never)]
    fn parse_place_index(&mut self) -> Result<ContractExpression, ClickError> {
        let index = self.parse_contract_expression()?;
        Ok(index)
    }

    /// The right operand of a binary operator, with any Rust `as` casts.
    #[inline(never)]
    fn parse_binary_operand(&mut self) -> Result<ContractExpression, ClickError> {
        let operand = self.parse_contract_unary()?;
        self.parse_rust_casts(operand)
    }

    /// `true` and `false` are `bool` literals unless a C name in scope, or a
    /// proof binder, spells them; such a name keeps its meaning, as C's own
    /// `true` and `false` are conveniences rather than reserved words.
    fn bool_literal_spelling(&self, name: &str) -> Option<bool> {
        let value = match name {
            "true" => true,
            "false" => false,
            _ => return None,
        };
        let shadowed = self.names.c_parameter_types.contains_key(name)
            || self
                .names
                .c_object_names
                .as_ref()
                .is_some_and(|names| names.contains(name))
            || self.names.contains(NameKind::ProofBinder, name)
            || self.names.arm_binding_types.contains_key(name);
        (!shadowed).then_some(value)
    }

    /// Refuse a Click binder spelled `true` or `false`: inside Click those
    /// spellings are the `bool` literals, so the binder could never be read.
    fn refuse_bool_literal_binder(&self, name: &str) -> Result<(), ClickError> {
        if matches!(name, "true" | "false") {
            return Err(self.error(format!(
                "`{name}` is a `bool` literal and cannot name a Click binder"
            )));
        }
        Ok(())
    }

    /// A C variable named in a contract, or the length a slice parameter's
    /// `name.len()` denotes.
    #[inline(never)]
    fn c_variable_expression(&mut self, name: String) -> ContractExpression {
        let name = self.take_rust_slice_len(&name).unwrap_or(name);
        ContractExpression::CFragment(CExpression::Variable(name))
    }

    fn parse_parameters(&mut self) -> Result<ParsedParameters, ClickError> {
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        let mut struct_array_params = BTreeSet::new();
        let mut reference_params = BTreeSet::new();
        let mut declared_loadable_bytes = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(ParsedParameters {
                parameters,
                struct_params,
                struct_array_params,
                reference_params,
                declared_loadable_bytes,
            });
        }

        loop {
            // `const std::function<int(int)>& f` or `std::function<int(int)> f`:
            // a callable value, as a function pointer is; so is `unary f` for a
            // C function-pointer typedef.
            let callable = match self.parse_cpp_std_function_type()? {
                Some(callable) => Some(callable),
                None => self.parse_c_function_pointer_typedef()?,
            };
            if let Some((c_type, function_pointer_signature)) = callable {
                let name = self.expect_ident("parameter name")?;
                parameters.push(FunctionParameter {
                    click_type: ClickType::C(c_type),
                    name,
                    struct_name: None,
                    function_pointer_signature: Some(function_pointer_signature),
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                });
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        continue;
                    }
                    Some(Token::RParen) => {
                        return Ok(ParsedParameters {
                            parameters,
                            struct_params,
                            struct_array_params,
                            reference_params,
                            declared_loadable_bytes,
                        });
                    }
                    _ => return Err(self.error("expected `,` or `)` after a parameter")),
                }
            }
            // `triple values` for a C array typedef, `int values[3]`.
            if let Some((element, length, constant)) = self.parse_c_array_typedef()? {
                let name = self.expect_ident("parameter name")?;
                let parsed_type = ParsedType {
                    c_type: element,
                    struct_name: None,
                    struct_pointer: false,
                    constant,
                    pointee_constant: false,
                    reference: false,
                };
                let parsed_parameter = self.array_parameter(name, parsed_type, Some(length))?;
                if let Some(bytes) = parsed_parameter.declared_bytes {
                    declared_loadable_bytes.push((parsed_parameter.parameter.name.clone(), bytes));
                }
                parameters.push(parsed_parameter.parameter);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        continue;
                    }
                    Some(Token::RParen) => {
                        return Ok(ParsedParameters {
                            parameters,
                            struct_params,
                            struct_array_params,
                            reference_params,
                            declared_loadable_bytes,
                        });
                    }
                    _ => {
                        return Err(self.error(
                            "expected `,` or `)` after a parameter of an array typedef, \
                             which already has its length",
                        ));
                    }
                }
            }
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
                        reference: false,
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
                if parsed_parameter.parameter.click_type
                    == ClickType::C(C0Type::Int32PointerPointer)
                {
                    struct_params.insert(
                        struct_pointer_pointer_key(&parsed_parameter.parameter.name),
                        struct_name.clone(),
                    );
                }
                struct_params.insert(parsed_parameter.parameter.name.clone(), struct_name);
            }
            if parsed_parameter.struct_array {
                struct_array_params.insert(parsed_parameter.parameter.name.clone());
            }
            if parsed_parameter.parameter.is_reference() {
                reference_params.insert(
                    syntax::referent_of_carrier(&parsed_parameter.parameter.name)
                        .unwrap_or(&parsed_parameter.parameter.name)
                        .to_string(),
                );
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
                        reference_params,
                        declared_loadable_bytes,
                    });
                }
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    /// A typedef name of the verified source is written only in a function
    /// head, which restates the declaration.
    fn check_head_typedef(&self, spelling: &str) -> Result<(), ClickError> {
        if self.exact_long_rank {
            return Ok(());
        }
        Err(self.error(format!(
            "`{spelling}` is a typedef name of the verified source, which a function head \
             may write; a specification writes Click's type, such as `int32`"
        )))
    }

    fn parse_type(&mut self) -> Result<ParsedType, ClickError> {
        let mut is_constant = if self.peek_ident() == Some("const") {
            self.position += 1;
            true
        } else {
            false
        };
        // A generic class template's type parameter in its method's head,
        // `T`, `T&` or `T*`: a value of the abstract type, or its address.
        if self.verifies_cpp()
            && let Some(name) = self.peek_ident()
            && self.rust_abstract_type_parameters.contains(name)
        {
            let parameter = crate::kernel::TypeParameterName::intern(name);
            self.position += 1;
            let indirection = match self.peek() {
                Some(Token::Amp) => Some(true),
                Some(Token::Star) => Some(false),
                _ => None,
            };
            if let Some(reference) = indirection {
                self.position += 1;
                return Ok(ParsedType {
                    c_type: C0Type::ParameterPointer(parameter),
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: is_constant,
                    reference,
                });
            }
            return Ok(ParsedType {
                c_type: C0Type::Parameter(parameter),
                struct_name: None,
                struct_pointer: false,
                constant: is_constant,
                pointee_constant: false,
                reference: false,
            });
        }
        // C++ names a record by its own name or path, `std::span<int>`; C
        // writes `struct name`.
        let qualified_record = if self.verifies_cpp() {
            self.parse_cpp_record_type()
        } else {
            None
        };
        let spelling = match &qualified_record {
            Some(record) => record.clone(),
            None => self.expect_ident("type")?,
        };
        let cpp_record = qualified_record.is_some()
            || (self.verifies_cpp() && self.struct_layouts.contains_key(&spelling));
        // A function head may write a typedef name of the verified C source
        // for the type it stands for, where the name is not a standard
        // spelling; a specification writes Click's type.
        let typedef_struct = match self.c_typedefs.get(&spelling) {
            Some(syntax::C0HeadTypedef::Struct {
                name,
                c_type,
                constant,
                pointee_constant,
            }) => {
                self.check_head_typedef(&spelling)?;
                is_constant |= constant;
                Some((name.clone(), *c_type, *pointee_constant))
            }
            _ => None,
        };
        // A pointer alias has already supplied its `*`s: a `const` written
        // before it qualifies the pointer, as in C.
        let alias_pointer = typedef_struct
            .as_ref()
            .filter(|(_, c_type, _)| *c_type != C0Type::Int32)
            .map(|(_, c_type, pointee_constant)| (*c_type, *pointee_constant));
        if spelling == "struct" || cpp_record || typedef_struct.is_some() {
            let struct_name = if let Some((name, _, _)) = typedef_struct {
                name
            } else if cpp_record {
                spelling
            } else {
                self.expect_ident("struct name")?
            };
            let mut object_constant = is_constant;
            if self.peek_ident() == Some("const") {
                self.position += 1;
                object_constant = true;
            }
            if self.peek() == Some(&Token::Amp) && alias_pointer.is_none() {
                self.position += 1;
                return Ok(ParsedType {
                    c_type: C0Type::Int32Pointer,
                    struct_name: Some(struct_name),
                    struct_pointer: true,
                    constant: false,
                    pointee_constant: object_constant,
                    reference: true,
                });
            }
            if self.peek() == Some(&Token::Star) || alias_pointer.is_some() {
                let (mut c_type, mut pointee_constant) =
                    alias_pointer.unwrap_or((C0Type::Int32, false));
                let mut saw_pointer = alias_pointer.is_some();
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
                    reference: false,
                });
            }
            return Ok(ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(struct_name),
                struct_pointer: false,
                constant: object_constant,
                pointee_constant: false,
                reference: false,
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
            self.plain_char,
        )
        .map_err(|message| self.error(message))?;
        // A specification type names a representation: a sidecar's `long
        // long` is `int64`, which matches a C `long` or `long long` alike. A
        // function head restates a C declaration and keeps its rank.
        let integer = integer.map(|(c_type, count)| {
            if self.exact_long_rank {
                (c_type, count)
            } else {
                (c_type.erase_long_rank(), count)
            }
        });
        let typedef_rank = if self.exact_long_rank {
            self.int64_t_rank
        } else {
            LongRank::Long
        };
        // A scalar pointer alias's pointee qualification, as for a struct one.
        let mut alias_scalar_pointer = None;
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
                "int64" | "ssize_t" => C0Type::Int64(LongRank::Long),
                "int64_t" => C0Type::Int64(typedef_rank),
                "uint64" | "size_t" => C0Type::UInt64(LongRank::Long),
                "uint64_t" => C0Type::UInt64(typedef_rank),
                "int128" => C0Type::Int128,
                "uint128" => C0Type::UInt128,
                "float" => C0Type::Float32,
                "double" => C0Type::Float64,
                "volatile" => {
                    return Err(self.error("the `volatile` qualifier is not supported by Click"));
                }
                _ if let Some(typedef) = self.c_typedefs.get(&spelling) => {
                    self.check_head_typedef(&spelling)?;
                    let syntax::C0HeadTypedef::Scalar {
                        c_type,
                        constant,
                        pointee_constant,
                    } = *typedef
                    else {
                        return Err(self.error(format!(
                            "the typedef `{spelling}` stands for a union, or volatile or aligned \
                             type, or for different types in two verified sources, or is an array \
                             or function pointer written other than as a parameter's type; a head \
                             writes its C type"
                        )));
                    };
                    is_constant |= constant;
                    if c_type.is_pointer() {
                        alias_scalar_pointer = Some(pointee_constant);
                    }
                    c_type
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
        let mut pointee_constant = alias_scalar_pointer.unwrap_or(false);
        if self.peek_ident() == Some("const") {
            self.position += 1;
            object_constant = true;
        }
        let mut saw_pointer = alias_scalar_pointer.is_some();
        // `T&` is carried by a pointer to `T`. A reference to a pointer is
        // not supported.
        let mut reference = false;
        while self.peek() == Some(&Token::Star)
            || (self.peek() == Some(&Token::Amp) && !saw_pointer && !reference)
        {
            reference = self.peek() == Some(&Token::Amp);
            if saw_pointer && pointee_constant {
                return Err(self
                    .error("const qualification beyond the first pointer level is not supported"));
            }
            let base_constant = object_constant;
            object_constant = false;
            self.position += 1;
            c_type = match c_type {
                C0Type::Void if reference => {
                    return Err(self.error("a reference to `void` is not a type"));
                }
                C0Type::Void => C0Type::VoidPointer,
                C0Type::Int8 => C0Type::Int8Pointer,
                C0Type::Int16 => C0Type::Int16Pointer,
                C0Type::UInt16 => C0Type::UInt16Pointer,
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::Char(plain) => C0Type::CharPointer(plain),
                C0Type::UInt8 => C0Type::UInt8Pointer,
                C0Type::UInt32 => C0Type::UInt32Pointer,
                C0Type::Int64(rank) => C0Type::Int64Pointer(rank),
                C0Type::Int128 => C0Type::Int128Pointer,
                C0Type::UInt64(rank) => C0Type::UInt64Pointer(rank),
                C0Type::UInt128 => C0Type::UInt128Pointer,
                C0Type::Int8Pointer => C0Type::Int8PointerPointer,
                C0Type::Int16Pointer => C0Type::Int16PointerPointer,
                C0Type::UInt16Pointer => C0Type::UInt16PointerPointer,
                C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                C0Type::CharPointer(plain) => C0Type::CharPointerPointer(plain),
                C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
                C0Type::UInt32Pointer => C0Type::UInt32PointerPointer,
                C0Type::Int64Pointer(rank) => C0Type::Int64PointerPointer(rank),
                C0Type::Int128Pointer => C0Type::Int128PointerPointer,
                C0Type::UInt64Pointer(rank) => C0Type::UInt64PointerPointer(rank),
                C0Type::UInt128Pointer => C0Type::UInt128PointerPointer,
                _ => return Err(self.error("pointer depth beyond `**` is not supported")),
            };
            if base_constant {
                pointee_constant = true;
            }
            if reference {
                break;
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
            reference,
        })
    }

    /// The class of the object a pointer of the declared type `parsed`
    /// designates (`design/effective-types.md`), as a C parameter of that
    /// type gets it, at every pointer depth. A bare `struct tag` designates
    /// nothing.
    fn declared_object_class(
        &self,
        parsed: &ParsedType,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        match (&parsed.struct_name, parsed.struct_pointer) {
            (Some(_), false) => None,
            (struct_name, _) => syntax::declared_pointee_class(
                parsed.c_type,
                struct_name.as_deref(),
                &self.struct_layouts,
            ),
        }
    }

    fn parse_click_type(&mut self) -> Result<(ClickType, Option<ParsedType>), ClickError> {
        if let Some(parsed) = self.parse_rust_click_type()? {
            return Ok((ClickType::C(parsed.c_type), Some(parsed)));
        }
        let Some(name) = self.peek_ident() else {
            return Err(self.error("expected Click type"));
        };
        // A C++ generic method's or resource's abstract type parameter.
        let c_type = is_c_type_keyword(name)
            || (self.verifies_cpp() && self.rust_abstract_type_parameters.contains(name));
        if c_type || self.at_cpp_record_type() {
            let parsed = self.parse_type()?;
            return Ok((ClickType::C(parsed.c_type), Some(parsed)));
        }
        let Some(name) = self.peek_ident() else {
            return Err(self.error("expected Click type"));
        };
        if name == "Integer" {
            self.position += 1;
            return Ok((ClickType::Integer, None));
        }
        if self.names.contains(NameKind::TypeParameter, name) {
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
                        | C0Type::Char(_)
                        | C0Type::UInt8
                        | C0Type::UInt16
                        | C0Type::UInt32
                        | C0Type::Int64(_)
                        | C0Type::UInt64(_)
                        | C0Type::Float32
                        | C0Type::Float64
                        | C0Type::Int32Array(_)
                        | C0Type::UInt32Array(_)
                        | C0Type::Int128Array(_)
                        | C0Type::Int64Array(_, _)
                        | C0Type::UInt128Array(_)
                        | C0Type::UInt64Array(_, _)
                        | C0Type::CharArray(_, _)
                        | C0Type::UInt8Array(_)
                        | C0Type::Float32Array(_)
                        | C0Type::Float64Array(_)
                        | C0Type::Int32Pointer
                        | C0Type::CharPointer(_)
                        | C0Type::UInt8Pointer
                        | C0Type::Float32Pointer
                        | C0Type::Float64Pointer
                        | C0Type::Int32PointerPointer
                        | C0Type::CharPointerPointer(_)
                        | C0Type::UInt8PointerPointer
                        | C0Type::Float32PointerPointer
                        | C0Type::Float64PointerPointer
                        // A callback field is an eight-byte pointer value,
                        // matching the C boundary's own by-value field set.
                        | C0Type::FunctionPointer(_)
                        // A generic Rust struct's field of a type parameter.
                        | C0Type::Parameter(_)
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

    /// A parameter type that is a function-pointer typedef name of the
    /// verified C source, `unary f`: its callable type. `None`, with nothing
    /// consumed, for any other type.
    fn parse_c_function_pointer_typedef(
        &mut self,
    ) -> Result<Option<(C0Type, syntax::C0FunctionPointerSignature)>, ClickError> {
        let Some(name) = self.peek_ident() else {
            return Ok(None);
        };
        let Some(syntax::C0HeadTypedef::FunctionPointer { c_type, signature }) =
            self.c_typedefs.get(name)
        else {
            return Ok(None);
        };
        // `unary *f` is a pointer to a function pointer, which the type
        // parser refuses.
        if !matches!(self.peek_next(), Some(Token::Ident(_))) {
            return Ok(None);
        }
        let callable = (*c_type, signature.clone());
        self.check_head_typedef(name)?;
        self.position += 1;
        Ok(Some(callable))
    }

    /// A parameter type that is a scalar array typedef name of the verified
    /// C source, `triple values`: its element type, length and element
    /// `const`. `None`, with nothing consumed, for any other type.
    fn parse_c_array_typedef(&mut self) -> Result<Option<(C0Type, u32, bool)>, ClickError> {
        let Some(name) = self.peek_ident() else {
            return Ok(None);
        };
        let Some(syntax::C0HeadTypedef::Array {
            element,
            length,
            constant,
        }) = self.c_typedefs.get(name)
        else {
            return Ok(None);
        };
        if !matches!(self.peek_next(), Some(Token::Ident(_))) {
            return Ok(None);
        }
        let array = (*element, *length, *constant);
        self.check_head_typedef(name)?;
        self.position += 1;
        Ok(Some(array))
    }

    /// A C++ `std::function<R(A...)>` parameter type, possibly `const` and
    /// taken by reference: the callable type of its signature. `None`, with
    /// nothing consumed, when the type is not one.
    fn parse_cpp_std_function_type(
        &mut self,
    ) -> Result<Option<(C0Type, syntax::C0FunctionPointerSignature)>, ClickError> {
        if !self.verifies_cpp() {
            return Ok(None);
        }
        let start = self.position;
        if self.peek_ident() == Some("const") {
            self.position += 1;
        }
        if !(self.peek_ident() == Some("std")
            && self.peek_next() == Some(&Token::ColonColon)
            && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(word)) if word == "function")
            && self.tokens.get(self.position + 3) == Some(&Token::LessThan))
        {
            self.position = start;
            return Ok(None);
        }
        self.position += 4;
        let return_type = self.parse_type()?;
        let callable = self.parse_function_pointer_signature_tail(return_type)?;
        self.expect(Token::GreaterThan)?;
        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
        }
        Ok(Some(callable))
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
                            "expected `,` or `)` in function-pointer parameter list, got {token}"
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
                    // The parameter is the pointer that carries the
                    // reference; the written name is the referent.
                    name: if parsed_type.reference {
                        syntax::reference_carrier_name(&name)
                    } else {
                        name
                    },
                    struct_name: struct_name.clone(),
                    function_pointer_signature: None,
                    constant: parsed_type.constant,
                    pointee_constant: parsed_type.pointee_constant,
                    reference: parsed_type.reference,
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
                    reference: false,
                },
                struct_name,
                declared_bytes: None,
                struct_array: true,
            });
        }
        self.position += 1;
        let length = match self.peek() {
            Some(Token::Number(length)) => {
                let length = *length;
                self.position += 1;
                Some(length)
            }
            _ => None,
        };
        self.expect(Token::RBracket)?;
        self.array_parameter(name, parsed_type, length)
    }

    /// A scalar array parameter, `int values[3]`, which C passes as a
    /// pointer to its first element; `length`, when written, bounds the
    /// bytes the head declares.
    fn array_parameter(
        &self,
        name: String,
        parsed_type: ParsedType,
        length: Option<u32>,
    ) -> Result<ParsedParameter, ClickError> {
        let (pointer_type, element_width) = match parsed_type.c_type {
            C0Type::Int8 => (C0Type::Int8Pointer, 1),
            C0Type::Int16 => (C0Type::Int16Pointer, 2),
            C0Type::Int32 => (C0Type::Int32Pointer, 4),
            C0Type::Char(plain) => (C0Type::CharPointer(plain), 1),
            C0Type::UInt8 => (C0Type::UInt8Pointer, 1),
            C0Type::UInt16 => (C0Type::UInt16Pointer, 2),
            C0Type::UInt32 => (C0Type::UInt32Pointer, 4),
            C0Type::Int64(rank) => (C0Type::Int64Pointer(rank), 8),
            C0Type::Int128 => (C0Type::Int128Pointer, 16),
            C0Type::UInt64(rank) => (C0Type::UInt64Pointer(rank), 8),
            C0Type::UInt128 => (C0Type::UInt128Pointer, 16),
            C0Type::Int8Pointer => (C0Type::Int8PointerPointer, 8),
            C0Type::Int16Pointer => (C0Type::Int16PointerPointer, 8),
            C0Type::UInt16Pointer => (C0Type::UInt16PointerPointer, 8),
            C0Type::Int32Pointer => (C0Type::Int32PointerPointer, 8),
            C0Type::CharPointer(plain) => (C0Type::CharPointerPointer(plain), 8),
            C0Type::UInt8Pointer => (C0Type::UInt8PointerPointer, 8),
            C0Type::UInt32Pointer => (C0Type::UInt32PointerPointer, 8),
            C0Type::Int64Pointer(rank) => (C0Type::Int64PointerPointer(rank), 8),
            C0Type::Int128Pointer => (C0Type::Int128PointerPointer, 8),
            C0Type::UInt64Pointer(rank) => (C0Type::UInt64PointerPointer(rank), 8),
            C0Type::UInt128Pointer => (C0Type::UInt128PointerPointer, 8),
            _ => return Err(self.error("only scalar array parameters are supported")),
        };
        let declared_bytes = length.and_then(|length| length.checked_mul(element_width));
        Ok(ParsedParameter {
            parameter: FunctionParameter {
                click_type: ClickType::C(pointer_type),
                name,
                struct_name: None,
                function_pointer_signature: None,
                constant: false,
                pointee_constant: parsed_type.constant || parsed_type.pointee_constant,
                reference: false,
            },
            struct_name: None,
            declared_bytes,
            struct_array: false,
        })
    }

    /// A field after `.` or `->`: an identifier, or in a Rust sidecar a tuple
    /// field's position, `self.0`, which names the field the importer calls
    /// `_0`.
    fn expect_field_name(&mut self) -> Result<String, ClickError> {
        if self.verifies_rust()
            && self.position > 0
            && self.tokens.get(self.position - 1) == Some(&Token::Arrow)
        {
            return Err(
                self.error("a Rust reference field is written `p.f`; replace `p->f` with `p.f`")
            );
        }
        if self.verifies_rust()
            && let Some(Token::Number(position)) = self.peek()
        {
            let name = format!("_{position}");
            self.position += 1;
            return Ok(name);
        }
        self.expect_ident("field name")
    }

    /// A clause's optional `name:` prefix, as `ensures` takes.
    fn parse_clause_label(&mut self, what: &str) -> Result<Option<String>, ClickError> {
        if matches!(self.peek(), Some(Token::Ident(_))) && self.peek_next() == Some(&Token::Colon) {
            let name = self.expect_ident(what)?;
            self.expect(Token::Colon)?;
            return Ok(Some(name));
        }
        Ok(None)
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        // A proof cites a precondition by its proposition and nothing names
        // one, so a label here would be read by nothing.
        if matches!(self.peek(), Some(Token::Ident(_))) && self.peek_next() == Some(&Token::Colon) {
            return Err(self.error(
                "a `requires` clause takes no label; a proof cites a precondition by its proposition",
            ));
        }
        let requirement = match (self.peek_ident(), self.peek_next()) {
            (Some("viewable"), Some(Token::LParen)) => self.parse_loadable_requirement()?,
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
        let segments = self.parse_current_contract_segments_inner(true)?;
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
        if !matches!(self.peek(), Some(Token::Ident(_))) {
            return false;
        }
        let open = if self.verifies_rust() {
            // A Rust callee's path, `a::b::f`, and a generic function
            // instance's type arguments, `<u32>`.
            let mut at = self.position + 1;
            while self.tokens.get(at) == Some(&Token::ColonColon)
                && matches!(self.tokens.get(at + 1), Some(Token::Ident(_)))
            {
                at += 2;
            }
            if self.tokens.get(at) == Some(&Token::LessThan) {
                at += 1;
                while matches!(self.tokens.get(at), Some(Token::Ident(_)))
                    && matches!(self.tokens.get(at + 1), Some(Token::Comma))
                {
                    at += 2;
                }
                if !matches!(self.tokens.get(at), Some(Token::Ident(_)))
                    || self.tokens.get(at + 1) != Some(&Token::GreaterThan)
                {
                    return false;
                }
                at += 2;
            }
            at
        } else if self.peek_next() == Some(&Token::ColonColon) {
            if !matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_))) {
                return false;
            }
            self.position + 3
        } else {
            self.position + 1
        };
        if self.tokens.get(open) != Some(&Token::LParen) {
            return false;
        }
        let Some(close) = self.matching_parentheses.get(open).cloned().flatten() else {
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
        tactic: bool,
    ) -> Result<CallBinderTransport, ClickError> {
        let mut callee = self.expect_ident(if tactic {
            "tactic name"
        } else {
            "call step callee"
        })?;
        if !tactic && self.verifies_rust() {
            // A Rust callee is named as its function head is: its path, and a
            // generic function's instance its type arguments,
            // `cells::write<u32>(...)`.
            callee = self.rust_step_callee(callee)?;
        } else if !tactic && self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            callee.push_str("::");
            callee.push_str(&self.expect_ident("C function name")?);
        }
        // The binder map is the last argument in both forms, as a fold's
        // field map is: a call step writes `step(callee(...), { ... })` and a
        // tactic application writes `name(..., { ... })`, where the map is
        // optional when the tactic supplies no binder.
        let form = if tactic { "name(...)" } else { "step(...)" };
        let named_contract = !tactic && self.peek() == Some(&Token::Comma);
        if named_contract && !self.contract_resource_binders.contains_key(&callee) {
            return Err(self.error(format!("unknown call contract `{callee}`")));
        }
        if !named_contract {
            self.expect(Token::LParen)?;
        }
        let mut arguments = Vec::new();
        let mut has_map = !tactic;
        while !named_contract && self.peek() != Some(&Token::RParen) {
            if tactic && self.peek() == Some(&Token::LBrace) {
                has_map = true;
                break;
            }
            arguments.push(self.parse_contract_expression()?);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        if !tactic {
            if !named_contract {
                self.expect(Token::RParen)?;
            }
            self.expect(Token::Comma)?;
        }
        let mut declared = if named_contract {
            &self.contract_resource_binders
        } else {
            &self.callee_resource_binders
        }
        .get(&callee)
        .cloned()
        .unwrap_or_default();
        if has_map && !named_contract && declared.is_empty() {
            declared = self.library_callee_value_binders(&callee)?;
        }
        if has_map {
            self.expect(Token::LBrace)?;
        }
        let mut binders: Vec<CallBinderBinding> = Vec::new();
        let mut bound = BTreeSet::new();
        let mut instances = BTreeSet::new();
        let mut type_arguments = Vec::new();
        let mut value_arguments = Vec::new();
        while has_map && self.peek() != Some(&Token::RBrace) {
            let binder = self.expect_ident("callee resource binder")?;
            self.expect(Token::Colon)?;
            if let Some(declaration) = declared.get(&binder)
                && declaration.kind == CalleeResourceBinderKind::Value
            {
                if !bound.insert(binder.clone()) {
                    return Err(self.error(format!("duplicate binder `{binder}` in the call map")));
                }
                let argument = if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let term = self.parse_declared_resource_call()?;
                    if let (ResourceClause::Declared { name, .. }, Some(expected)) =
                        (&term, &declaration.family)
                        && name != expected
                    {
                        return Err(self.error(format!(
                            "binder `{binder}` selects a `{expected}`, not a `{name}`"
                        )));
                    }
                    ValueBinderArgument::Term(term)
                } else {
                    let caller = self.expect_ident("resource term or value binder")?;
                    let Some(caller_binder) = self.names.value_binders.get(&caller) else {
                        return Err(self.error(format!(
                            "`{caller}` is not a value binder of this function; name the instance with a resource term such as `{binder}: {}(...)`",
                            declaration.family.as_deref().unwrap_or("resource")
                        )));
                    };
                    if Some(&caller_binder.resource) != declaration.family.as_ref() {
                        return Err(self.error(format!(
                            "binder `{binder}` selects a `{}`, but `{caller}` names a `{}`",
                            declaration.family.as_deref().unwrap_or("resource"),
                            caller_binder.resource
                        )));
                    }
                    ValueBinderArgument::Binder(caller)
                };
                value_arguments.push((binder, argument));
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            if let Some(declaration) = declared.get(&binder)
                && declaration.kind == CalleeResourceBinderKind::Type
            {
                if !bound.insert(binder.clone()) {
                    return Err(self.error(format!("duplicate binder `{binder}` in the call map")));
                }
                type_arguments.push((
                    binder.clone(),
                    declaration.identity,
                    self.parse_declared_resource_call()?,
                ));
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let instance = self.expect_ident("caller resource instance")?;
            crate::instrumentation::record_deterministic_work(1);
            let Some(declaration) = declared.get(&binder) else {
                return Err(self.error(format!(
                    "`{callee}` declares no resource instance binder `{binder}`"
                )));
            };
            if declaration.kind == CalleeResourceBinderKind::Produced {
                return Err(self.error(format!(
                    "`{callee}` produces `{binder}`; introduce it with `let {{ {binder}: name }} = {form}`"
                )));
            }
            if !bound.insert(binder.clone()) {
                return Err(self.error(format!("duplicate binder `{binder}` in the call map")));
            }
            let Some((identity, family)) = self.names.resource_bindings.get(&instance).cloned()
            else {
                return Err(self.unknown_instance(&instance, "resource instance"));
            };
            if let Some(expected) = &declaration.family
                && family != *expected
                && !(expected == "mutex_use" && family == "mutex_live")
                && !self.child_slot_identities.contains(&identity)
            {
                return Err(self.error(format!(
                    "binder `{binder}` expects resource `{expected}`, but `{instance}` is `{family}`"
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
                family: None,
            });
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        if has_map {
            self.expect(Token::RBrace)?;
        }
        if tactic {
            self.expect(Token::RParen)?;
            if self.peek() == Some(&Token::LBrace) {
                return Err(self.error(format!(
                    "the binder map is the last argument of a tactic application: write `{callee}(..., {{ binder: instance }})`"
                )));
            }
        }
        // An empty mutex has no protected resource to deposit. Its named
        // initialization still produces ordinary lifetime authority.
        if callee == "pthread_mutex_init" && !bound.contains("state") {
            declared.remove("state");
        }
        if let Some((missing, _)) = declared.iter().find(|(name, entry)| {
            matches!(
                entry.kind,
                CalleeResourceBinderKind::Supplied | CalleeResourceBinderKind::Type
            ) && !bound.contains(*name)
        }) {
            return Err(self.error(format!("call map omits `{callee}` binder `{missing}`")));
        }
        // Instantiate the runtime's ordinary state output from the resource
        // type argument on the selected access input. This only names a type;
        // the kernel authenticates the association and grants custody at lock.
        if callee == "pthread_mutex_lock" {
            let protected = binders
                .iter()
                .find(|b| b.binder == "access")
                .and_then(|b| self.names.resource_targets.get(&b.instance))
                .and_then(|target| match target {
                    ResourceClause::Named { resource, .. } => match resource.as_ref() {
                        ResourceClause::Declared {
                            resource_type_arguments,
                            ..
                        } => resource_type_arguments.first(),
                        _ => None,
                    },
                    _ => None,
                })
                .cloned();
            if let (Some(protected), Some(output)) = (protected, declared.get_mut("state"))
                && let ResourceClause::Declared {
                    name, type_schema, ..
                } = &protected
            {
                output.family = Some(name.clone());
                output.parameter_names.clear();
                output.resource = Some(ResourceClause::Named {
                    binding: ResourceInstanceBinding {
                        name: "state".into(),
                        identity: output.identity,
                        children: vec![],
                        schema: type_schema.clone(),
                        fields: None,
                        fold_fields: None,
                        child_bindings: None,
                        default_child_bindings: None,
                    },
                    resource: Box::new(protected),
                });
            }
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
                    "`{callee}` produces named resource instance(s) `{names}`; bind them with `let {{ ... }} = {form}`"
                )));
            }
            (Some(CallOutputPattern::Single(name)), [(produced_name, declaration)]) if tactic => {
                produced.push(self.bind_produced_call_instance(
                    &name,
                    produced_name,
                    declaration,
                    &arguments,
                )?);
            }
            (Some(CallOutputPattern::Single(_)), _) => {
                return Err(self.error(
                    "step outputs require named bindings: write `let { result: name } = step(...)` for a C value, or `let { binder: name } = step(...)` for a produced resource"
                ));
            }
            (Some(CallOutputPattern::Named(bindings)), _) => {
                let mut bound = BTreeSet::new();
                let mut names = BTreeSet::new();
                for (binder, name) in bindings {
                    if !bound.insert(binder.clone()) {
                        return Err(self.error(format!(
                            "duplicate output key `{binder}` in the call output pattern"
                        )));
                    }
                    if !names.insert(name.clone()) {
                        return Err(self.error(format!(
                            "call output pattern introduces name `{name}` twice"
                        )));
                    }
                    if binder == "result" && !tactic {
                        if declared
                            .get("result")
                            .is_some_and(|entry| entry.kind == CalleeResourceBinderKind::Produced)
                        {
                            return Err(self.error("`result` is reserved for the C value in a step output pattern; rename the produced resource binder"));
                        }
                        if self.names.contains_any(NameKind::INTEGERS, &name) {
                            return Err(self
                                .error(format!("call result name `{name}` is already in scope")));
                        }
                        self.bind_proof_name(&name, false)?;
                        result = Some(name);
                        continue;
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
                if bound.len() != produced_declarations.len() + usize::from(result.is_some()) {
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
            named_contract,
            arguments,
            binders,
            produced,
            type_arguments,
            value_arguments,
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
        if self.names.contains_any(NameKind::VALUES, name) {
            return Err(self.error("produced instance conflicts with a C or pure binding"));
        }
        self.bind_proof_name(name, true)?;
        let family = declaration.family.as_ref().ok_or_else(|| {
            self.error("produced resource assertion parameter has not been instantiated")
        })?;
        let resource = declaration.resource.as_ref().ok_or_else(|| {
            self.error("produced resource assertion parameter has no instantiated target")
        })?;
        if matches!(family.as_str(), "mutex_live" | "mutex_use" | "mutex_guard")
            && self.names.resource_bindings.contains_key(name)
        {
            return Err(self.error(format!(
                "produced mutex authority requires a fresh name; `{name}` is already bound"
            )));
        }
        let identity = match self.names.resource_bindings.get(name) {
            Some((identity, family)) => {
                if Some(family) != declaration.family.as_ref()
                    && !self.child_slot_identities.contains(identity)
                {
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
        self.names
            .bind_instance(name.to_string(), (identity, family.clone()));
        let substitutions = declaration
            .parameter_names
            .iter()
            .zip(arguments.iter())
            .map(|(parameter, argument)| (parameter.clone(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let target = substitute_resource_clause_bindings(resource, &substitutions)
            .map_err(|message| self.error(message))?;
        let ResourceClause::Named { binding, resource } = target else {
            return Err(self.error(format!(
                "produced resource binder `{produced}` has no named resource target"
            )));
        };
        self.names.set_instance_target(
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
                    default_child_bindings: None,
                },
                resource,
            },
        );
        Ok(CallBinderBinding {
            binder: produced.to_string(),
            binder_identity: declaration.identity,
            instance: name.to_string(),
            identity,
            family: Some(family.clone()),
        })
    }

    /// Runtime specifications supply their binders to the same call-map
    /// checker as sidecar declarations. Unsupported schema entries are not
    /// installed until their ordinary authority transport is implemented.
    fn record_runtime_resource_binders(
        &mut self,
        runtime: crate::languages::c::thread_runtime::CThreadRuntime,
    ) {
        use crate::languages::c::thread_runtime::{
            CThreadRuntime, MutexBinderMode, MutexOperation, MutexResourceRole,
        };
        if runtime != CThreadRuntime::ModeledPthread {
            return;
        }
        for operation in MutexOperation::ALL {
            let contract = operation.descriptor();
            let binders = self
                .callee_resource_binders
                .entry(contract.function_name.to_string())
                .or_default();
            for binder in contract.implemented_binders() {
                let family = match binder.role {
                    MutexResourceRole::Lifetime => Some("mutex_live"),
                    MutexResourceRole::Access => Some("mutex_use"),
                    MutexResourceRole::Guard => Some("mutex_guard"),
                    MutexResourceRole::State | MutexResourceRole::Storage => None,
                };
                let resource = family.map(|family| ResourceClause::Named {
                    binding: ResourceInstanceBinding {
                        name: binder.name().to_string(),
                        identity: Variable(binder.identity),
                        children: vec![],
                        schema: None,
                        fields: None,
                        fold_fields: None,
                        child_bindings: None,
                        default_child_bindings: None,
                    },
                    resource: Box::new(ResourceClause::Declared {
                        type_schema: None,
                        resource_type_arguments: Vec::new(),
                        resource_arguments: Vec::new(),
                        access: ResourceAccessMode::Own,
                        kind: ResourceKind::Token,
                        name: family.to_string(),
                        arguments: vec![ContractExpression::CFragment(CExpression::Variable(
                            "mutex".to_string(),
                        ))],
                        parameter_types: vec![C0Type::VoidPointer],
                    }),
                });
                binders.insert(
                    binder.name().to_string(),
                    CalleeResourceBinder {
                        identity: Variable(binder.identity),
                        family: family.map(str::to_string),
                        resource,
                        parameter_names: vec!["mutex".to_string(), "attributes".to_string()],
                        kind: match binder.mode {
                            MutexBinderMode::Own | MutexBinderMode::Consume => {
                                CalleeResourceBinderKind::Supplied
                            }
                            MutexBinderMode::Produce => CalleeResourceBinderKind::Produced,
                        },
                    },
                );
            }
        }
        use crate::languages::c::thread_runtime::{
            ATOMIC_INIT_NAME, ATOMIC_INIT_PAYLOAD_BINDER_ID,
        };
        self.callee_resource_binders
            .entry(ATOMIC_INIT_NAME.to_string())
            .or_default()
            .insert(
                "payload".to_string(),
                CalleeResourceBinder {
                    identity: Variable(ATOMIC_INIT_PAYLOAD_BINDER_ID),
                    family: None,
                    resource: None,
                    parameter_names: vec!["object".to_string(), "value".to_string()],
                    kind: CalleeResourceBinderKind::Type,
                },
            );
    }

    /// The value binders of the C library function `callee`, such as
    /// `strlen`'s `s`, for a call map in a program's sidecar. The library's
    /// declarations are parsed apart from the sidecar, so its binders are
    /// not in the sidecar's registry. A library module itself never asks:
    /// the library is not loaded while it is being parsed.
    fn library_callee_value_binders(
        &self,
        callee: &str,
    ) -> Result<BTreeMap<String, CalleeResourceBinder>, ClickError> {
        if self.library_module
            || crate::languages::c::syntax::library_contract_module_named(callee).is_none()
        {
            return Ok(BTreeMap::new());
        }
        crate::instrumentation::record_deterministic_work(1);
        Ok(super::validation::library_c_function_value_binders(callee)?
            .into_iter()
            .map(|(name, family)| (name, Self::value_callee_binder(family)))
            .collect())
    }

    /// A call map's entry for a value binder of family `family`.
    fn value_callee_binder(family: String) -> CalleeResourceBinder {
        CalleeResourceBinder {
            identity: Variable(0),
            family: Some(family),
            resource: None,
            parameter_names: Vec::new(),
            kind: CalleeResourceBinderKind::Value,
        }
    }

    /// Records an instance binder in the selected function/interface registry.
    /// Call maps name those declarations, including produced identities.
    /// Whether a value binder follows: `name: R(...)` where the clause is a
    /// `views` clause, or one of `R`'s arguments is `_`. An `owns` or
    /// `consumes` binder without `_` keeps naming an instance.
    fn value_binder_follows(&self, view: bool) -> bool {
        let open = self.position + 3;
        if !matches!(self.peek(), Some(Token::Ident(_)))
            || self.peek_next() != Some(&Token::Colon)
            || !matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_)))
            || self.tokens.get(open) != Some(&Token::LParen)
        {
            return false;
        }
        if view {
            return true;
        }
        let Some(close) = self.matching_parentheses.get(open).cloned().flatten() else {
            return false;
        };
        self.tokens[open + 1..close]
            .iter()
            .any(|token| matches!(token, Token::Ident(name) if name == "_"))
    }

    /// `name: R(a, _)`: the clause `R(a, s.#1)` with a placeholder at each
    /// `_`, which declaration expansion names after `R`'s parameter. The
    /// binder is recorded for `s.<parameter>` and for callers' call maps.
    fn parse_value_binder(
        &mut self,
        access: ResourceAccessMode,
        function: &str,
        parameter_names: &BTreeSet<String>,
        requirement_index: usize,
    ) -> Result<ResourceClause, ClickError> {
        if self.in_contract_definition {
            return Err(self.error(
                "a value binder `name: resource(..., _)` is supported only in a C function contract",
            ));
        }
        let name = self.expect_ident("binder name")?;
        self.expect(Token::Colon)?;
        if self.names.value_binders.contains_key(&name)
            || self.names.resource_bindings.contains_key(&name)
            || self.names.contains(NameKind::ContractBinding, &name)
            || parameter_names.contains(&name)
        {
            return Err(self.error(format!("duplicate binder `{name}`")));
        }
        // `name.parameter` would read the binder in a proposition while a
        // C place such as `owns name.field` reads the program's variable.
        if self.names.is_c_variable(&name) {
            return Err(self.error(format!(
                "value binder `{name}` takes the name of a C variable; `{name}.field` would name the binder in one clause and the variable in another; choose another name"
            )));
        }
        let resource = self.expect_ident("resource name")?;
        if matches!(
            resource.as_str(),
            "authority" | "mutex_live" | "mutex_guard" | "mutex_use" | "publisher" | "subscriber"
        ) {
            return Err(self.error(format!("`{resource}` cannot be named by a value binder")));
        }
        self.expect(Token::LParen)?;
        let mut written = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                if self.peek_ident() == Some("_") {
                    self.position += 1;
                    written.push(None);
                } else {
                    written.push(Some(self.parse_contract_expression()?));
                }
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::RParen) => break,
                    _ => return Err(self.error("expected `,` or `)` after resource argument")),
                }
            }
        }
        self.expect(Token::RParen)?;
        let arguments = written
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                argument.clone().unwrap_or_else(|| {
                    ContractExpression::CFragment(CExpression::Variable(ValueBinder::placeholder(
                        &name, index,
                    )))
                })
            })
            .collect();
        let binder = ValueBinder {
            name: name.clone(),
            resource: resource.clone(),
            arguments: written,
            requirement_index,
        };
        self.names.value_binders.insert(name.clone(), binder);
        self.names.value_binder_order.push(name.clone());
        crate::instrumentation::record_deterministic_work(1);
        self.callee_resource_binders
            .entry(function.to_string())
            .or_default()
            .insert(name, Self::value_callee_binder(resource.clone()));
        Ok(ResourceClause::Declared {
            type_schema: None,
            resource_type_arguments: Vec::new(),
            resource_arguments: Vec::new(),
            access,
            kind: ResourceKind::Token,
            name: resource,
            arguments,
            parameter_types: Vec::new(),
        })
    }

    fn record_callee_resource_binder(
        &mut self,
        function: &str,
        resource: &ResourceClause,
        parameter_names: &[String],
        kind: CalleeResourceBinderKind,
    ) {
        let ResourceClause::Named { binding, resource } = resource else {
            return;
        };
        let ResourceClause::Declared { name: family, .. } = resource.as_ref() else {
            return;
        };
        crate::instrumentation::record_deterministic_work(1);
        let registry = if self.in_contract_definition {
            &mut self.contract_resource_binders
        } else {
            &mut self.callee_resource_binders
        };
        registry.entry(function.to_string()).or_default().insert(
            binding.name.clone(),
            CalleeResourceBinder {
                identity: binding.identity,
                family: Some(family.clone()),
                resource: Some(ResourceClause::Named {
                    binding: binding.clone(),
                    resource: resource.clone(),
                }),
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
        if !matches!(self.peek(), Some(Token::Ident(_))) || self.peek_next() != Some(&Token::Colon)
        {
            let target = self.parse_owned_resource_target()?;
            return Ok(self.hold_a_hidden_record_unnamed(target));
        }
        let name = self.expect_ident("resource instance name")?;
        self.expect(Token::Colon)?;
        let rebound = rebinding
            .then(|| self.names.resource_bindings.get(&name).cloned())
            .flatten();
        if (rebound.is_none() && self.names.resource_bindings.contains_key(&name))
            || self.names.contains(NameKind::ContractBinding, &name)
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
        if resource_name == "authority" {
            return Err(self.error(
                "named authority binders are unsupported; use an ordinary unnamed authority clause",
            ));
        }
        if matches!(
            resource_name.as_str(),
            "mutex_live" | "mutex_guard" | "mutex_use"
        ) && (!self.in_function_block
            || self.in_contract_definition
            || self.in_resource_definition
            || rebinding)
        {
            return Err(self.error(format!(
                "named {resource_name} is currently supported only in C function contracts"
            )));
        }
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
        self.names
            .bind_instance(name.clone(), (identity, resource_name.clone()));
        let target = ResourceClause::Named {
            binding: ResourceInstanceBinding {
                name: name.clone(),
                identity,
                children: vec![],
                schema: None,
                fields: None,
                fold_fields: None,
                child_bindings: None,
                default_child_bindings: None,
            },
            resource: Box::new(resource),
        };
        self.names.set_instance_target(name, target.clone());
        Ok(target)
    }

    /// Whether every field of `resource` is hidden: it declares none and
    /// holds its named children's fields in a record the author does not
    /// write.
    fn is_hidden_record(&self, resource: &str) -> bool {
        self.declared_resource_fields
            .get(resource)
            .is_some_and(|fields| {
                !fields.is_empty() && fields.iter().all(|field| field.name.contains('.'))
            })
    }

    /// The binder an unnamed hidden-record resource is held under, if this
    /// exact resource is held.
    fn hidden_binder(&self, resource: &ResourceClause) -> Option<ResourceClause> {
        self.names.resource_targets
            .iter()
            .find(|(name, target)| {
                name.starts_with('#')
                    && matches!(target, ResourceClause::Named { resource: held, .. } if held.as_ref() == resource)
            })
            .map(|(_, target)| target.clone())
    }

    /// A resource whose every field is hidden has no field a contract could
    /// name, so it is held without a name: `owns pair(p);`. It is still an
    /// instance, and is bound under a name the author cannot write. Naming
    /// the same resource again, in a loop header or a proof step, is the
    /// same binder.
    #[inline(never)]
    fn hold_a_hidden_record_unnamed(&mut self, target: ResourceClause) -> ResourceClause {
        let ResourceClause::Declared { name, .. } = &target else {
            return target;
        };
        if !self.is_hidden_record(name) {
            return target;
        }
        if let Some(held) = self.hidden_binder(&target) {
            return held;
        }
        let identity = Variable(self.next_resource_identity);
        self.next_resource_identity += 1;
        let binder = format!("#{name}{}", identity.0);
        self.names
            .bind_instance(binder.clone(), (identity, name.clone()));
        let named = ResourceClause::Named {
            binding: ResourceInstanceBinding {
                name: binder.clone(),
                identity,
                children: vec![],
                schema: None,
                fields: None,
                fold_fields: None,
                child_bindings: None,
                default_child_bindings: None,
            },
            resource: Box::new(target),
        };
        self.names.set_instance_target(binder, named.clone());
        named
    }

    fn parse_owned_resource_target(&mut self) -> Result<ResourceClause, ClickError> {
        if let Some(mut target) = self
            .peek_ident()
            .and_then(|name| self.names.resource_targets.get(name))
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
                let name = self.parse_clause_label("invariant name")?;
                let proposition = self.parse_proposition()?;
                if self.peek_ident() == Some("by") {
                    return Err(self.error(
                        "invariant proofs belong to the loop; use `initialize by ...` and `preserve by ...`",
                    ));
                }
                self.expect(Token::Semicolon)?;
                Ok(vec![StructuralItem {
                    claim: proposition,
                    name,
                }])
            }
            Some(Token::Ident(kind)) => {
                Err(self.error(format!("expected `invariant`, got `{kind}`")))
            }
            Some(token) => Err(self.error(format!("expected `invariant`, got {token}"))),
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
        let scope = self.names.scope();
        let previous = execution_names.map(|_| {
            (
                std::mem::take(&mut self.names.resource_bindings),
                std::mem::take(&mut self.names.resource_targets),
            )
        });
        let introduced = match execution_names {
            Some(names) => self.introduce_execution_target_instances(&ensure, names)?,
            None => Vec::new(),
        };
        let proof = self.parse_proof_clause_or_default();
        self.names.end_declaration(scope);
        let proof = proof?;
        if let Some((bindings, targets)) = previous {
            self.names.resource_bindings = bindings;
            self.names.resource_targets = targets;
        }

        Ok((
            EnsureClause {
                proof_bindings: Vec::new(),
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
                .any(|parameter| matches!(parameter, ResourceClause::Named { binding, .. } if binding.name == *slot))
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
        for parameter in declared {
            crate::instrumentation::record_deterministic_work(1);
            let ResourceClause::Named {
                mut binding,
                resource,
            } = parameter
            else {
                unreachable!()
            };
            let ResourceClause::Declared { name: family, .. } = resource.as_ref() else {
                unreachable!()
            };
            let parameter = binding.name.clone();
            let Some(name) = bound.get(parameter.as_str()) else {
                return Err(self.error(format!(
                    "contract `{target}` proof parameter `{parameter}` needs an introduced name; \
                     write `ensures {target}(...) as {{ {parameter}: <name> }}`"
                )));
            };
            bindings.push(((*name).to_string(), (binding.identity, family.clone())));
            binding.name = (*name).to_string();
            self.names.set_instance_target(
                binding.name.clone(),
                ResourceClause::Named { binding, resource },
            );
            ordered.push((parameter, (*name).to_string()));
        }
        for (name, binding) in bindings {
            self.names.bind_instance(name, binding);
        }
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

    /// The name at the cursor when it stands alone as a proposition, as a
    /// cited fact name does.
    fn standalone_proposition_name(&self) -> Option<&str> {
        let Some(Token::Ident(name)) = self.peek() else {
            return None;
        };
        let standalone = matches!(
            self.peek_next(),
            None | Some(Token::Semicolon | Token::RParen | Token::RBrace | Token::Comma)
        ) || matches!(
            self.tokens.get(self.position + 1),
            Some(Token::Ident(next)) if matches!(next.as_str(), "and" | "or" | "implies" | "by")
        );
        standalone.then_some(name.as_str())
    }

    fn parse_proposition_atom(&mut self) -> Result<ClickProposition, ClickError> {
        if let Some(name) = self.standalone_proposition_name()
            && !self.quantifier_binders.iter().any(|binder| binder == name)
        {
            if let Some(proposition) = self.names.fact_names.get(name) {
                let proposition = proposition.clone();
                self.position += 1;
                return Ok(proposition);
            }
            if !self.names.is_bound(name) {
                if self.names.fact_names_being_proved.contains(name) {
                    return Err(self.error(format!(
                        "`{name}` names the fact this `have` is proving, so it cannot be cited inside its own proof; restate the proposition"
                    )));
                }
                if self.names.ended_fact_names.contains(name) {
                    return Err(self.error(format!(
                        "the fact name `{name}` is out of scope here: `have {name}: ...` names its fact only to the end of the block that holds it"
                    )));
                }
            }
        }
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
                            | Token::Arrow
                            | Token::Dot
                            | Token::DotDot
                    )
                )
                && !matches!(self.peek_ident(), Some("as" | "in"))
            {
                // Refuse only once the proposition reading is chosen, so the
                // refusal is not mistaken for a reason to reparse.
                if let Ok(ClickProposition::At {
                    selector,
                    proposition,
                }) = &proposition_at_snapshot
                {
                    self.refuse_result_in_snapshot_proposition(selector, proposition)?;
                }
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
                        "aligned expects a power-of-two byte alignment, got {token}"
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
            if let Some(name) = self.peek_ident()
                && let Some(value_parameters) = self.contract_value_parameter_names.get(name)
                && !value_parameters.is_empty()
            {
                return self.parse_contract_value_application();
            }
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
                    let right = self.parse_comparison_operand()?;
                    return Ok(self.specification_comparison(
                        ContractExpression::Call { name, arguments },
                        operator,
                        right,
                    ));
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
                _ if self.symbols.is_pure_function(&name) => {
                    return Ok(bool_truth(ContractExpression::Call { name, arguments }));
                }
                _ => return Ok(ClickProposition::PredicateCall { name, arguments }),
            }
        }

        self.parse_proposition_comparison()
    }

    /// A named contract with value parameters attached to a function value,
    /// `Adds(f, { amount: k })`. The map names every value parameter once;
    /// the proposition takes the values in declaration order.
    fn parse_contract_value_application(&mut self) -> Result<ClickProposition, ClickError> {
        let name = self.expect_ident("contract name")?;
        let declared = self
            .contract_value_parameter_names
            .get(&name)
            .cloned()
            .unwrap_or_default();
        self.expect(Token::LParen)?;
        let function = self.parse_contract_expression()?;
        if self.peek() != Some(&Token::Comma) {
            return Err(self.error(format!(
                "contract `{name}` takes its value parameters after the function, as in \
                 `{name}(f, {{ {}: value }})`",
                declared.join(": value, ")
            )));
        }
        self.position += 1;
        self.expect(Token::LBrace)?;
        let mut values = BTreeMap::new();
        while self.peek() != Some(&Token::RBrace) {
            let parameter = self.expect_ident("contract value parameter")?;
            if !declared.contains(&parameter) {
                return Err(self.error(format!(
                    "contract `{name}` has no value parameter `{parameter}`"
                )));
            }
            self.expect(Token::Colon)?;
            let value = self.parse_contract_expression()?;
            if values.insert(parameter.clone(), value).is_some() {
                return Err(self.error(format!(
                    "contract value parameter `{parameter}` is bound twice"
                )));
            }
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RBrace)?;
        self.expect(Token::RParen)?;
        let mut arguments = vec![function];
        for parameter in &declared {
            arguments.push(values.remove(parameter).ok_or_else(|| {
                self.error(format!(
                    "contract `{name}` needs a value for its parameter `{parameter}`"
                ))
            })?);
        }
        Ok(ClickProposition::PredicateCall { name, arguments })
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
            /// Where the bindings this binder makes and hides start.
            names: NameScope,
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
                        self.refuse_bool_literal_binder(&name)?;
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
                        // Like a proof binder, the quantified variable hides
                        // the value binder, fact and resource instance of
                        // its name, and the field a resource body reads by
                        // it, until its body ends.
                        let names = self.names.scope();
                        self.names.hide_for_proof_binder(&name, false);
                        self.names.hide_resource_field(&name);
                        match &click_type {
                            ClickType::Integer => {
                                self.names
                                    .set_scoped(NameKind::ContractBinding, &name, false);
                                self.names
                                    .set_scoped(NameKind::IntegerParameter, &name, true);
                                self.integer_literal_context = true;
                            }
                            ClickType::C(_) | ClickType::CObjectPointer { .. } => {
                                self.names
                                    .set_scoped(NameKind::IntegerParameter, &name, false);
                                self.names.set_scoped(NameKind::IntegerLet, &name, false);
                                self.names
                                    .set_scoped(NameKind::ContractBinding, &name, false);
                                self.integer_literal_context = false;
                            }
                            ClickType::Algebraic(_) => {
                                self.names
                                    .set_scoped(NameKind::IntegerParameter, &name, false);
                                self.names.set_scoped(NameKind::IntegerLet, &name, false);
                                self.names
                                    .set_scoped(NameKind::ContractBinding, &name, true);
                                self.integer_literal_context = false;
                            }
                            ClickType::Parameter(_) => {
                                return Err(self.error(
                                    "quantifier type must be a concrete C, Integer, or algebraic type",
                                ));
                            }
                        }
                        self.quantifier_binders.push(name.clone());
                        scopes.push(Scope {
                            forall,
                            click_type,
                            name,
                            negations: if group_len == 0 { negations } else { 0 },
                            previous_integer_context,
                            names,
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
                    self.quantifier_binders.pop();
                    self.names.end(scope.names);
                    self.integer_literal_context = scope.previous_integer_context;
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
        let name = self.expect_reference_name(expected_name)?;
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
                        return Err(self.error(format!("expected `,` or `)`, got {token}")));
                    }
                    None => return Err(self.error("expected `,` or `)`, got end of input")),
                }
            }
        }
        self.expect(Token::RParen)?;
        let arguments = self.spread_slice_arguments(&name, arguments)?;
        Ok((name, arguments))
    }

    fn parse_proposition_comparison(&mut self) -> Result<ClickProposition, ClickError> {
        let left = self.parse_comparison_operand()?;
        // A value written alone where a proposition is expected is a `bool`
        // claim: `flag` means `flag == true`. Type checking refuses it when
        // the value is not a `bool`, so an integer is never read with C's
        // nonzero truth.
        if self.at_proposition_end() {
            return Ok(bool_truth(left));
        }
        let operator = self.parse_comparison_operator("proposition")?;
        let right = self.parse_comparison_operand()?;

        Ok(self.specification_comparison(left, operator, right))
    }

    /// A comparison as the file's specification arithmetic reads it. Under
    /// `arithmetic "integer";` a comparison that does arithmetic, or that
    /// compares an Integer with a machine value, compares exact Integers:
    /// each machine operand of its arithmetic is observed with
    /// `to_integer`, so `x + 1 > x` reads
    /// `to_integer(x) + 1 > to_integer(x)`. A population count is a
    /// quantity, so a comparison with a `count(...)` operand compares
    /// Integers too. A comparison with a pointer operand keeps its C
    /// meaning.
    fn specification_comparison(
        &self,
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
    ) -> ClickProposition {
        if self.integer_arithmetic && operator != ComparisonOperator::In {
            let left_integer = self.integer_operand(&left);
            let right_integer = self.integer_operand(&right);
            let mixed = left_integer != right_integer;
            let arithmetic = has_arithmetic_spine(&left) || has_arithmetic_spine(&right);
            let counted = has_count_operand(&left) || has_count_operand(&right);
            if !(left_integer && right_integer)
                && (mixed || arithmetic || counted)
                && !self.has_pointer_operand(&left)
                && !self.has_pointer_operand(&right)
            {
                return ClickProposition::Comparison {
                    left: self.observe_machine_operands(left),
                    operator,
                    right: self.observe_machine_operands(right),
                };
            }
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        }
    }

    /// Whether `expression` is already an exact Integer: an Integer
    /// binding, a `to_integer` observation, or arithmetic over them.
    fn integer_operand(&self, expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                self.integer_operand(left) || self.integer_operand(right)
            }
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.integer_operand(inner),
            leaf => self.integer_leaf(leaf),
        }
    }

    fn integer_leaf(&self, expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Call { name, .. } => {
                name == "to_integer"
                    || crate::surface::integer_truncation::is_integer_truncation(name)
                    || self.integer_function_names.contains(name)
            }
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.names.contains_any(NameKind::INTEGERS, name)
            }
            _ => false,
        }
    }

    /// Whether the function header whose parameter list opens at `start`
    /// declares `-> Integer`: the parenthesis is matched, then the result
    /// type follows the arrow.
    fn declares_integer_result(&self, start: usize) -> bool {
        if self.tokens.get(start) != Some(&Token::LParen) {
            return false;
        }
        let Some(close) = self.matching_parentheses.get(start).copied().flatten() else {
            return false;
        };
        self.tokens.get(close + 1) == Some(&Token::Arrow)
            && matches!(self.tokens.get(close + 2), Some(Token::Ident(name)) if name == "Integer")
    }

    /// Whether an arithmetic operand of `expression` is a pointer parameter
    /// or an `address(p)` of a pointer.
    fn has_pointer_operand(&self, expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                self.has_pointer_operand(left) || self.has_pointer_operand(right)
            }
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.has_pointer_operand(inner),
            ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .names
                .c_parameter_types
                .get(name)
                .is_some_and(|c_type| c_type.is_pointer()),
            ContractExpression::CFragment(cast @ CExpression::Cast { .. })
            | ContractExpression::CUnary {
                lowered: cast @ CExpression::Cast { .. },
                ..
            } => self.address_casts.contains(cast),
            _ => false,
        }
    }

    /// `expression` with each machine operand of its arithmetic observed
    /// with `to_integer`. Unsuffixed literals take the Integer type from
    /// context, and Integer operands are left as they are.
    fn observe_machine_operands(&self, expression: ContractExpression) -> ContractExpression {
        match expression {
            ContractExpression::Add(left, right) => ContractExpression::Add(
                Box::new(self.observe_machine_operands(*left)),
                Box::new(self.observe_machine_operands(*right)),
            ),
            ContractExpression::Subtract(left, right) => ContractExpression::Subtract(
                Box::new(self.observe_machine_operands(*left)),
                Box::new(self.observe_machine_operands(*right)),
            ),
            ContractExpression::Multiply(left, right) => ContractExpression::Multiply(
                Box::new(self.observe_machine_operands(*left)),
                Box::new(self.observe_machine_operands(*right)),
            ),
            ContractExpression::Negate(inner) => {
                ContractExpression::Negate(Box::new(self.observe_machine_operands(*inner)))
            }
            ContractExpression::Old(inner) if has_arithmetic_spine(&inner) => {
                ContractExpression::Old(Box::new(self.observe_machine_operands(*inner)))
            }
            ContractExpression::At {
                selector,
                expression,
            } if has_arithmetic_spine(&expression) || self.integer_operand(&expression) => {
                ContractExpression::At {
                    selector,
                    expression: Box::new(self.observe_machine_operands(*expression)),
                }
            }
            ContractExpression::IntegerLiteral(value) => ContractExpression::IntegerLiteral(value),
            // An Integer operand, including one under `old` or `at`, is
            // already exact.
            leaf if self.integer_operand(&leaf) => leaf,
            leaf => ContractExpression::Call {
                name: "to_integer".to_string(),
                arguments: vec![leaf],
            },
        }
    }

    /// A comparison operand whose outermost operator is `&`, `|` or `^` must
    /// be parenthesized. C binds comparisons tighter than these operators and
    /// Click binds them looser, so `x & 1 == 0` would read differently to a C
    /// reader than it verifies. Rust groups them as Click does, so a sidecar
    /// verifying Rust needs no parentheses.
    fn parse_comparison_operand(&mut self) -> Result<ContractExpression, ClickError> {
        let start = self.position;
        let operand = self.parse_contract_expression()?;
        if self.verifies_rust() {
            return Ok(operand);
        }
        let operator = match &operand {
            ContractExpression::BitwiseAnd(..) => "&",
            ContractExpression::BitwiseOr(..) => "|",
            ContractExpression::BitwiseXor(..) => "^",
            _ => return Ok(operand),
        };
        let parenthesized = self.tokens.get(start) == Some(&Token::LParen)
            && self.matching_parentheses.get(start).copied().flatten() == Some(self.position - 1);
        if parenthesized {
            return Ok(operand);
        }
        Err(self.error(format!(
            "parenthesize a `{operator}` operand of a comparison: C groups \
             `a {operator} b == c` as `a {operator} (b == c)` and Click as \
             `(a {operator} b) == c`, so write `(a {operator} b) == c`"
        )))
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
                "expected comparison operator in `{clause}`, got {token}"
            ))),
        }
    }

    fn parse_by_clause(&mut self) -> Result<SourceProof, ClickError> {
        let start = self.here();
        let owner = self.proof_clause_owner.take();
        self.expect_ident_spelling("by")?;
        let scope = self.names.scope();
        let previous_proof_let_names = self.names.take(NameKind::ProofBinder);
        let result = self.parse_by_clause_body();
        self.names.end(scope);
        self.names
            .replace(NameKind::ProofBinder, previous_proof_let_names);
        // A `;` after a closing brace ends nothing; accept it after a block
        // proof as everywhere else, though it is never required.
        if result.is_ok()
            && self.position > 0
            && self.tokens.get(self.position - 1) == Some(&Token::RBrace)
        {
            self.skip_redundant_semicolon();
        }
        if result.is_ok() {
            self.record_proof_clause(start, owner);
        }
        result
    }

    /// Records the proof clause from `start` to the token before the cursor.
    fn record_proof_clause(
        &mut self,
        start: Option<SourcePosition>,
        owner: Option<SourcePosition>,
    ) {
        if let Some(start) = start
            && let Some(last) = self
                .position
                .checked_sub(1)
                .and_then(|last| self.positions.get(last))
        {
            self.proof_clause_spans.push(ProofClauseSpan {
                start,
                last: last.clone(),
                owner,
            });
        }
    }

    /// Makes `name` a proof binder of a value or a resource instance. The
    /// newest binding of a name wins everywhere it is read: a fact or a
    /// resource of the same spelling is hidden until the binder's block
    /// ends, so a citation, a value and a resource argument all read the
    /// same binding. A C variable cannot be hidden: execution keeps reading
    /// the program's variable, so a proof binder of its name would change
    /// what the proof's propositions mean without changing what runs.
    fn bind_proof_name(&mut self, name: &str, resource: bool) -> Result<(), ClickError> {
        if resource
            && self.names.is_c_variable(name)
            && self.names.resource_bindings.contains_key(name)
        {
            return Err(self.error(format!(
                "`{name}` names both a C variable and the contract's resource instance `{name}`; a proof binder cannot hide the C variable, so the instance cannot be bound again under this name; rename the instance in the contract"
            )));
        }
        if self.names.is_c_variable(name) {
            return Err(self.error(format!(
                "`{name}` names a C variable here; a proof binder cannot hide it, since execution keeps reading the program's `{name}`; choose another name"
            )));
        }
        self.names.hide_for_proof_binder(name, resource);
        Ok(())
    }

    /// The refusal for a name that binds no resource instance here: one
    /// whose binding block has ended is refused as out of scope.
    fn unknown_instance(&self, name: &str, kind: &str) -> ClickError {
        if self.names.ended_instance_names.contains(name) {
            self.error(format!(
                "the resource instance `{name}` is out of scope here: a name bound inside a block names its instance only to the end of that block; bind it before the block, or name it in the contract"
            ))
        } else {
            self.error(format!("unknown {kind} `{name}`"))
        }
    }

    fn starts_standalone_smart_proof(&self) -> bool {
        match self.peek_ident() {
            Some("auto") => true,
            // Route the old bare spelling through the missing-parentheses diagnostic.
            Some("simp") => self.peek_next() != Some(&Token::LParen),
            _ => false,
        }
    }

    fn parse_by_clause_body(&mut self) -> Result<SourceProof, ClickError> {
        if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let proof = match self.peek() {
                Some(Token::Ident(name))
                    if is_tactic_name(name) && self.starts_standalone_smart_proof() =>
                {
                    let open = self.positions[self.position - 1].clone();
                    let start = self.positions[self.position].clone();
                    let tactic = self.parse_tactic()?;
                    self.record_proof_block(open, vec![start]);
                    self.expect(Token::RBrace)?;
                    SourceProof::Tactic(tactic)
                }
                Some(Token::RBrace) => {
                    return Err(self.error("`by` block must contain at least one tactic"));
                }
                Some(_) => {
                    let tactics = self.parse_tactic_list_to_rbrace()?;
                    self.expect(Token::RBrace)?;
                    SourceProof::Script(tactics)
                }
                None => return Err(self.error("expected tactic, got end of input")),
            };
            return Ok(proof);
        }

        // `auto()` uses whole-proof automation. Other single calls are one-step scripts.
        if self.starts_standalone_smart_proof() {
            let first = self.position;
            let tactic = self.parse_tactic()?;
            self.record_implicit_proof(first);
            return Ok(SourceProof::Tactic(tactic));
        }
        match self.peek() {
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::LParen) => {
                Ok(SourceProof::Script(vec![self.parse_implicit_proof_tactic()?]))
            }
            Some(Token::Ident(name)) => Err(self.error(format!(
                "expected a proof after `by`, got `{name}`: write one tactic call such as `{name}();`, or a block `{{ ... }}`"
            ))),
            Some(token) => Err(self.error(format!("expected a proof after `by`, got {token}"))),
            None => Err(self.error("expected a proof after `by`, got end of input")),
        }
    }

    fn parse_loop_phase_proof(&mut self) -> Result<SourceProof, ClickError> {
        let proof = self.parse_by_clause()?;
        // A lone phase `simp()` owns the generated execution and closure steps,
        // with either brace spelling. Keep it out of per-step source capture.
        if matches!(&proof, SourceProof::Script(tactics) if matches!(tactics.as_slice(), [ProofTactic::Simp]))
        {
            Ok(SourceProof::Tactic(SmartTactic::Simp))
        } else {
            Ok(proof)
        }
    }

    fn parse_proof_clause_or_default(&mut self) -> Result<SourceProof, ClickError> {
        if self.peek_ident() == Some("by") {
            self.parse_by_clause()
        } else {
            let start = self.here();
            let owner = self.proof_clause_owner.take();
            self.expect(Token::Semicolon)?;
            self.record_proof_clause(start, owner);
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
        self.bind_resource_child_names(parent, None, bindings, introduce)
    }

    /// Binds the names of an unfold or fold pattern over `parent`, whose
    /// resource is `family` when the instance recorded one other than its
    /// clause's.
    fn bind_resource_child_names(
        &mut self,
        parent: &ResourceClause,
        family: Option<&str>,
        bindings: Vec<(String, String)>,
        introduce: bool,
    ) -> Result<Vec<(String, String, Variable)>, ClickError> {
        let ResourceClause::Declared { name: written, .. } = parent else {
            return Err(self.error("child bindings require a declared resource family"));
        };
        let family = &family.map_or_else(|| written.clone(), str::to_string);
        let mut result = Vec::new();
        let mut slots = BTreeSet::new();
        let mut names = BTreeSet::new();
        for (slot, name) in bindings {
            if !slots.insert(slot.clone()) || !names.insert(name.clone()) {
                return Err(self.error("duplicate child slot or resource name"));
            }
            if self.names.contains(NameKind::ContractBinding, &name) {
                return Err(self.error("child resource name conflicts with a C or pure binding"));
            }
            self.bind_proof_name(&name, true)?;
            // A mixed unfold pattern also names C-valued fields. They are
            // ordinary proof values, not references to owned resources.
            let scalar_field = self
                .declared_resource_fields
                .get(family)
                .is_some_and(|fields| {
                    fields.iter().any(|field| {
                        field.name == slot && matches!(field.click_type, ClickType::C(_))
                    })
                });
            if introduce && scalar_field {
                if self.names.resource_bindings.contains_key(&name) {
                    return Err(self.error("field output conflicts with a resource binding"));
                }
                let identity = Variable(self.next_resource_identity);
                self.next_resource_identity += 1;
                self.names.insert(NameKind::ProofBinder, name.clone());
                result.push((slot, name, identity));
                continue;
            }
            let existing = self.names.resource_bindings.get(&name).cloned();
            let identity = if let Some((identity, _)) = &existing {
                // A child slot's resource comes from the parent's matched
                // arm, which the parser cannot resolve; declaration
                // expansion checks the supplied instance against it.
                *identity
            } else if introduce {
                let identity = Variable(self.next_resource_identity);
                self.next_resource_identity += 1;
                identity
            } else {
                return Err(self.unknown_instance(&name, "child resource"));
            };
            if introduce {
                self.child_slot_identities.insert(identity);
                // A name already bound, such as the contract's `produces
                // whole: ...` that the unfold's child becomes, keeps the
                // resource it was declared with: its fields are that
                // resource's, not the parent's, when a later `have` reads
                // `whole.model`. A new binder takes the slot's resource when
                // every arm of the parent's declaration agrees on it, so an
                // unfold of the child reads the child's own fields and
                // slots. Otherwise it records the parent, which declaration
                // expansion replaces with the slot's resource.
                let recorded = existing.map_or_else(
                    || {
                        self.declared_resource_child_slots
                            .get(family)
                            .and_then(|slots| slots.get(&slot).cloned().flatten())
                            .unwrap_or_else(|| family.clone())
                    },
                    |(_, family)| family,
                );
                self.names.bind_instance(name.clone(), (identity, recorded));
                self.names.set_instance_target(
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
                            default_child_bindings: None,
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
            "let" => self.parse_let_proof_tactic(),
            "both" => self.parse_both_proof_tactic(),
            "if" => self.parse_if_proof_tactic(),
            "induct" if !self.tactic_names.contains(&name) => self.parse_induct_proof_tactic(),
            _ => self.parse_other_proof_tactic(name),
        }
    }

    // `let ... = fold(...)` has a large parsing frame. Keep it out of the
    // common tactic dispatcher so nested proof bodies fit the bounded stack.
    #[inline(never)]
    fn parse_let_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let output = self.parse_let_output_pattern()?;
        self.expect(Token::Equal)?;
        if self.peek_ident() == Some("step") {
            self.position += 1;
            self.expect(Token::LParen)?;
            if self.peek() == Some(&Token::RParen) {
                let CallOutputPattern::Named(bindings) = output else {
                    return Err(self.error("step outputs require named bindings: write `let { result: name } = step()`"));
                };
                let [(binder, name)] = bindings.as_slice() else {
                    return Err(self.error(
                        "`step()` has one value output: write `let { result: name } = step()`",
                    ));
                };
                if binder != "result" {
                    return Err(self.error("`step()` has only the `result` output"));
                }
                let name = name.clone();
                // A result is a proof binder: it hides an earlier proof
                // binding of its name. Contract and theorem names stay
                // reserved, and a C variable cannot be hidden.
                if self.names.contains_any(NameKind::INTEGERS, &name) {
                    return Err(
                        self.error(format!("step result name `{name}` is already in scope"))
                    );
                }
                self.bind_proof_name(&name, false)?;
                self.position += 1;
                return self.parse_step_proof(ProofTactic::StepBind(name));
            }
            if !self.call_binder_transport_follows() && self.peek_next() != Some(&Token::Comma) {
                return Err(self.error(
                            "a call output binding requires a call and binder map: `let { result: name } = step(callee(...), { binder: instance })`",
                        ));
            }
            let transport = self.parse_call_binder_transport(Some(output), false)?;
            self.expect(Token::RParen)?;
            return self.parse_step_proof(ProofTactic::StepCall(transport));
        }
        if let Some(name) = self.peek_ident()
            && self.tactic_names.contains(name)
            && self.peek_next() == Some(&Token::LParen)
        {
            let application = self.parse_call_binder_transport(Some(output), true)?;
            self.expect(Token::Semicolon)?;
            return Ok(ProofTactic::UserTactic(application));
        }
        if self.peek_ident() == Some("unfold") {
            let CallOutputPattern::Named(bindings) = output else {
                return Err(self.error(
                            "resource unfold outputs require a labeled pattern: `let { slot: name } = unfold(resource)`",
                        ));
            };
            self.position += 1;
            self.expect(Token::LParen)?;
            let target = self.parse_owned_resource_target()?;
            let target = self.hidden_binder(&target).unwrap_or(target);
            // A declared resource's unfold names the `let ... where`
            // witnesses its opened body binds.
            if matches!(target, ResourceClause::Declared { .. }) {
                self.expect(Token::RParen)?;
                self.expect(Token::Semicolon)?;
                let mut seen = BTreeSet::new();
                for (slot, name) in &bindings {
                    if !seen.insert(name.clone()) {
                        return Err(self.error(format!(
                            "unfold witness name `{name}` is bound twice; the names in `let {{ ... }} = unfold(...)` must differ"
                        )));
                    }
                    let _ = slot;
                    self.bind_proof_name(name, false)?;
                    self.names.insert(NameKind::ProofBinder, name.clone());
                }
                return Ok(ProofTactic::UnfoldWitnesses {
                    resource: target,
                    names: bindings,
                });
            }
            let ResourceClause::Named {
                mut binding,
                resource,
            } = target
            else {
                return Err(self.error("resource unfold outputs require a named resource"));
            };
            self.expect(Token::RParen)?;
            // A child an earlier unfold introduced keeps its parent's clause
            // as its target, since the parser cannot instantiate the slot's
            // arguments; the resource it recorded is the slot's.
            let family = self
                .names
                .resource_bindings
                .get(&binding.name)
                .map(|(_, family)| family.clone());
            binding.child_bindings = Some(
                self.bind_resource_child_names(&resource, family.as_deref(), bindings, true)?
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
        self.parse_fold_construction(Some(name))
    }

    /// `fold(resource, { field: value }, { slot: child })` after its opening
    /// parenthesis. `let name = fold(...)` binds the instance to `name`. A
    /// resource whose every field is hidden is folded without a name,
    /// `fold(pair(p), { first: c });`, under the binder it is held by.
    #[inline(never)]
    fn parse_fold_construction(&mut self, name: Option<String>) -> Result<ProofTactic, ClickError> {
        let resource = self.parse_resource_target(ResourceAccessMode::Own)?;
        let ResourceClause::Declared {
            name: resource_name,
            ..
        } = &resource
        else {
            return Err(self.error("fold construction requires a declared resource"));
        };
        let name = match name {
            Some(name) => name,
            None => match self.hidden_binder(&resource) {
                Some(ResourceClause::Named { binding, .. }) => binding.name,
                _ => format!("#{resource_name}{}", self.next_resource_identity),
            },
        };
        if self.names.contains_any(NameKind::VALUES, &name) {
            return Err(self.error("fold result conflicts with a C or pure binding"));
        }
        self.bind_proof_name(&name, true)?;
        let identity = if let Some((identity, previous)) = self.names.resource_bindings.get(&name) {
            if previous != resource_name && !self.child_slot_identities.contains(identity) {
                return Err(self.error("fold result changes the named resource family"));
            }
            *identity
        } else {
            let identity = Variable(self.next_resource_identity);
            self.next_resource_identity += 1;
            identity
        };
        // A resource whose every field is hidden has no field the proof
        // could write, so its one brace is the child map, and a map whose
        // every child defaults by name may be left out with it.
        let declared = self
            .declared_resource_fields
            .get(resource_name)
            .cloned()
            .unwrap_or_default();
        let only_hidden =
            !declared.is_empty() && declared.iter().all(|field| field.name.contains('.'));
        if !(only_hidden && self.peek() == Some(&Token::RParen)) {
            self.expect(Token::Comma)?;
        }
        let mut fields = Vec::new();
        if !only_hidden {
            self.expect(Token::LBrace)?;
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
        }
        let child_bindings = if only_hidden && self.peek() == Some(&Token::LBrace) {
            self.parse_resource_child_bindings(&resource, false)?
        } else if !only_hidden && self.peek() == Some(&Token::Comma) {
            self.position += 1;
            self.parse_resource_child_bindings(&resource, false)?
        } else {
            Vec::new()
        };
        let default_child_bindings =
            self.default_fold_child_bindings(resource_name, &name, &child_bindings);
        let mut hidden_sources = child_bindings.clone();
        hidden_sources.extend(default_child_bindings.iter().cloned());
        self.fill_hidden_fold_fields(&declared, &hidden_sources, &mut fields);
        self.expect(Token::RParen)?;
        let binding = ResourceInstanceBinding {
            name: name.clone(),
            identity,
            children: vec![],
            schema: None,
            fields: None,
            fold_fields: None,
            child_bindings: Some(Vec::new().into()),
            default_child_bindings: None,
        };
        self.names
            .bind_instance(name.clone(), (identity, resource_name.clone()));
        self.names.set_instance_target(
            name,
            ResourceClause::Named {
                binding: binding.clone(),
                resource: Box::new(resource.clone()),
            },
        );
        // Like any fold, a construction may prove the body facts it leaves
        // open with `by` or `requires` entries.
        self.parse_step_proof(ProofTactic::FoldResource(ResourceClause::Named {
            binding: ResourceInstanceBinding {
                fold_fields: Some(fields),
                child_bindings: Some(child_bindings.into()),
                default_child_bindings: (!default_child_bindings.is_empty())
                    .then(|| default_child_bindings.into()),
                ..binding
            },
            resource: Box::new(resource),
        }))
    }

    /// The child slots of `family` that a fold's map left out and that an
    /// in-scope resource of the same name could fill: `{ left: left }` is
    /// written `{}` or not at all. A name the map already uses, the fold's
    /// own result, or a name that is also a pure binding fills nothing.
    /// Which of these the fold keeps is decided by the arm it selects.
    #[inline(never)]
    fn default_fold_child_bindings(
        &self,
        family: &str,
        result: &str,
        explicit: &[(String, String, Variable)],
    ) -> Vec<(String, String, Variable)> {
        let Some(slots) = self.declared_resource_child_slots.get(family) else {
            return Vec::new();
        };
        slots
            .keys()
            .filter(|slot| {
                slot.as_str() != result
                    && !explicit
                        .iter()
                        .any(|(bound, name, _)| bound == *slot || name == *slot)
                    && !self.names.contains(NameKind::ContractBinding, slot)
                    && !self.names.contains(NameKind::IntegerParameter, slot)
                    && !self.names.contains(NameKind::IntegerLet, slot)
                    && !self.names.contains(NameKind::ProofBinder, slot)
            })
            .filter_map(|slot| {
                let (identity, _) = self.names.resource_bindings.get(slot)?;
                Some((slot.clone(), slot.clone(), *identity))
            })
            .collect()
    }

    /// A hidden field `slot.field` is the field of the child bound to
    /// `slot`, so a fold supplies it from that child and the proof never
    /// writes it.
    #[inline(never)]
    fn fill_hidden_fold_fields(
        &self,
        declared: &[ResourceFieldDefinition],
        child_bindings: &[(String, String, Variable)],
        fields: &mut Vec<(String, ContractExpression)>,
    ) {
        for field in declared {
            let Some((slot, child_field)) = field.name.split_once('.') else {
                continue;
            };
            if fields.iter().any(|(name, _)| name == &field.name) {
                continue;
            }
            let Some((_, child, identity)) =
                child_bindings.iter().find(|(bound, _, _)| bound == slot)
            else {
                continue;
            };
            let Some((_, family)) = self.names.resource_bindings.get(child) else {
                continue;
            };
            fields.push((
                field.name.clone(),
                ContractExpression::ResourceField(ResourceFieldAccess {
                    owner: child.clone(),
                    resource_name: family.clone(),
                    identity: *identity,
                    children: vec![],
                    field: child_field.to_string(),
                    field_index: 0,
                    click_type: None,
                }),
            ));
        }
    }

    /// `obtain (name: Type, ...) { P }` opens an available
    /// `exists (name: Type, ...) { P }`, binding its typed names.
    fn parse_obtain(&mut self) -> Result<ProofTactic, ClickError> {
        self.expect(Token::LParen)?;
        let mut bindings = Vec::new();
        loop {
            let name = self.expect_ident("existential binding name")?;
            if is_c_type_keyword(&name)
                || self.names.contains(NameKind::ProofBinder, &name)
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
        self.expect(Token::LBrace)?;
        let previous_integer_context = self.integer_literal_context;
        for (name, click_type) in &bindings {
            self.bind_proof_name(name, false)?;
            match click_type {
                ClickType::Integer => {
                    self.names
                        .set_scoped(NameKind::ContractBinding, name, false);
                    self.names.set_scoped(NameKind::IntegerLet, name, true);
                    self.integer_literal_context = true;
                }
                ClickType::C(_) | ClickType::CObjectPointer { .. } | ClickType::Algebraic(_) => {
                    self.names.set_scoped(NameKind::IntegerLet, name, false);
                    self.names.set_scoped(NameKind::ContractBinding, name, true);
                    self.integer_literal_context = false;
                }
                ClickType::Parameter(_) => unreachable!("rejected above"),
            }
        }
        let body = self.parse_proposition()?;
        self.expect(Token::RBrace)?;
        self.skip_redundant_semicolon();
        self.integer_literal_context = previous_integer_context;
        self.names.extend(
            NameKind::ProofBinder,
            bindings.iter().map(|(name, _)| name.clone()),
        );
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
        // The left blocks that hold only a nested `both`, outermost first.
        let mut nested_left_blocks = Vec::new();
        self.expect(Token::LBrace)?;
        let mut left_tactics = if self.peek_ident() == Some("both") {
            nested_left_blocks.push((
                self.positions[self.position - 1].clone(),
                self.positions[self.position].clone(),
            ));
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
                nested_left_blocks.push((
                    self.positions[self.position - 1].clone(),
                    self.positions[self.position].clone(),
                ));
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
                if let Some((open, start)) = nested_left_blocks.pop() {
                    self.record_proof_block(open, vec![start]);
                }
                self.expect(Token::RBrace)?;
            }
        }
        self.skip_redundant_semicolon();
        Ok(current.expect("the both tactic chain has a root"))
    }

    /// `have P;`, `have P by simp();` or `have P by { ... }`, after the word
    /// `have`. Out of line: the tactic dispatcher that calls it is on the
    /// recursive proof-parsing path and keeps none of this in its frame.
    #[inline(never)]
    fn parse_have_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        // `have name: P` names the fact for the rest of the block: a later
        // step may cite it as `name` where it would restate `P`. `name:` is
        // never the start of a proposition.
        let name = if let (Some(Token::Ident(name)), Some(Token::Colon)) =
            (self.peek(), self.peek_next())
        {
            let name = name.clone();
            self.refuse_fact_name_in_scope(&name)?;
            self.position += 2;
            Some(name)
        } else {
            None
        };
        if let Some(name) = &name {
            self.names.fact_names_being_proved.insert(name.clone());
        }
        let have = self.parse_have_after_name();
        if let Some(name) = &name {
            self.names.fact_names_being_proved.remove(name);
        }
        let have = have?;
        if let (Some(name), ProofTactic::Have(have)) = (name, &have) {
            self.names.ended_fact_names.remove(&name);
            let previous = self
                .names
                .fact_names
                .insert(name.clone(), have.proposition.clone());
            self.names.undo.push(ShadowRestore::Fact { name, previous });
        }
        Ok(have)
    }

    /// A fact name is read only where a proposition stands, but a value
    /// spelled the same would read as a proposition there too (a `bool`), so
    /// a name that already binds anything visible is refused.
    fn refuse_fact_name_in_scope(&self, name: &str) -> Result<(), ClickError> {
        self.refuse_bool_literal_binder(name)?;
        if self.names.fact_names.contains_key(name)
            || self.names.fact_names_being_proved.contains(name)
            || self.names.is_bound(name)
        {
            return Err(self.error(format!(
                "`have {name}: ...` names a fact `{name}`, but `{name}` already names something in scope; choose another name"
            )));
        }
        Ok(())
    }

    /// `have P ...` after any `name:`.
    fn parse_have_after_name(&mut self) -> Result<ProofTactic, ClickError> {
        let proposition = self.parse_proposition()?;
        // A `have` states a fact at the current point, so an omitted
        // proof is `simp` here; it never executes C to reach the fact.
        if self.peek() == Some(&Token::Semicolon) {
            self.position += 1;
            return Ok(ProofTactic::Have(ProofHave {
                proposition,
                proof: have_proof_as_written_in_full(SourceProof::Tactic(SmartTactic::Simp)),
            }));
        }
        // `have P by auto();` proves the fact where it is stated: with no C
        // to run toward the fact, `auto` is the solver.
        let proof = self.parse_by_clause()?;
        self.skip_redundant_semicolon();
        // `have P;`, `have P by simp();` and `have P by { simp(); }` are
        // one proof step. They are one syntax tree too, so every
        // consumer proves and reports them the same way.
        Ok(ProofTactic::Have(ProofHave {
            proposition,
            proof: have_proof_as_written_in_full(proof),
        }))
    }

    // Conjunction spines do not retain the larger frames for loop, resource,
    // and leaf syntax at every child-proof level.
    #[inline(never)]
    fn parse_other_proof_tactic(&mut self, name: String) -> Result<ProofTactic, ClickError> {
        if name == "have" {
            return self.parse_have_tactic();
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
            // `open(r) { ... } by ...`: the proof of the one body fact the
            // closing fold leaves open, as after `fold(r) by`.
            let close_proof = if self.peek_ident() == Some("by") {
                self.position += 1;
                if self.peek_ident() == Some("auto") && self.peek_next() == Some(&Token::LParen) {
                    return Err(self.error(
                        "`open(...) { ... } by auto()` is `open(...) { ... }`: its closing fold's open body facts already go to `auto`",
                    ));
                }
                Some(self.parse_step_proof_body()?)
            } else {
                None
            };
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::Open(ProofOpen {
                resource,
                tactics,
                close_proof,
            }));
        }
        if name == "cases" {
            // One arm per disjunct, each naming the disjunct it assumes:
            // `cases { A => { ... } B => { ... } }`. The arms' disjunction,
            // grouped left to right, must be an available fact.
            self.expect(Token::LBrace)?;
            let mut arms = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                let assumption = self.parse_proposition()?;
                self.expect(Token::FatArrow)?;
                let tactics = self.parse_possibly_empty_tactic_block()?;
                arms.push(ProofCaseArm::new(assumption, tactics));
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
            }
            self.expect(Token::RBrace)?;
            if arms.len() < 2 {
                return Err(self.error("`cases` needs one arm for each disjunct, at least two"));
            }
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::Cases(ProofCases::new(arms)));
        }
        if name == "match" {
            let scrutinee = self.parse_contract_expression()?;
            // Arms that end in different states name what the rejoined
            // proof keeps, as a `branch` does.
            let ensuring = self.parse_optional_join_interface()?;
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
                let scope = self.names.scope();
                for name in &bindings {
                    self.names.set_scoped(NameKind::ContractBinding, name, true);
                }
                // A proof arm's struct-pointer binding is a memory base in the
                // arm body exactly as a resource arm's is (package A5), so the
                // arm's bindings get their declared types here too. Without
                // this, `id->word` in the body resolves against no layout and
                // lowers as a width-unknown load, which reads a different cell
                // from the `p->word` the same arm's `fact p == id` identifies
                // it with.
                let saved_arm_binding_types = std::mem::take(&mut self.names.arm_binding_types);
                for binding in &bindings {
                    self.bind_proof_name(binding, false)?;
                }
                self.bind_arm_binding_types(&type_name, &variant, &bindings);
                let tactics = self.parse_possibly_empty_tactic_block();
                self.names.end(scope);
                self.names.arm_binding_types = saved_arm_binding_types;
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
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::Match(std::sync::Arc::new(ProofMatch {
                scrutinee,
                ensuring,
                arms,
            })));
        }
        if name == "branch" {
            let ensuring = self.parse_binary_join_interface()?;
            let then_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect_ident_spelling("else")?;
            let else_tactics = self.parse_possibly_empty_tactic_block()?;
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::Branch(ProofBranch {
                ensuring,
                then_tactics,
                else_tactics,
            }));
        }
        if name == "outcomes" {
            // `outcomes { returned => { ... } threw => { ... } }`: one arm per
            // way the call can end, in either order, as `match` arms are.
            self.expect(Token::LBrace)?;
            let mut returned_tactics = None;
            let mut threw_tactics = None;
            while self.peek() != Some(&Token::RBrace) {
                let arm = self.expect_ident("`returned` or `threw`")?;
                self.expect(Token::FatArrow)?;
                let tactics = self.parse_possibly_empty_tactic_block()?;
                let slot = match arm.as_str() {
                    "returned" => &mut returned_tactics,
                    "threw" => &mut threw_tactics,
                    _ => {
                        return Err(self.error(format!(
                            "`outcomes` arms are `returned` and `threw`, got `{arm}`"
                        )));
                    }
                };
                if slot.replace(tactics).is_some() {
                    return Err(self.error(format!("duplicate `outcomes` arm `{arm}`")));
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
            }
            self.expect(Token::RBrace)?;
            let (Some(returned_tactics), Some(threw_tactics)) = (returned_tactics, threw_tactics)
            else {
                return Err(self.error("`outcomes` needs both a `returned` and a `threw` arm"));
            };
            self.skip_redundant_semicolon();
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
                if self.peek_ident() == Some("if") {
                    self.position += 1;
                    let condition = self.parse_proposition()?;
                    self.expect(Token::LBrace)?;
                    let start = resources.len();
                    while self.peek() != Some(&Token::RBrace) {
                        let access = match self.expect_ident("conditional loop resource assertion")?.as_str() {
                            "owns" => ResourceAccessMode::Own,
                            "views" => ResourceAccessMode::View,
                            _ => return Err(self.error("conditional loop contracts accept `owns` or `views` resource assertions")),
                        };
                        if self.peek_ident().is_some()
                            && self.tokens.get(self.position + 1) == Some(&Token::Colon)
                        {
                            return Err(self.error("conditional loop resource binders are not supported; use an unnamed `owns` or `views` assertion"));
                        }
                        let resource = self.parse_resource_target(access)?;
                        self.expect(Token::Semicolon)?;
                        resources.push(ResourceClause::Conditional {
                            condition: condition.clone(),
                            resource: Box::new(resource),
                        });
                    }
                    self.expect(Token::RBrace)?;
                    if resources.len() == start {
                        return Err(self.error(
                            "conditional loop contract must contain an `owns` or `views` assertion",
                        ));
                    }
                    continue;
                }
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
                    self.proof_clause_owner = self.here();
                    self.position += 1;
                    if initialize_proof.is_some() {
                        return Err(self.error("duplicate `initialize` proof"));
                    }
                    initialize_proof = Some(self.parse_loop_phase_proof()?);
                    continue;
                }
                if self.peek_ident() == Some("preserve") {
                    self.proof_clause_owner = self.here();
                    self.position += 1;
                    if preserve_proof.is_some() {
                        return Err(self.error("duplicate `preserve` proof"));
                    }
                    preserve_proof = Some(self.parse_loop_phase_proof()?);
                    continue;
                }
                items.extend(self.parse_region_proof_items()?);
            }
            self.expect(Token::RBrace)?;
            self.skip_redundant_semicolon();
            if items.is_empty() && decreases.is_none() && resources.is_empty() && !diverges {
                return Err(self
                    .error("`loop` block must contain at least one item or a `decreases` clause"));
            }
            return Ok(ProofTactic::Loop(StructuralClause::from(
                StructuralClauseData {
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
                },
            )));
        }
        self.parse_named_proof_tactic(name)
    }

    // Structural induction retains a child proof parser. Its syntax
    // temporaries must not share the large leaf-tactic dispatch frame.
    #[inline(never)]
    fn parse_induct_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let tactic = {
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
                            self.names
                                .insert(NameKind::ContractBinding, (*binding).clone())
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    let tactics = self.parse_possibly_empty_tactic_block();
                    for binding in newly_bound {
                        self.names.remove(NameKind::ContractBinding, &binding);
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
                self.skip_redundant_semicolon();
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
        };
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    // Keep the large leaf-tactic dispatch frame out of recursive proof-body
    // parsing. Expanded both/if/closure scopes can nest while reading terms.
    #[inline(never)]
    fn parse_named_proof_tactic(&mut self, name: String) -> Result<ProofTactic, ClickError> {
        if self.tactic_names.contains(&name) && self.peek() == Some(&Token::LParen) {
            // The name was consumed by the dispatcher; the application
            // parser reads it again as the tactic it applies.
            self.position -= 1;
            let application = self.parse_call_binder_transport(None, true)?;
            self.expect(Token::Semicolon)?;
            return Ok(ProofTactic::UserTactic(application));
        }
        let tactic = match name.as_str() {
            "step" => {
                self.expect(Token::LParen)?;
                let step = if self.peek() == Some(&Token::RParen) {
                    ProofTactic::Step
                } else if self.call_binder_transport_follows()
                    || self.peek_next() == Some(&Token::Comma)
                {
                    ProofTactic::StepCall(self.parse_call_binder_transport(None, false)?)
                } else {
                    let name = self.expect_ident("call contract name")?;
                    if self.peek() == Some(&Token::LParen) {
                        return Err(self.error(format!(
                            "`step({name}(...))` is retired; select a named contract with \
                             `step({name})`, or `step({name}, {{ handle: instance }})` \
                             when its body declares resource handles"
                        )));
                    }
                    let mut arguments = Vec::new();
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                        if self.peek() != Some(&Token::LBrace) {
                            return Err(self.error(format!(
                                "`step({name}, ...)` selects one contract; after the comma it \
                                 takes a handle map, `{{ handle: instance }}`"
                            )));
                        }
                        self.position += 1;
                        while self.peek() != Some(&Token::RBrace) {
                            let handle = self.expect_ident("contract resource handle")?;
                            self.expect(Token::Colon)?;
                            let name = self.expect_ident("resource instance")?;
                            let (identity, resource_name) = self
                                .names
                                .resource_bindings
                                .get(&name)
                                .cloned()
                                .ok_or_else(|| self.unknown_instance(&name, "resource instance"))?;
                            arguments.push(ContractResourceArgument {
                                handle,
                                name,
                                resource_name,
                                identity,
                            });
                            if self.peek() != Some(&Token::Comma) {
                                break;
                            }
                            self.position += 1;
                        }
                        self.expect(Token::RBrace)?;
                    }
                    ProofTactic::StepContract(ContractApplication { name, arguments })
                };
                self.expect(Token::RParen)?;
                return self.parse_step_proof(step);
            }
            "close_invariants" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("by") {
                    self.position += 1;
                    let body = self.parse_close_invariants_body()?;
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::CloseInvariantsBy(body));
                }
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
            "unfold" => {
                self.expect(Token::LParen)?;
                // Look ahead without parsing: parsing an expression may split
                // generic `>>` tokens, so rewinding only the cursor is unsafe.
                let mut depth = 0usize;
                let mut quantified = false;
                for token in &self.tokens[self.position..] {
                    match token {
                        Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
                        Token::RParen | Token::RBracket | Token::RBrace => {
                            if depth == 0 {
                                break;
                            }
                            depth -= 1;
                        }
                        Token::Ident(name) if depth == 0 && name == "of" => {
                            quantified = true;
                            break;
                        }
                        _ => {}
                    }
                }
                // `unfold(f(args))` applies `f` even where a resource
                // instance shares its name; the instance is unfolded bare.
                let tactic = if quantified
                    || self.peek_ident() == Some("authority")
                    || (self
                        .peek_ident()
                        .is_some_and(|name| self.names.resource_targets.contains_key(name))
                        && self.peek_next() != Some(&Token::LParen))
                {
                    ProofTactic::UnfoldResource(self.parse_owned_resource_target()?)
                } else if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let (name, arguments) =
                        self.parse_call_arguments("function or resource name")?;
                    ProofTactic::UnfoldFunction(ClickFunctionApplication { name, arguments })
                } else if let Some(name) = self.peek_ident()
                    && self.names.resource_bindings.contains_key(name)
                {
                    return Err(self.error(format!(
                        "resource instance `{name}` is not available as an unfold target"
                    )));
                } else {
                    let predicate = self.expect_reference_name("predicate name")?;
                    ProofTactic::UnfoldPredicate(predicate)
                };
                self.expect(Token::RParen)?;
                if self.peek_ident() == Some("using") {
                    return Err(self.error(
                        "`unfold` takes no `using` list; write `peel(f(args)) using { ... }` to open a range fold by the law its guards select",
                    ));
                }
                if self.peek_ident() == Some("as") {
                    return Err(self.error(
                        "`unfold` takes no `as` map; name the opened pieces on the left: `let { slot: name } = unfold(resource);`",
                    ));
                }
                tactic
            }
            "peel" => {
                self.expect(Token::LParen)?;
                if !(matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen))
                {
                    return Err(
                        self.error("`peel` requires a pure-function application, `peel(f(args))`")
                    );
                }
                let (name, arguments) = self.parse_call_arguments("function name")?;
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    return Err(self.error(
                        "`peel` requires a `using { ... }` list naming the guard that decides the range",
                    ));
                }
                let premises = self.parse_exact_premises()?;
                self.skip_redundant_semicolon();
                return Ok(ProofTactic::PeelFunction {
                    application: ClickFunctionApplication { name, arguments },
                    premises,
                });
            }
            "apply" => {
                self.expect(Token::LParen)?;
                let application = self.parse_theorem_application()?;
                self.expect(Token::RParen)?;
                if self.peek_ident() != Some("using") {
                    ProofTactic::ApplyTheorem(application)
                } else {
                    let premises = self.parse_exact_premises()?;
                    self.skip_redundant_semicolon();
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
                // `witness { k: value, ... }`: a value for each named binder
                // of the existential goal, in order.
                self.expect(Token::LBrace)?;
                let mut bindings: Vec<(String, ContractExpression)> = Vec::new();
                while self.peek() != Some(&Token::RBrace) {
                    let name = self.expect_ident("witness binder name")?;
                    if bindings.iter().any(|(bound, _)| bound == &name) {
                        return Err(self.error(format!("duplicate witness for `{name}`")));
                    }
                    self.expect(Token::Colon)?;
                    let value = self.parse_contract_expression()?;
                    bindings.push((name, value));
                    if self.peek() != Some(&Token::Comma) {
                        break;
                    }
                    self.position += 1;
                }
                self.expect(Token::RBrace)?;
                if bindings.is_empty() {
                    return Err(self.error("`witness` needs at least one `binder: value`"));
                }
                if self.peek() != Some(&Token::Semicolon) {
                    return Err(self.error("expected `;` after `witness { ... }`"));
                }
                self.position += 1;
                return Ok(ProofTactic::Witness(ProofWitness::new(bindings)));
            }
            "obtain" => return self.parse_obtain(),
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
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::NormalizeUsing(premises));
                }
                ProofTactic::Normalize
            }
            "arithmetic" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::ArithmeticUsing(premises));
                }
                ProofTactic::ArithmeticUsing(Vec::new())
            }
            "arithmetic_certificate" => {
                return self.parse_arithmetic_certificate_tactic();
            }
            "intro" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("as") {
                    self.position += 1;
                    let name = self.expect_ident("name for the introduced variable")?;
                    self.names.hide_for_proof_binder(&name, false);
                    self.names.ended_fact_names.remove(&name);
                    ProofTactic::IntroAs(name)
                } else {
                    ProofTactic::Intro
                }
            }
            "split" | "left" | "right" => {
                return Err(self.error(format!(
                    "`{name}()` is now `assumption()`, which closes a conjunction whose sides are facts and a disjunction with one side a fact"
                )));
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
                    self.skip_redundant_semicolon();
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
                    ProofTactic::InstantiateUsing {
                        quantified,
                        argument,
                        premises: None,
                    }
                } else {
                    let premises = self.parse_exact_premises()?;
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::InstantiateUsing {
                        quantified,
                        argument,
                        premises: Some(premises),
                    });
                }
            }
            "simp" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::SimpUsing(ProofSimpUsing { premises }));
                }
                ProofTactic::Simp
            }
            "fold" => {
                self.expect(Token::LParen)?;
                if self
                    .peek_ident()
                    .is_some_and(|resource| self.is_hidden_record(resource))
                {
                    return self.parse_fold_construction(None);
                }
                let resource = self.parse_owned_resource_target()?;
                self.expect(Token::RParen)?;
                return self.parse_step_proof(ProofTactic::FoldResource(resource));
            }
            "construct" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_owned_resource_target()?;
                self.expect(Token::RParen)?;
                ProofTactic::ConstructResource(resource)
            }
            "induct" => return self.parse_induct_proof_tactic(),
            // `auto();` closes every goal still open in its block, as the
            // closer an omitted one stands for does.
            "auto" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::AutoClose
            }
            _ if is_tactic_name(&name) => {
                return Err(self.error(format!(
                    "`{name}` is only available as a standalone smart tactic; use `by {name}();`"
                )));
            }
            _ => return Err(self.error(format!("unknown tactic `{name}`"))),
        };
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    /// Binary proof splits use `then` exactly when an interface precedes the arms.
    fn parse_binary_join_interface(&mut self) -> Result<Option<Vec<ProofAssertion>>, ClickError> {
        let ensuring = self.parse_optional_join_interface()?;
        if ensuring.is_some() {
            self.expect_ident_spelling("then")?;
        } else if self.peek_ident() == Some("then") {
            return Err(
                self.error("`then` requires an `ensuring` interface; start the arm with `{`")
            );
        }
        Ok(ensuring)
    }

    /// An optional `ensuring { fact ...; owns ...; views ...; }` block: what
    /// the state after a join keeps when its arms end in different states.
    fn parse_optional_join_interface(&mut self) -> Result<Option<Vec<ProofAssertion>>, ClickError> {
        if self.peek_ident() != Some("ensuring") {
            return Ok(None);
        }
        self.position += 1;
        self.expect(Token::LBrace)?;
        let mut assertions = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            let kind = self.expect_ident("branch assertion kind")?;
            let assertion = match kind.as_str() {
                "fact" => ProofAssertion::Fact(self.parse_proposition()?),
                "owns" => ProofAssertion::Resource(
                    self.parse_join_interface_resource(ResourceAccessMode::Own)?,
                ),
                "views" => ProofAssertion::Resource(
                    self.parse_join_interface_resource(ResourceAccessMode::View)?,
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
        Ok(Some(assertions))
    }

    /// One resource of a join interface. `name: resource(args)` binds the
    /// instance the rejoined proof holds, so later `fact` entries and the
    /// proof after the join can read its fields; each arm supplies whichever
    /// instance of that resource it holds at those arguments. A name already
    /// bound outside the join is rebound, as a loop header rebinds one.
    fn parse_join_interface_resource(
        &mut self,
        access: ResourceAccessMode,
    ) -> Result<ResourceClause, ClickError> {
        if !matches!(self.peek(), Some(Token::Ident(_))) || self.peek_next() != Some(&Token::Colon)
        {
            return self.parse_resource_target(access);
        }
        let name = self.expect_ident("resource instance name")?;
        self.expect(Token::Colon)?;
        if access != ResourceAccessMode::Own {
            return Err(self.error(
                "a named interface resource must be owned: write `owns name: resource(...);`",
            ));
        }
        let resource = self.parse_resource_target(access)?;
        let ResourceClause::Declared {
            name: resource_name,
            ..
        } = &resource
        else {
            return Err(self.error("a named interface resource requires a declared resource"));
        };
        let identity = match self.names.resource_bindings.get(&name) {
            // A binder an `unfold` introduced for a child slot is recorded
            // under its parent's resource, so it is taken by identity alone,
            // as a loop header takes it.
            Some((identity, family))
                if family == resource_name || self.child_slot_identities.contains(identity) =>
            {
                *identity
            }
            Some((_, family)) => {
                return Err(self.error(format!(
                    "interface binder `{name}` rebinds an instance of resource `{family}`, not `{resource_name}`"
                )));
            }
            None => {
                let identity = Variable(self.next_resource_identity);
                self.next_resource_identity += 1;
                identity
            }
        };
        self.names
            .bind_instance(name.clone(), (identity, resource_name.clone()));
        let target = ResourceClause::Named {
            binding: ResourceInstanceBinding {
                name: name.clone(),
                identity,
                children: vec![],
                schema: None,
                fields: None,
                fold_fields: None,
                child_bindings: None,
                default_child_bindings: None,
            },
            resource: Box::new(resource),
        };
        self.names.set_instance_target(name, target.clone());
        Ok(target)
    }

    /// An else spine represents successive cases, including sequential C
    /// early returns. Keep its block scopes on the heap rather than retaining
    /// a tactic-dispatch frame per case. Then arms still use the ordinary
    /// structural recursion bound.
    fn parse_if_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let mut frames = Vec::new();
        let mut scopes = Vec::new();
        let result = (|| {
            loop {
                let condition = self.parse_proposition()?;
                let ensuring = self.parse_binary_join_interface()?;
                let then_tactics = self.parse_possibly_empty_tactic_block()?;
                self.expect_ident_spelling("else")?;
                self.expect(Token::LBrace)?;
                let else_open = self.positions[self.position - 1].clone();
                let mut else_starts = Vec::new();
                scopes.push((self.names.scope(), self.names.take(NameKind::ProofBinder)));
                let mut else_tactics = Vec::new();
                while self.peek() != Some(&Token::RBrace) && self.peek_ident() != Some("if") {
                    else_starts.push(self.positions[self.position].clone());
                    else_tactics.push(self.parse_proof_tactic()?);
                }
                if self.peek_ident() == Some("if") {
                    else_starts.push(self.positions[self.position].clone());
                }
                frames.push((
                    condition,
                    ensuring,
                    then_tactics,
                    else_tactics,
                    else_open,
                    else_starts,
                ));
                if self.peek_ident() == Some("if") {
                    self.position += 1;
                    continue;
                }
                break;
            }
            let mut nested = None;
            while let Some((
                condition,
                ensuring,
                then_tactics,
                mut else_tactics,
                else_open,
                mut else_starts,
            )) = frames.pop()
            {
                if let Some(nested) = nested.take() {
                    else_tactics.push(nested);
                }
                while self.peek() != Some(&Token::RBrace) {
                    else_starts.push(self.positions[self.position].clone());
                    else_tactics.push(self.parse_proof_tactic()?);
                }
                self.record_proof_block(else_open, else_starts);
                self.expect(Token::RBrace)?;
                let (scope, names) = scopes.pop().expect("an else block owns a scope");
                self.names.end(scope);
                self.names.replace(NameKind::ProofBinder, names);
                self.skip_redundant_semicolon();
                nested = Some(ProofTactic::If(ProofIf {
                    condition,
                    ensuring,
                    then_tactics,
                    else_tactics,
                }));
            }
            Ok(nested.expect("an if spine has a root"))
        })();
        // Error exits restore exactly the same bindings as a recursive block.
        while let Some((scope, names)) = scopes.pop() {
            self.names.end(scope);
            self.names.replace(NameKind::ProofBinder, names);
        }
        result
    }

    /// What follows a `step(...)` head: `;`, `by` and the proof of its one
    /// open obligation, or a block of `requires P by ...` entries.
    #[inline(never)]
    fn parse_step_proof(&mut self, step: ProofTactic) -> Result<ProofTactic, ClickError> {
        let (tactic, call) = if matches!(step, ProofTactic::FoldResource(_)) {
            ("fold", "fold(...)")
        } else {
            ("step", "step()")
        };
        if self.peek_ident() == Some("by") {
            self.position += 1;
            if self.peek_ident() == Some("auto") && self.peek_next() == Some(&Token::LParen) {
                return Err(self.error(format!(
                    "`{call} by auto()` is `{call}`: its open obligations already go to `auto`",
                )));
            }
            let body = self.parse_step_proof_body()?;
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::StepProved {
                step: Box::new(step),
                proof: StepProof::By(body),
            });
        }
        if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let mut entries = Vec::new();
            while self.peek() != Some(&Token::RBrace) {
                match self.peek_ident() {
                    Some("requires") => self.position += 1,
                    _ => {
                        return Err(self.error(format!(
                            "a `{tactic}(...) {{ ... }}` block holds only `requires P by ...;` entries",
                        )));
                    }
                }
                let label = if let (Some(Token::Ident(label)), Some(Token::Colon)) =
                    (self.peek(), self.peek_next())
                {
                    let label = label.clone();
                    self.position += 2;
                    Some(label)
                } else {
                    None
                };
                let proposition = self.parse_proposition()?;
                if self.peek_ident() != Some("by") {
                    return Err(self
                        .error("a `requires` entry needs its proof: write `requires P by ...;`"));
                }
                let proof = self.parse_by_clause()?;
                self.skip_redundant_semicolon();
                entries.push(StepRequirement {
                    label,
                    have: ProofHave {
                        proposition,
                        proof: have_proof_as_written_in_full(proof),
                    },
                });
            }
            self.expect(Token::RBrace)?;
            if entries.is_empty() {
                return Err(self.error(format!(
                    "a `{tactic}(...) {{ ... }}` block needs at least one `requires` entry"
                )));
            }
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::StepProved {
                step: Box::new(step),
                proof: StepProof::Requires(entries),
            });
        }
        self.expect(Token::Semicolon)?;
        Ok(step)
    }

    /// The body after a step's `by`: a block or one tactic call, as
    /// after `close_invariants() by`.
    fn parse_step_proof_body(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        if self.peek() == Some(&Token::LBrace) {
            let body = self.parse_possibly_empty_tactic_block()?;
            if body.is_empty() {
                return Err(self.error("a step's `by` block must contain at least one tactic"));
            }
            return Ok(body);
        }
        match self.peek() {
            Some(Token::Ident(_)) => Ok(vec![self.parse_implicit_proof_tactic()?]),
            Some(token) => Err(self.error(format!(
                "expected a proof after a step's `by`, got {token}: write one tactic call or a block `{{ ... }}`"
            ))),
            None => Err(self.error("expected a proof after a step's `by`, got end of input")),
        }
    }

    // `close_invariants() by T(...);` is the one-step body
    // `close_invariants() by { T(...); }`, as after `have` and `ensures`.
    #[inline(never)]
    fn parse_close_invariants_body(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        if self.peek() == Some(&Token::LBrace) {
            return self.parse_possibly_empty_tactic_block();
        }
        // `auto` has no script spelling, and the bare closer is already the
        // smart one; say so rather than suggest the `by auto();` just written.
        if self.peek_ident() == Some("auto") {
            return Err(self.error(
                "`close_invariants() by auto()` is not a form: write `close_invariants();`, whose closer is already smart, or end the `preserve` script and let the back edge close implicitly",
            ));
        }
        match self.peek() {
            Some(Token::Ident(_)) => Ok(vec![self.parse_implicit_proof_tactic()?]),
            Some(token) => Err(self.error(format!(
                "expected a proof after `close_invariants() by`, got {token}: write one tactic call or a block `{{ ... }}`"
            ))),
            None => Err(self.error(
                "expected a proof after `close_invariants() by`, got end of input",
            )),
        }
    }

    fn parse_possibly_empty_tactic_block(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        self.expect(Token::LBrace)?;
        let tactics = self.parse_tactics_until_rbrace()?;
        self.expect(Token::RBrace)?;
        Ok(tactics)
    }

    /// The one tactic of a proof written without braces, recording its span.
    fn parse_implicit_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        let first = self.position;
        let tactic = self.parse_proof_tactic()?;
        self.record_implicit_proof(first);
        Ok(tactic)
    }

    /// Records the unbraced one-tactic proof from token `first` to the
    /// token before the cursor.
    fn record_implicit_proof(&mut self, first: usize) {
        if let (Some(first), Some(last)) = (
            self.positions.get(first),
            self.position
                .checked_sub(1)
                .and_then(|last| self.positions.get(last)),
        ) {
            self.implicit_proof_spans.push(ImplicitProofSpan {
                first: first.clone(),
                last: last.clone(),
            });
        }
    }

    /// Records a braced proof block whose `}` is at the cursor.
    fn record_proof_block(&mut self, open: SourcePosition, tactics: Vec<SourcePosition>) {
        if let Some(close) = self.positions.get(self.position) {
            self.proof_block_spans.push(ProofBlockSpan {
                open,
                close: close.clone(),
                tactics,
            });
        }
    }

    /// The tactics of a braced block whose `{` the cursor has just passed,
    /// up to its `}`, recording the block's span.
    fn parse_tactic_list_to_rbrace(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        let open = self
            .position
            .checked_sub(1)
            .filter(|index| self.tokens[*index] == Token::LBrace)
            .map(|index| self.positions[index].clone());
        let mut tactics = Vec::new();
        let mut starts = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            starts.push(self.positions[self.position].clone());
            tactics.push(self.parse_proof_tactic()?);
        }
        if let Some(open) = open {
            self.record_proof_block(open, starts);
        }
        Ok(tactics)
    }

    fn parse_tactics_until_rbrace(&mut self) -> Result<Vec<ProofTactic>, ClickError> {
        let scope = self.names.scope();
        let previous_proof_let_names = self.names.take(NameKind::ProofBinder);
        let result = self.parse_tactic_list_to_rbrace();
        self.names.end(scope);
        self.names
            .replace(NameKind::ProofBinder, previous_proof_let_names);
        result
    }

    fn parse_theorem_application(&mut self) -> Result<TheoremApplication, ClickError> {
        let (name, arguments) = self.parse_call_arguments("theorem name")?;
        let name = self.symbols.theorem_identity(name);
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
                        return Err(self.error(format!("expected `,` or `)`, got {token}")));
                    }
                    None => return Err(self.error("expected `,` or `)`, got end of input")),
                }
            }
        }
        self.expect(Token::RParen)?;
        Ok(ResourceClause::Declared {
            type_schema: None,
            resource_type_arguments: Vec::new(),
            resource_arguments: Vec::new(),
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
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        let mut resource_type_arguments = Vec::new();
        if name == "authority" {
            if self.peek() == Some(&Token::RParen) {
                return Err(self.error("authority expects one declared resource type"));
            }
            resource_type_arguments.push(self.parse_resource_count_pattern()?);
            if self.peek() != Some(&Token::RParen) {
                return Err(self.error("authority expects exactly one declared resource type"));
            }
            self.expect(Token::RParen)?;
            return Ok(ResourceClause::Declared {
                type_schema: None,
                resource_type_arguments,
                resource_arguments: Vec::new(),
                access,
                kind: ResourceKind::Token,
                name,
                arguments,
                parameter_types: Vec::new(),
            });
        }
        if self.peek() != Some(&Token::RParen) {
            loop {
                if matches!(name.as_str(), "mutex_use" | "publisher" | "subscriber")
                    && arguments.len() == 1
                {
                    resource_type_arguments.push(self.parse_declared_resource_call()?);
                } else {
                    arguments.push(self.parse_contract_expression()?);
                }
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::RParen) => break,
                    _ => return Err(self.error("expected `,` or `)` after resource argument")),
                }
            }
        }
        self.expect(Token::RParen)?;
        let mut resource_arguments = Vec::new();
        let first_reference = arguments.iter().position(|argument| {
            matches!(argument, ContractExpression::CFragment(CExpression::Variable(name)) | ContractExpression::Binding(name)
                if self.names.resource_bindings.contains_key(name))
        });
        if let Some(first) = first_reference {
            for argument in arguments.drain(first..) {
                let reference =
                    match argument {
                        ContractExpression::CFragment(CExpression::Variable(name))
                        | ContractExpression::Binding(name) => name,
                        _ => return Err(self.error(
                            "resource arguments must be named resources after ordinary arguments",
                        )),
                    };
                let Some(ResourceClause::Named { binding, .. }) =
                    self.names.resource_targets.get(&reference)
                else {
                    return Err(self.error(format!("unknown resource argument `{reference}`")));
                };
                resource_arguments.push(binding.clone());
            }
        }
        Ok(ResourceClause::Declared {
            type_schema: None,
            resource_type_arguments,
            resource_arguments,
            access,
            kind: ResourceKind::Token,
            name,
            arguments,
            parameter_types: Vec::new(),
        })
    }

    fn expect_empty_tactic_args(&mut self, name: &str) -> Result<(), ClickError> {
        if (is_tactic_name(name) || name == "close_invariants")
            && self.peek() != Some(&Token::LParen)
        {
            return Err(self.error(format!("`{name}` requires parentheses; write `{name}()`")));
        }
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
        } else if self.peek_ident() == Some("rules") {
            self.position += 1;
            self.parse_special_arithmetic_certificate_body()
        } else if self.peek_ident() == Some("special") {
            Err(self.error(RETIRED_SPECIAL_CERTIFICATE))
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
            let keyword = self.expect_ident("`rules` arithmetic certificate node")?;
            match keyword.as_str() {
                "premise" => {
                    let index = self.expect_index("`rules` premise index")?;
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
                            "`rules` arithmetic premise {index} must repeat the same proposition on both sides"
                        )));
                    }
                    if index > premises.len() {
                        return Err(self.error(format!(
                            "`rules` arithmetic premise indices must be contiguous; expected {} but found {index}",
                            premises.len()
                        )));
                    }
                    if index == premises.len() {
                        premises.push(None);
                    }
                    if premises[index].replace(proposition).is_some() {
                        return Err(self.error(format!(
                            "`rules` arithmetic premise {index} is declared more than once"
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
                "unsigned_sum_bound" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds = self.parse_certificate_index_list("unsigned sum bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::UnsignedSumBound { bounds, result });
                }
                "integer_cast_identity" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds = self.parse_certificate_index_list("integer cast bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerCastIdentity { bounds, result });
                }
                "integer_operation_identity" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer operation bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerOperationIdentity { bounds, result });
                }
                "integer_product_bounds" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer product bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerProductBounds { bounds, result });
                }
                "integer_division_bounds" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer division bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerDivisionBounds { bounds, result });
                }
                "integer_multiply_order" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer multiply order premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerMultiplyOrder { bounds, result });
                }
                "integer_quotient_bound" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer quotient bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerQuotientBound { bounds, result });
                }
                "integer_bound_exclusion" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer bound exclusion premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerBoundExclusion { bounds, result });
                }
                "integer_relation_transport" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds = self
                        .parse_certificate_index_list("integer relation transport bound premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerRelationTransport { bounds, result });
                }
                "integer_polynomial_identity" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer polynomial identity premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerPolynomialIdentity { bounds, result });
                }
                "integer_quotient_shift" => {
                    self.expect_ident_spelling("bounds")?;
                    let bounds =
                        self.parse_certificate_index_list("integer quotient shift premise")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::IntegerQuotientShift { bounds, result });
                }
                "int32_defined" | "int64_defined" => {
                    let width = if keyword == "int32_defined" {
                        crate::kernel::SignedDefinedWidth::Int32
                    } else {
                        crate::kernel::SignedDefinedWidth::Int64
                    };
                    self.expect_ident_spelling("bounds")?;
                    let bounds = self.parse_certificate_index_list(match width {
                        crate::kernel::SignedDefinedWidth::Int32 => "int32 bound premise",
                        crate::kernel::SignedDefinedWidth::Int64 => "int64 bound premise",
                    })?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(SpecialArithmeticNode::SignedDefined {
                        width,
                        bounds,
                        result,
                    });
                }
                "conclusion" => {
                    if conclusion.is_some() {
                        return Err(self.error(
                            "`rules` arithmetic certificate may contain only one `conclusion` line",
                        ));
                    }
                    conclusion = Some(self.expect_index("conclusion node")?);
                    self.expect(Token::Semicolon)?;
                }
                _ => {
                    return Err(self.error(format!(
                        "unknown `rules` arithmetic certificate node `{keyword}`"
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let conclusion = conclusion.ok_or_else(|| {
            self.error("`rules` arithmetic certificate must end with `conclusion N;`")
        })?;
        if nodes.is_empty() {
            return Err(self.error("`rules` arithmetic certificate must contain a node"));
        }
        let premises = premises
            .into_iter()
            .enumerate()
            .map(|(index, premise)| {
                premise.ok_or_else(|| {
                    self.error(format!(
                        "`rules` arithmetic premise indices must be contiguous; missing {index}"
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
                "less_equal_from_equal" => {
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
                "equal_from_bounds" => {
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
                "less_than_from_not_equal" => {
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
                "int32_range" => {
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::Int32Range { result }
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
                "interval_remainder_add" => {
                    let operand = self.expect_index("operand interval")?;
                    self.expect(Token::Comma)?;
                    let remainder = self.expect_index("remainder interval")?;
                    let addend = i32::try_from(self.expect_signed_i64("remainder addend")?)
                        .map_err(|_| self.error("remainder addend must fit in int32"))?;
                    let divisor = i32::try_from(self.expect_signed_i64("remainder divisor")?)
                        .map_err(|_| self.error("remainder divisor must fit in int32"))?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalRemainderAdd {
                        operand,
                        remainder,
                        addend,
                        divisor,
                        result: SignedInt32Interval { lower, upper },
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
                "interval_narrowed_cast" => {
                    let operand = self.expect_index("operand interval")?;
                    let cast_type = |parser: &mut Self, what: &str| {
                        let name = parser.expect_ident(what)?;
                        crate::surface::printing::machine_integer_type_from_name(&name)
                            .ok_or_else(|| parser.error(format!("unknown integer type `{name}`")))
                    };
                    let source = cast_type(self, "conversion source type")?;
                    let destination = cast_type(self, "conversion destination type")?;
                    let lower = self.expect_signed_i64("interval lower bound")?;
                    let upper = self.expect_signed_i64("interval upper bound")?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::IntervalNarrowedCast {
                        operand,
                        source,
                        destination,
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
                "affine_premise" => {
                    let source = self.expect_index("premise source")?;
                    let left_evidence = self.expect_index("left interval evidence")?;
                    let right_evidence = self.expect_index("right interval evidence")?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    SignedArithmeticStep::AffinePremise {
                        source,
                        left_evidence,
                        right_evidence,
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
                "less_equal_from_equal" => {
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
                "equal_from_bounds" => {
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
                "type_range" => {
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::TypeRange { result });
                }
                "negated_goal" => {
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::NegatedGoal { result });
                }
                "divide" => {
                    let source = self.expect_index("divide source")?;
                    self.expect_ident_spelling("by")?;
                    let divisor = self.parse_contract_expression()?;
                    self.expect(Token::FatArrow)?;
                    let result = self.parse_proposition()?;
                    self.expect(Token::Semicolon)?;
                    nodes.push(IntegerCertificateNode::Divide {
                        source,
                        divisor,
                        result,
                    });
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
            Some(Token::Ident(kind)) if kind == "back_edge" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::BackEdge)
            }
            Some(Token::Ident(kind)) if kind == "read" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let occurrence = self.expect_index("read occurrence")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Read(occurrence))
            }
            Some(Token::Ident(kind)) if kind == "assignment" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let local = self.expect_ident("assignment local")?;
                if self.names.contains(NameKind::ReferenceParameter, &local) {
                    return Err(self.error(format!(
                        "`{local}` is a reference, and binding a reference is not an assignment; a store through `{local}` is a store to what it refers to, so select the statement itself with `statement(N)`"
                    )));
                }
                self.expect(Token::Comma)?;
                let occurrence = self.expect_index("assignment occurrence")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Assignment { local, occurrence })
            }
            Some(Token::Ident(label)) => Ok(CodeRegionRef::Label(label)),
            Some(token) => Err(self.error(format!(
                "expected code region `function`, `loop(N)`, `statement(N)`, `assignment(local, N)`, `read(N)`, `back_edge()`, or label, got {token}"
            ))),
            None => Err(self.error(
                "expected code region `function`, `loop(N)`, `statement(N)`, `assignment(local, N)`, `read(N)`, `back_edge()`, or label, got end of input",
            )),
        }
    }

    fn parse_tactic(&mut self) -> Result<SmartTactic, ClickError> {
        let tactic = match self.next() {
            Some(Token::Ident(name)) if name == "auto" => SmartTactic::Auto,
            Some(Token::Ident(name)) if name == "simp" => SmartTactic::Simp,
            Some(Token::Ident(name)) => {
                return Err(self.error(format!("expected tactic, got `{name}`")));
            }
            Some(token) => {
                return Err(self.error(format!("expected tactic, got {token}")));
            }
            None => return Err(self.error("expected tactic, got end of input")),
        };
        let name = match tactic {
            SmartTactic::Auto => "auto",
            SmartTactic::Simp => "simp",
        };
        self.expect_empty_tactic_args(name)?;
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
        let mut values = vec![self.parse_rust_casts(first)?];
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
            values.push(self.parse_binary_operand()?);
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
            return Err(self.error("`object(p)` is now written `*p`: the object `p` points at"));
        }
        if self.peek() == Some(&Token::Amp) {
            return Err(self.error(
                "a resource clause names its place directly: write `p->next`, not `&p->next`, and `counter`, not `&counter[0..1]`",
            ));
        }
        // `*p` is the object `p` points at: one complete struct for a struct
        // pointer, one element for a scalar pointer.
        let dereference = self.peek() == Some(&Token::Star);
        if dereference {
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
                .names
                .struct_params
                .get(name)
                .or_else(|| self.names.aggregate_objects.get(name))
                .or_else(|| {
                    self.qualified_object(name)
                        .and_then(|object| object.struct_name.as_ref())
                })
                .cloned(),
            ContractExpression::CUnary {
                lowered: CExpression::Cast { pointee_struct, .. },
                ..
            }
            | ContractExpression::CFragment(CExpression::Cast { pointee_struct, .. }) => {
                pointee_struct.clone()
            }
            _ => None,
        };
        if let ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) = &surface_base
            && self
                .names
                .struct_params
                .contains_key(&struct_pointer_pointer_key(name))
        {
            struct_name = None;
        }
        let names_aggregate_object = match &surface_base {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.names.aggregate_objects.contains_key(name)
                    || self.names.global_array_shapes.contains_key(name)
                    || self.qualified_object(name).is_some()
            }
            _ => false,
        };
        let mut dereferences_pointer = !names_aggregate_object;
        let mut union_name: Option<String> = None;
        let mut struct_array_element_width = match &surface_base {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name))
                if self.names.contains(NameKind::StructArrayParameter, name) =>
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
                .names
                .global_array_shapes
                .get(name)
                .map(|array| array.shape.clone())
                .or_else(|| {
                    self.qualified_object(name)
                        .and_then(|object| object.array_shape.clone())
                }),
            _ => None,
        };
        let mut indexed_scalar_field: Option<CType> = None;
        let mut scalar_range_offset = None;
        let mut postfixes = 0;
        while matches!(self.peek(), Some(Token::Arrow | Token::Dot))
            || (self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range())
        {
            self.check_expression_chain_limit(postfixes)?;
            postfixes += 1;
            if self.peek() == Some(&Token::LBracket) {
                self.position += 1;
                let index = self.parse_place_index()?;
                self.expect(Token::RBracket)?;
                let index = contract_expression_as_c_fragment(&index).ok_or_else(|| {
                    self.error("struct array indices must be current C expressions")
                })?;
                let surface_base_before_index = surface_base;
                dereferences_pointer = false;
                if let Some(element_width) = struct_array_element_width
                    .filter(|_| struct_name.is_some())
                    .or_else(|| {
                        struct_name
                            .as_ref()
                            .and_then(|name| self.struct_layouts.get(name))
                            .map(|layout| layout.size_bytes())
                    })
                {
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
                    let stride = struct_byte_stride(offset, element_width);
                    base = CExpression::Add(Box::new(struct_byte_base(base)), Box::new(stride));
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
            let field_name = self.expect_field_name()?;
            // Under `*`, the last field is read as the pointer it holds, not
            // owned as a slot.
            if !dereference
                && !matches!(
                    self.peek(),
                    Some(Token::Arrow | Token::Dot | Token::LBracket)
                )
            {
                if let Some(base_union_name) = &union_name
                    && self.union_layouts.contains_key(base_union_name)
                {
                    let field = self.resolve_union_field_metadata(base_union_name, &field_name)?;
                    // Owning a union field covers its opaque storage in ABI byte units.
                    // It does not authorize reading or copying a typed union value.
                    let field = if field.union_name.is_some() {
                        ResolvedField {
                            c_type: C0Type::UInt8,
                            byte_width: 1,
                            union_name: None,
                            ..field
                        }
                    } else {
                        field
                    };
                    self.validate_field_place(&field)?;
                    let segment = Self::field_segment_from_metadata(
                        base,
                        Some(surface_base.clone()),
                        &field_name,
                        &field,
                    );
                    return Ok(vec![segment]);
                }
                if let Some(base_struct_name) = &struct_name
                    && self.struct_layouts.contains_key(base_struct_name)
                {
                    let field =
                        self.resolve_struct_field_metadata(base_struct_name, &field_name)?;
                    if field.struct_name.is_some() && !field.c_type.is_pointer() {
                        if !allow_aggregates {
                            return Err(self.error(
                                "aggregate contract segments are only supported in resource clauses",
                            ));
                        }
                        return self.aggregate_field_segments(
                            base,
                            surface_base,
                            &field_name,
                            &field,
                        );
                    }
                    // Owning a union field covers its opaque storage in ABI byte units.
                    // It does not authorize reading or copying a typed union value.
                    let field = if field.union_name.is_some() {
                        ResolvedField {
                            c_type: C0Type::UInt8,
                            byte_width: 1,
                            union_name: None,
                            ..field
                        }
                    } else {
                        field
                    };
                    self.validate_field_place(&field)?;
                    let segment = Self::field_segment_from_metadata(
                        base,
                        Some(surface_base.clone()),
                        &field_name,
                        &field,
                    );
                    return Ok(vec![segment]);
                }
                let segment =
                    self.resolve_field_segment(base, Some(surface_base.clone()), &field_name)?;
                return Ok(vec![segment]);
            }
            let mut scalar_field = false;
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
                dereferences_pointer = field.c_type.is_pointer();
                let pointer = self.offset_field_pointer(base, field.offset_bytes);
                let field_memory_pointer = field_has_direct_memory_place(&field);
                scalar_field = field_memory_pointer
                    && matches!(
                        field.c_type,
                        C0Type::Int8
                            | C0Type::Int16
                            | C0Type::Int32
                            | C0Type::Char(_)
                            | C0Type::UInt8
                            | C0Type::UInt16
                            | C0Type::UInt32
                            | C0Type::Int64(_)
                            | C0Type::UInt64(_)
                    );
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
                dereferences_pointer = field.c_type.is_pointer();
                let pointer = self.member_field_pointer(base, &field);
                let field_memory_pointer = field_has_direct_memory_place(&field);
                scalar_field = field_memory_pointer
                    && matches!(
                        field.c_type,
                        C0Type::Int8
                            | C0Type::Int16
                            | C0Type::Int32
                            | C0Type::Char(_)
                            | C0Type::UInt8
                            | C0Type::UInt16
                            | C0Type::UInt32
                            | C0Type::Int64(_)
                            | C0Type::UInt64(_)
                    );
                indexed_scalar_field = scalar_array_field_element(&field).map(|(_, ty)| ty);
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
            if scalar_field
                && self.peek() == Some(&Token::LBracket)
                && self.contract_bracket_is_range()
            {
                return Err(self.error(format!(
                    "field `{field_name}` is one value, not a pointer or an array, so it takes no range; write the field alone"
                )));
            }
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
                            | CType::Int128Array(_)
                            | CType::Int64Array(_)
                            | CType::UInt128Array(_)
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
                pointee_struct: next_struct_name.clone().filter(|_| dereferences_pointer),
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
        if let Some(element_type) = indexed_scalar_field {
            // The lowered base already addresses the selected scalar element.
            // Retain the complete written place, including every subscript,
            // instead of losing it in the field's byte-address arithmetic.
            let address = CExpression::AddressOf(Box::new(CExpression::TypedLoad {
                pointer: Box::new(base.clone()),
                value_type: element_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            }));
            return Ok(vec![ContractSegment {
                state: ContractSegmentState::Current,
                base,
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::CUnary {
                        operand: Box::new(surface_base),
                        lowered: address,
                    },
                    start: ContractExpression::CFragment(CExpression::Value(int32(0))),
                    end: ContractExpression::CFragment(CExpression::Value(int32(1))),
                },
            }]);
        }
        // A struct reference written alone is the struct it refers to.
        let carries_reference = |name: &str| {
            syntax::referent_of_carrier(name)
                .is_some_and(|referent| self.names.contains(NameKind::ReferenceParameter, referent))
        };
        let names_reference = match &surface_base {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => carries_reference(name),
            _ => false,
        };
        let names_scalar_referent = matches!(
            &surface_base,
            ContractExpression::CFragment(CExpression::Index(carrier, _))
                if matches!(carrier.as_ref(), CExpression::Variable(name) if carries_reference(name))
        );
        if dereference && (names_reference || names_scalar_referent) {
            return Err(self.error(
                "a reference parameter already names what it refers to; write it without `*`",
            ));
        }
        // Written alone, a scalar referent is the one element behind its
        // carrier, typed and sized by the carrier.
        if names_scalar_referent
            && self.peek() != Some(&Token::LBracket)
            && let CExpression::Index(carrier, _) = &base
        {
            let (start, end) = (CExpression::Value(int32(0)), CExpression::Value(int32(1)));
            return Ok(vec![ContractSegment {
                state: ContractSegmentState::Current,
                base: (**carrier).clone(),
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::CFragment((**carrier).clone()),
                    start: ContractExpression::CFragment(start),
                    end: ContractExpression::CFragment(end),
                },
            }]);
        }
        // Written alone, a struct reference is the object it refers to.
        let dereference = dereference
            || (names_reference
                && matches!(base, CExpression::Variable(_))
                && self.peek() != Some(&Token::LBracket));
        if dereference {
            if self.peek() == Some(&Token::LBracket) {
                return Err(self.error(
                    "`*` names one object and takes no range; write the range on the pointer, as in `p[lo..hi]`",
                ));
            }
            if !dereferences_pointer {
                return Err(self.error("`*` expects a pointer"));
            }
            // `*bytes` on a slice parameter is the whole slice, as `*value`
            // is the one object a reference refers to.
            if let CExpression::Variable(name) = &base
                && self.rust_slice_params.contains(name)
            {
                let length =
                    ContractExpression::CFragment(CExpression::Variable(format!("{name}_len")));
                let end_expression = length;
                let end = contract_expression_as_c_fragment(&end_expression)
                    .expect("a slice length is a C expression");
                let start = CExpression::Value(int32(0));
                return Ok(vec![ContractSegment {
                    state: ContractSegmentState::Current,
                    base,
                    start: start.clone(),
                    end,
                    surface: ContractSegmentSurface::Range {
                        base: surface_base,
                        start: ContractExpression::CFragment(start),
                        end: end_expression,
                    },
                }]);
            }
            let (start, end) = (CExpression::Value(int32(0)), CExpression::Value(int32(1)));
            let Some(struct_name) = struct_name else {
                return Ok(vec![ContractSegment {
                    state: ContractSegmentState::Current,
                    base,
                    start: start.clone(),
                    end: end.clone(),
                    surface: ContractSegmentSurface::Range {
                        base: surface_base,
                        start: ContractExpression::CFragment(start),
                        end: ContractExpression::CFragment(end),
                    },
                }]);
            };
            return Ok(vec![self.object_segment(base, struct_name)?]);
        }
        // A declared struct object owns all of its storage, with the same
        // word-based extent as `*p` for a pointer to that struct. Retain its
        // imported ABI so input cells use the actual field types.
        if postfixes == 0
            && self.peek() != Some(&Token::LBracket)
            && let ContractExpression::CFragment(CExpression::Variable(name)) = &surface_base
        {
            let object = if !self.names.c_parameter_types.contains_key(name)
                && !self.names.contains(NameKind::StructArrayParameter, name)
                && let Some(struct_name) = self.names.aggregate_objects.get(name)
            {
                Some((struct_name, CExpression::AddressOf(Box::new(base.clone()))))
            } else {
                self.qualified_object(name)
                    .filter(|object| object.address.is_none() && object.array_shape.is_none())
                    .and_then(|object| {
                        Some((object.struct_name.as_ref()?, object.expression.clone()))
                    })
            };
            if let Some((struct_name, address)) = object {
                let mut segment = self.object_segment(address, struct_name.clone())?;
                segment.surface = ContractSegmentSurface::ObjectPlace {
                    name: name.clone(),
                    layout: std::sync::Arc::new(StructRangeLayout {
                        name: struct_name.clone(),
                        layout: self.struct_layouts[struct_name].clone(),
                    }),
                };
                return Ok(vec![segment]);
            }
        }
        // A place written alone is its own storage: one element at its
        // address.
        if self.peek() != Some(&Token::LBracket) {
            if let CExpression::Variable(name) = &base
                && self.names.struct_params.contains_key(name)
                && !names_aggregate_object
            {
                return Err(self.error(format!(
                    "`{name}` alone names the variable that holds the pointer, which a contract cannot own; write `*{name}` for the object it points at"
                )));
            }
            let base = match base {
                CExpression::TypedLoad { pointer, .. } => *pointer,
                CExpression::Value(CValue::Pointer(_)) => {
                    let ContractExpression::CFragment(CExpression::Variable(name)) = &surface_base
                    else {
                        return Err(self.error("this C expression has no storage to own"));
                    };
                    self.qualified_object(name)
                        .and_then(|object| object.address.clone())
                        .ok_or_else(|| self.error("this C expression has no storage to own"))?
                }
                expression => CExpression::AddressOf(Box::new(expression)),
            };
            let surface_base = ContractExpression::CFragment(CExpression::AddressOf(Box::new(
                contract_expression_as_c_fragment(&surface_base).expect("C segment base"),
            )));
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
        // Preserve object counts. Multiplying source int32 bounds by the
        // struct's word count invents a signed-overflow obligation for a
        // perfectly valid pointer range; the kernel range carries its stride.
        let range_layout = struct_name
            .as_ref()
            .map(|name| {
                let layout = self.struct_layouts.get(name).ok_or_else(|| {
                    self.error(format!(
                        "a range of `struct {name}` needs an imported layout for it"
                    ))
                })?;
                Ok::<_, ClickError>(std::sync::Arc::new(StructRangeLayout {
                    name: name.clone(),
                    layout: layout.clone(),
                }))
            })
            .transpose()?;
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
            surface: match range_layout {
                Some(layout) => ContractSegmentSurface::StructRange {
                    base: surface_base,
                    start: start_expression,
                    end: end_expression,
                    layout,
                },
                None => ContractSegmentSurface::Range {
                    base: surface_base,
                    start: start_expression,
                    end: end_expression,
                },
            },
        }])
    }

    /// One complete struct object at `base`.
    fn object_segment(
        &self,
        base: CExpression,
        struct_name: String,
    ) -> Result<ContractSegment, ClickError> {
        let layout = self.struct_layouts.get(&struct_name).ok_or_else(|| {
            self.error(format!(
                "a whole object needs an imported layout for `struct {struct_name}`"
            ))
        })?;
        if layout.size_bytes() % 4 != 0 {
            return Err(self.error(format!(
                "a whole object cannot represent the {}-byte `struct {struct_name}` as an int32-aligned memory segment",
                layout.size_bytes()
            )));
        }
        Ok(ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start: CExpression::Value(int32(0)),
            end: CExpression::Value(int32(layout.size_bytes() / 4)),
            surface: ContractSegmentSurface::Object(struct_name),
        })
    }

    fn aggregate_field_segments(
        &self,
        base: CExpression,
        surface_base: ContractExpression,
        field_name: &str,
        field: &ResolvedField,
    ) -> Result<Vec<ContractSegment>, ClickError> {
        let Some(struct_name) = field.struct_name.as_deref() else {
            return Err(self.error(format!(
                "aggregate field `{field_name}` has no embedded struct layout"
            )));
        };
        // Keep the aggregate member's checked bounds while expanding its
        // ownership into leaf slots. The C member selector needs those bounds
        // before it can select a leaf through the enclosing aggregate.
        let base = self.member_field_pointer(base, field);
        let retain_surface_base = |mut segments: Vec<ContractSegment>| {
            for segment in &mut segments {
                if let ContractSegmentSurface::Field { base, .. } = &mut segment.surface {
                    *base = Some(Box::new(surface_base.clone()));
                }
            }
            segments
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
                let element_offset = flat_index.checked_mul(element_width).ok_or_else(|| {
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
            return Ok(retain_surface_base(segments));
        }

        let mut segments = Vec::new();
        self.append_aggregate_leaf_segments(&mut segments, base, struct_name, 0, field_name)?;
        Ok(retain_surface_base(segments))
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
            C0Type::Int64Array(_, length) => Some((length, 8, CType::Int64)),
            C0Type::Int128Array(length) => Some((length, 16, CType::Int128)),
            C0Type::UInt64Array(_, length) => Some((length, 8, CType::UInt64)),
            C0Type::UInt128Array(length) => Some((length, 16, CType::UInt128)),
            C0Type::CharArray(crate::languages::c::syntax::PlainChar::Unsigned, length)
            | C0Type::UInt8Array(length) => Some((length, 1, CType::UInt8)),
            C0Type::CharArray(crate::languages::c::syntax::PlainChar::Signed, length)
            | C0Type::Int8Array(length) => Some((length, 1, CType::Int8)),
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
                    access_class: None,
                    source: Default::default(),
                },
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(length)),
                surface: ContractSegmentSurface::Field {
                    base: surface_base.map(Box::new),
                    name: field_name.to_string(),
                    element_width: Some(element_width),
                    element_type: Some(element_type),
                },
            };
        }
        let element_width = match field.c_type {
            C0Type::Char(_) => 1,
            C0Type::UInt8 => 1,
            C0Type::Int8 => 1,
            C0Type::Int16 | C0Type::UInt16 => 2,
            C0Type::Int64(_) | C0Type::UInt64(_) => 8,
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
        self.refuse_trait_receiver_field(named_place_base(&base).map(String::as_str))?;
        let Some(field) = self.resolve_field_metadata(&base, field_name)? else {
            return Ok(CExpression::Load(Box::new(base)));
        };
        Ok(CExpression::TypedLoad {
            pointer: Box::new(self.member_field_pointer(base, &field)),
            value_type: field.c_type.to_kernel_type(),
            volatile: false,
            pointee_constant: field.pointee_constant,
            access_class: None,
            source: Default::default(),
        })
    }

    /// A crate trait method's interface does not know its receiver's type,
    /// so it has no field of `self` to read.
    fn refuse_trait_receiver_field(&self, base: Option<&str>) -> Result<(), ClickError> {
        if self.rust_trait_interface.is_some() && base == Some("self") {
            return Err(self.error(
                "a trait method's interface reads nothing through `self`, whose type it does not know",
            ));
        }
        Ok(())
    }

    fn resolve_c0_field_load(
        &self,
        base: C0Expression,
        field_name: &str,
    ) -> Result<Option<C0Expression>, ClickError> {
        if let C0Expression::Variable(name) = &base {
            self.refuse_trait_receiver_field(Some(name))?;
        }
        let struct_name = match &base {
            C0Expression::Variable(base_name) => self
                .names
                .struct_params
                .get(base_name)
                .or_else(|| self.names.aggregate_objects.get(base_name)),
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
                        access_class: None,
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
                    access_class: None,
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
            .names
            .struct_params
            .get(base_name)
            .or_else(|| self.names.aggregate_objects.get(base_name))
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
            ContractExpression::CUnary {
                lowered: CExpression::Cast { pointee_struct, .. },
                ..
            }
            | ContractExpression::CFragment(CExpression::Cast { pointee_struct, .. }) => {
                pointee_struct.clone()
            }
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .names
                .struct_params
                .get(name)
                .or_else(|| self.names.aggregate_objects.get(name))
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
        let Some(field) = self.names.arm_binding_types.get(base_name) else {
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
                | C0Type::CharArray(_, _)
                | C0Type::UInt8Array(_)
                | C0Type::Int128Array(_)
                | C0Type::Int64Array(_, _)
                | C0Type::UInt128Array(_)
                | C0Type::UInt64Array(_, _)
        ) {
            let width = match field.c_type {
                C0Type::Int64Array(_, _) | C0Type::UInt64Array(_, _) => 8,
                C0Type::Int128Array(_) | C0Type::UInt128Array(_) => 16,
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
        if matches!(field.c_type, C0Type::Int64(_) | C0Type::UInt64(_)) {
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
        if matches!(field.c_type, C0Type::Int8 | C0Type::Char(_) | C0Type::UInt8) {
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

    fn member_field_pointer(&self, base: CExpression, field: &ResolvedField) -> CExpression {
        let pointer = self.offset_field_pointer(base, field.offset_bytes);
        if field.byte_width == 0 {
            return pointer;
        }
        CExpression::Subobject {
            pointer: Box::new(pointer),
            width: field.byte_width,
        }
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
    /// consuming it. Contracts retain the explicit target layout through
    /// object-pointer conversions via `void *`.
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
        operand: &CExpression,
        struct_name: &str,
    ) -> Result<(), ClickError> {
        // Integer casts name the complete word's reconstructed pointer.
        // Unknown types (notably `result`) are checked after elaboration.
        if matches!(
            crate::surface::validation::infer_c_expression_type(
                operand,
                &self.names.c_parameter_types,
            ),
            None | Some(C0Type::Int64(_) | C0Type::UInt64(_))
        ) {
            return Ok(());
        }
        // An explicit conversion through void retains its target layout on
        // the expression. It does not assign a layout to the source parameter.
        if matches!(
            operand,
            CExpression::Cast {
                target_type: CType::VoidPointer,
                ..
            }
        ) {
            return Ok(());
        }
        let name = match operand {
            CExpression::Variable(name) => Some(name.as_str()),
            _ => None,
        };
        let Some(name) =
            name.filter(|name| self.names.contains(NameKind::VoidPointerParameter, name))
        else {
            return Err(self.error(
                "a struct pointer cast applies to a `void *` parameter of the function under contract",
            ));
        };
        match self.names.parameter_struct_casts.get(name) {
            Some(previous) if previous != struct_name => Err(self.error(format!(
                "parameter `{name}` is already cast to `struct {previous}`; a contract casts a parameter to one struct"
            ))),
            _ => {
                self.names.parameter_struct_casts
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
            let source_operand = operand;
            let Some(operand) = contract_expression_as_c_fragment(&source_operand) else {
                return Err(self.error(
                    "struct pointer cast expects a current C `void *` expression; put old(...) around the whole cast for an entry-state value",
                ));
            };
            let integer_source = crate::surface::validation::infer_c_expression_type(
                &operand,
                &self.names.c_parameter_types,
            )
            .is_some_and(|ty| matches!(ty, C0Type::Int64(_) | C0Type::UInt64(_)));
            if !integer_source {
                self.record_parameter_struct_cast(&operand, &cast.struct_name)?;
            }
            return Ok(crate::surface::lowering::contract_c_unary(
                source_operand,
                CExpression::Cast {
                    expression: Box::new(operand),
                    target_type: CType::Int32Pointer,
                    integer_mode: crate::kernel::CIntegerCastMode::Standard,
                    pointee_struct: Some(cast.struct_name),
                    pointee_volatile: false,
                    pointee_constant: cast.pointee_constant,
                    explicit_qualification: false,
                },
            ));
        }
        if self.starts_contract_scalar_cast() {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            let parsed_type = self.parse_type()?;
            let target_type = parsed_type.c_type.to_kernel_type();
            if parsed_type.reference
                || (target_type.is_pointer()
                    && (parsed_type.constant || parsed_type.pointee_constant))
            {
                return Err(self.error("contract cast targets must be unqualified native types; byte views inherit the source qualification"));
            }
            self.expect(Token::RParen)?;
            let operand = self.parse_contract_unary_at_depth(depth + 1)?;
            let historical = crate::surface::validation::contains_old_expression(&operand)
                || crate::surface::validation::contains_at_expression(&operand);
            // Integer casts consume the value observed by their operand.
            // Other cast families retain their current-expression validation.
            let integer_target = matches!(
                target_type,
                CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Int64
                    | CType::UInt64
                    | CType::Int128
                    | CType::UInt128
            );
            if historical && !integer_target {
                return Err(self.error("scalar cast expects a current expression; put old(...) around the whole cast for an entry-state value"));
            }
            let expression =
                contract_expression_as_c_fragment(&operand).unwrap_or(CExpression::Value(int32(0)));
            if target_type == CType::VoidPointer {
                crate::surface::validation::validate_void_pointer_cast_source(
                    &expression,
                    &self.names.c_parameter_types,
                    "contract expression",
                )?;
            }
            return Ok(ContractExpression::CUnary {
                operand: Box::new(operand),
                lowered: CExpression::Cast {
                    expression: Box::new(expression),
                    target_type,
                    // This cast was written in the contract. Pointer targets
                    // use the specification cast rule, not the C conversion
                    // marker also used for inserted pointer coercions. Authored
                    // void and byte casts select the enclosing-object view.
                    integer_mode: if target_type.is_pointer() {
                        crate::kernel::CIntegerCastMode::Standard
                    } else {
                        crate::kernel::CIntegerCastMode::CConversion
                    },
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            });
        }
        if self.peek() == Some(&Token::Minus) {
            self.check_unary_nesting_limit(depth)?;
            if let Some((literal, end)) = self.negated_rust_literal() {
                self.position = end;
                return literal
                    .contract_expression(true)
                    .map_err(|message| self.error(message));
            }
            if self.peek_next() == Some(&Token::Int64MinimumMagnitude) {
                self.position += 2;
                return Ok(ContractExpression::CFragment(CExpression::Value(
                    CValue::Int64(Bitvector32Term::Int64Constant(i64::MIN)),
                )));
            }
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
            let source_pointer = pointer.clone();
            let Some(pointer) = contract_expression_as_c_fragment(&pointer) else {
                return Err(
                    self.error("pointer dereference is only supported on current C fragments")
                );
            };
            return Ok(crate::surface::lowering::contract_c_unary(
                source_pointer,
                CExpression::Load(Box::new(pointer)),
            ));
        }
        if self.peek() == Some(&Token::Amp) && self.at_reference_parameter_address() {
            return self.parse_reference_parameter_address();
        }
        if self.peek() == Some(&Token::Amp) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            let expression = self.parse_contract_unary_at_depth(depth + 1)?;
            if let ContractExpression::Field {
                base,
                offset_bytes,
                lowered,
                ..
            } = &expression
            {
                // Address the typed field lvalue without evaluating its load.
                // This preserves the field's pointee type and qualifiers even
                // when the aggregate itself uses byte-addressed storage.
                // The member is its own subobject, as the C frontend narrows
                // `&p->f` (`design/pointer-subobject-extents.md`), so a
                // contract's `&pair->second` is the program's pointer value
                // and is not equal to `&pair->first + 1`.
                if let CExpression::TypedLoad { value_type, .. } = lowered
                    && value_type.pointer_to().is_some()
                {
                    return Ok(ContractExpression::CUnary {
                        operand: Box::new(expression.clone()),
                        lowered: CExpression::AddressOf(Box::new(contract_member_lvalue(lowered))),
                    });
                }
                let source_base = (**base).clone();
                let Some(base) = contract_expression_as_c_fragment(base) else {
                    return Err(self.error("address-of field requires a current C pointer base"));
                };
                return Ok(crate::surface::lowering::contract_c_unary(
                    source_base,
                    CExpression::PointerOffsetBytes {
                        pointer: Box::new(base),
                        bytes: *offset_bytes,
                    },
                ));
            }
            let source_expression = expression.clone();
            let Some(expression) = contract_expression_as_c_fragment(&expression) else {
                return Err(self.error("address-of is only supported on current C expressions"));
            };
            return Ok(crate::surface::lowering::contract_c_unary(
                source_expression,
                CExpression::AddressOf(Box::new(expression)),
            ));
        }

        self.parse_contract_postfix()
    }

    fn parse_contract_postfix(&mut self) -> Result<ContractExpression, ClickError> {
        let expression = self.parse_contract_primary()?;
        self.parse_contract_postfix_suffix(expression)
    }

    /// Native parameter and result aliases name their referents.
    fn is_reference_binding(&self, name: &str) -> bool {
        self.names.contains(NameKind::ReferenceParameter, name)
            || (self.current_reference_result && name == "result")
    }

    fn reference_binding_carrier(&self, name: &str) -> String {
        if self.current_reference_result && name == "result" {
            "result".to_string()
        } else {
            syntax::reference_carrier_name(name)
        }
    }

    /// The address of a reference referent (`&value` or `&result`) is its
    /// existing pointer carrier. Keep this out of the recursive parser frame.
    #[inline(never)]
    fn at_reference_parameter_address(&self) -> bool {
        matches!(self.peek_next(), Some(Token::Ident(name)) if self.is_reference_binding(name))
            && !matches!(
                self.tokens.get(self.position + 2),
                Some(Token::Arrow | Token::Dot | Token::LBracket)
            )
    }

    /// Consumes `&name` where [`Self::at_reference_parameter_address`] holds.
    #[inline(never)]
    fn parse_reference_parameter_address(&mut self) -> Result<ContractExpression, ClickError> {
        let Some(Token::Ident(name)) = self.peek_next() else {
            return Err(self.error("expected a reference binding after `&`"));
        };
        let carrier = self.reference_binding_carrier(name);
        self.position += 2;
        Ok(ContractExpression::CFragment(CExpression::Variable(
            carrier,
        )))
    }

    /// A reference parameter's name is its referent. The pointer that
    /// carries it is named as the referent's address. A scalar referent is
    /// the element behind that pointer; a struct referent is reached through
    /// the pointer, as its fields are. Out of line for the same reason as
    /// [`Self::parse_reference_parameter_address`].
    #[inline(never)]
    fn resolve_reference_parameter(
        &mut self,
        mut expression: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        if let ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) = &expression
            && self.is_reference_binding(name)
        {
            let name = name.clone();
            let carrier = self.reference_binding_carrier(&name);
            let is_struct = self.names.struct_params.contains_key(&carrier);
            if is_struct && !matches!(self.peek(), Some(Token::Arrow | Token::Dot)) {
                return Err(self.error(format!(
                    "`{name}` is a struct reference; name a field as `{name}.field`, or its address as `&{name}`"
                )));
            }
            expression = ContractExpression::CFragment(CExpression::Variable(carrier));
            if !is_struct {
                if self.peek() == Some(&Token::LBracket) {
                    return Err(self.error(format!(
                        "`{name}` is a reference and names the value it refers to, so it takes no index; write `{name}`"
                    )));
                }
                expression = ContractExpression::Index(
                    Box::new(expression),
                    Box::new(ContractExpression::IntegerLiteral("0".to_string())),
                );
            }
        }
        Ok(expression)
    }

    // Keep postfix metadata and field-lowering temporaries out of the
    // recursive expression parser frame. Nested `match` expressions only
    // retain this small dispatcher while their primary is parsed.
    #[inline(never)]
    fn parse_contract_postfix_suffix(
        &mut self,
        mut expression: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        expression = self.resolve_reference_parameter(expression)?;
        let mut struct_name = match &expression {
            ContractExpression::CUnary {
                lowered: CExpression::Cast { pointee_struct, .. },
                ..
            }
            | ContractExpression::CFragment(CExpression::Cast { pointee_struct, .. }) => {
                pointee_struct.clone()
            }
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .names
                .struct_params
                .get(name)
                .or_else(|| self.names.aggregate_objects.get(name))
                .cloned(),
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.contract_expression_struct_name(inner),
            _ => None,
        };
        // A struct double pointer indexes pointer slots, not struct objects.
        if let ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) = &expression
            && self
                .names
                .struct_params
                .contains_key(&struct_pointer_pointer_key(name))
        {
            struct_name = None;
        }
        let mut union_name: Option<String> = None;
        let mut struct_array_element_width = match &expression {
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .names
                .contains(NameKind::StructArrayParameter, name)
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
                .names
                .global_array_shapes
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
                    let index = self.parse_place_index()?;
                    self.expect(Token::RBracket)?;
                    if let Some(element_width) = struct_array_element_width.or_else(|| {
                        struct_name
                            .as_ref()
                            .and_then(|name| self.struct_layouts.get(name))
                            .map(|layout| layout.size_bytes())
                    }) && let Some(base_struct_name) = &struct_name
                        && self.struct_layouts.contains_key(base_struct_name)
                    {
                        let base = contract_expression_as_c_fragment(&expression)
                            .ok_or_else(|| {
                                self.error(
                                    "struct array indexing is only supported on current C fragments",
                                )
                            })?;
                        let source_index = index.clone();
                        let index = contract_expression_as_c_fragment(&index).ok_or_else(|| {
                            self.error("struct array indices must be current C expressions")
                        })?;
                        let mut indexes = vec![source_index];
                        while struct_array_shape.is_some() && self.peek() == Some(&Token::LBracket)
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            contract_expression_as_c_fragment(&next_index).ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                            indexes.push(next_index);
                        }
                        let dimensions = struct_array_shape.clone().unwrap_or_else(|| vec![1]);
                        let offset = if let Some(shape) = struct_array_shape.take() {
                            if indexes.len() != shape.len() {
                                return Err(self.error(format!(
                                    "multidimensional struct array field requires {} indices, got {}",
                                    shape.len(),
                                    indexes.len()
                                )));
                            }
                            flatten_array_indices(
                                indexes
                                    .iter()
                                    .map(|index| {
                                        contract_expression_as_c_fragment(index)
                                            .expect("validated C index")
                                    })
                                    .collect(),
                                &shape,
                            )
                        } else {
                            index
                        };
                        let stride = struct_byte_stride(offset, element_width);
                        // Keep the subscripts as written beside the element
                        // address, so the access prints back as `a[i]`
                        // rather than as the byte arithmetic it lowers to.
                        expression = ContractExpression::ArrayIndex {
                            base: Box::new(expression),
                            indexes,
                            dimensions,
                            lowered: {
                                let address = CExpression::Add(
                                    Box::new(struct_byte_base(base)),
                                    Box::new(stride),
                                );
                                if matches!(self.peek(), Some(Token::Arrow | Token::Dot)) {
                                    address
                                } else {
                                    // A bare struct subscript retains the legacy
                                    // first-word read; a following field uses the
                                    // byte-scaled address of the whole element.
                                    CExpression::TypedLoad {
                                        pointer: Box::new(address),
                                        value_type: crate::kernel::CType::Int32,
                                        volatile: false,
                                        pointee_constant: false,
                                        access_class: None,
                                        source: Default::default(),
                                    }
                                }
                            },
                        };
                        struct_array_element_width = None;
                    } else if let Some(shape) = struct_array_shape.take() {
                        contract_expression_as_c_fragment(&index).ok_or_else(|| {
                            self.error("struct array indices must be current C expressions")
                        })?;
                        let mut indexes = vec![index.clone()];
                        while self.peek() == Some(&Token::LBracket)
                            && !self.contract_bracket_is_range()
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            contract_expression_as_c_fragment(&next_index).ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                            indexes.push(next_index);
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error(format!(
                                "multidimensional scalar array field requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let offset = flatten_array_indices(
                            indexes
                                .iter()
                                .map(|index| {
                                    contract_expression_as_c_fragment(index)
                                        .expect("validated C index")
                                })
                                .collect(),
                            &shape,
                        );
                        // Keep the source rank of a multidimensional field
                        // access, as a global array access does: the
                        // flattened index alone prints as one subscript,
                        // which does not parse back.
                        expression = match contract_expression_as_c_fragment(&expression) {
                            Some(lowered_base) if indexes.len() > 1 => {
                                ContractExpression::ArrayIndex {
                                    base: Box::new(expression),
                                    indexes,
                                    dimensions: shape.clone(),
                                    lowered: CExpression::Index(
                                        Box::new(lowered_base),
                                        Box::new(offset),
                                    ),
                                }
                            }
                            _ => {
                                let offset = indexes
                                    .into_iter()
                                    .enumerate()
                                    .map(|(index, expression)| {
                                        let stride = shape[index + 1..].iter().fold(
                                            1u32,
                                            |stride, dimension| {
                                                stride
                                                    .checked_mul(*dimension)
                                                    .expect("validated array stride")
                                            },
                                        );
                                        if stride == 1 {
                                            expression
                                        } else {
                                            ContractExpression::Multiply(
                                                Box::new(expression),
                                                Box::new(ContractExpression::CFragment(
                                                    CExpression::Value(int32(stride)),
                                                )),
                                            )
                                        }
                                    })
                                    .reduce(|left, right| {
                                        ContractExpression::Add(Box::new(left), Box::new(right))
                                    })
                                    .expect("array has indices");
                                ContractExpression::Index(Box::new(expression), Box::new(offset))
                            }
                        };
                        struct_name = None;
                        union_name = None;
                        struct_array_element_width = None;
                    } else if let Some(shape) = scalar_array_shape.take() {
                        contract_expression_as_c_fragment(&index).ok_or_else(|| {
                            self.error("global array indices must be current C expressions")
                        })?;
                        let mut indexes = vec![index.clone()];
                        while self.peek() == Some(&Token::LBracket)
                            && !self.contract_bracket_is_range()
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            contract_expression_as_c_fragment(&next_index).ok_or_else(|| {
                                self.error("global array indices must be current C expressions")
                            })?;
                            indexes.push(next_index);
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
                        let offset = flatten_array_indices(
                            indexes
                                .iter()
                                .map(|index| {
                                    contract_expression_as_c_fragment(index)
                                        .expect("validated C index")
                                })
                                .collect(),
                            &shape,
                        );
                        expression = ContractExpression::ArrayIndex {
                            base: Box::new(expression),
                            indexes,
                            dimensions: shape.clone(),
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
                        && self.names.value_binders.contains_key(owner)
                    {
                        if self.peek() != Some(&Token::Dot) {
                            return Err(self.error("binder parameters use `.`, not `->`"));
                        }
                        let owner = owner.clone();
                        self.position += 1;
                        let parameter = self.expect_ident("resource parameter name")?;
                        expression = ContractExpression::CFragment(CExpression::Variable(format!(
                            "{owner}.{parameter}"
                        )));
                        continue;
                    }
                    if let ContractExpression::CFragment(CExpression::Variable(owner)) = &expression
                        && self.peek() == Some(&Token::Dot)
                        && self.names.ended_instance_names.contains(owner)
                        && !self.names.is_bound(owner)
                    {
                        return Err(self.unknown_instance(owner, "resource instance"));
                    }
                    if let ContractExpression::CFragment(CExpression::Variable(owner)) = &expression
                        && let Some((identity, resource_name)) =
                            self.names.resource_bindings.get(owner).cloned()
                    {
                        if self.peek() != Some(&Token::Dot) {
                            return Err(self.error("resource fields use `.`, not `->`"));
                        }
                        let owner = owner.clone();
                        self.position += 1;
                        let field = self.expect_ident("resource field name")?;
                        if let Some(hidden) = self.hidden_child_field(&owner, &field) {
                            expression = hidden;
                            continue;
                        }
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
                    let field_name = self.expect_field_name()?;
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
                            pointee_struct: field
                                .struct_name
                                .clone()
                                .filter(|_| field.c_type.is_pointer()),
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
                        let pointer = self.member_field_pointer(base, &field);
                        struct_name = field.struct_name.clone();
                        union_name = field.union_name.clone();
                        struct_array_element_width = field.array_element_width;
                        struct_array_shape = field.array_shape.clone();
                        scalar_array_shape = None;
                        expression = ContractExpression::Field {
                            pointee_struct: field
                                .struct_name
                                .clone()
                                .filter(|_| field.c_type.is_pointer()),
                            base: Box::new(surface_base),
                            field: field_name,
                            lowered: lowered_field_expression(pointer, &field),
                            offset_bytes: field.offset_bytes,
                        };
                    } else {
                        expression = ContractExpression::Field {
                            pointee_struct: None,
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
        let bool_arms = std::mem::take(&mut self.bool_value_context);
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
                .filter(|binding| {
                    self.names
                        .insert(NameKind::ContractBinding, (*binding).clone())
                })
                .cloned()
                .collect::<Vec<_>>();
            let body = self.parse_branch_value(bool_arms);
            for binding in newly_bound {
                self.names.remove(NameKind::ContractBinding, &binding);
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
        // A proof may need the previous binding of a name shadowed by an
        // introduced quantifier. Keep the qualification on the variable name
        // until the proof scope substitutes its checked binder identity.
        if self.proof_nesting > 0
            && self.peek_ident() == Some("outer")
            && self.peek_next() == Some(&Token::Dot)
        {
            let start = self.position;
            let mut depth = 0;
            while self.peek_ident() == Some("outer") && self.peek_next() == Some(&Token::Dot) {
                self.position += 2;
                depth += 1;
            }
            if let Some(name) = self.peek_ident().map(str::to_string) {
                self.position += 1;
                return Ok(ContractExpression::CFragment(CExpression::Variable(
                    format!("{}{}", "outer.".repeat(depth), name),
                )));
            }
            self.position = start;
        }
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
            let allocation_size = self.whole_allocation_size_at(self.position);
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
                // A Rust sidecar names the type as Rust does, `crate::Node`.
                let parsed_type = if self.verifies_rust() {
                    self.parse_rust_type()?
                } else {
                    self.parse_type()?
                };
                self.expect(Token::RParen)?;
                if parsed_type.c_type == C0Type::Void {
                    return Err(self.error("`sizeof(void)` is not supported"));
                }
                if let C0Type::Parameter(_) = parsed_type.c_type {
                    return Err(self.error(
                        "the size of an abstract type is not the same at every type argument",
                    ));
                }
                match &parsed_type.struct_name {
                    // A C++ record named as the source names it, `Node`.
                    Some(name) if !parsed_type.struct_pointer => {
                        // A generic template's record at abstract arguments
                        // is laid out at a word for each value, which its
                        // instances are not: its size is not one number.
                        if !allocation_size && self.layout_holds_abstract_value(name) {
                            return Err(self.error(format!(
                                "the size of `{}` depends on its abstract type arguments",
                                crate::languages::display_source_names(name)
                            )));
                        }
                        self.struct_layouts
                            .get(name)
                            .ok_or_else(|| {
                                self.error(format!("unknown struct declaration `{name}`"))
                            })?
                            .size_bytes()
                    }
                    _ => parsed_type.c_type.abi_size_bytes(),
                }
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
            self.refuse_result_in_snapshot_expression(None, &expression)?;
            return Ok(ContractExpression::Old(Box::new(expression)));
        }

        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let selector = self.parse_snapshot_selector()?;
            self.expect(Token::Comma)?;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            self.refuse_result_in_snapshot_expression(Some(&selector), &expression)?;
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
            let source_pointer = pointer;
            let Some(pointer) = contract_expression_as_c_fragment(&source_pointer) else {
                return Err(self.error("address expects a current C pointer expression"));
            };
            self.expect(Token::RParen)?;
            let cast = CExpression::Cast {
                expression: Box::new(pointer),
                target_type: CType::UInt64,
                integer_mode: crate::kernel::CIntegerCastMode::Standard,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            };
            self.address_casts.insert(cast.clone());
            return Ok(crate::surface::lowering::contract_c_unary(
                source_pointer,
                cast,
            ));
        }

        if self.peek_ident() == Some("byte_offset") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let pointer = self.parse_contract_expression()?;
            let source_pointer = pointer;
            let Some(pointer) = contract_expression_as_c_fragment(&source_pointer) else {
                return Err(self.error("byte offset expects a current C pointer expression"));
            };
            self.expect(Token::Comma)?;
            let bytes = match self.next() {
                Some(Token::Number(bytes)) => bytes,
                Some(token) => {
                    return Err(self.error(format!(
                        "byte offset expects a nonnegative byte count, got {token}"
                    )));
                }
                None => {
                    return Err(self
                        .error("byte offset expects a nonnegative byte count, got end of input"));
                }
            };
            self.expect(Token::RParen)?;
            return Ok(crate::surface::lowering::contract_c_unary(
                source_pointer,
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
            let source_pointer = pointer.clone();
            if let Some(pointer) = contract_expression_as_c_fragment(&pointer) {
                return Ok(crate::surface::lowering::contract_c_unary(
                    source_pointer,
                    CExpression::TypedLoad {
                        pointer: Box::new(pointer),
                        value_type,
                        volatile: false,
                        pointee_constant: false,
                        access_class: None,
                        source: Default::default(),
                    },
                ));
            }
            // The operand remains authoritative during spec lowering. A
            // historical pointer selects an address, while this load uses
            // the surrounding clause's memory snapshot.
            let pointer = CExpression::Value(int32(0));
            return Ok(ContractExpression::CUnary {
                operand: Box::new(source_pointer),
                lowered: CExpression::TypedLoad {
                    pointer: Box::new(pointer),
                    value_type,
                    volatile: false,
                    pointee_constant: false,
                    access_class: None,
                    source: Default::default(),
                },
            });
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
                if let Some(field) = self.names.resource_fields.get(&name) {
                    return Ok(ContractExpression::ResourceField(field.clone()));
                }
                if self.names.contains_any(NameKind::VALUES, &name)
                {
                    Ok(ContractExpression::Binding(name))
                } else {
                    match self.names.algebraic_params.get(&name) {
                        Some((algebraic_type, binder_index)) => {
                            Ok(ContractExpression::AlgebraicVariable {
                                name,
                                algebraic_type: algebraic_type.clone(),
                                binder_index: *binder_index,
                            })
                        }
                        None => match self.bool_literal_spelling(&name) {
                            Some(value) => Ok(bool_literal(value)),
                            None => Ok(self.c_variable_expression(name)),
                        },
                    }
                }
            }
            // Keep unsuffixed specification numerals contextual until typing.
            // A surrounding conversion or Integer-valued expression may supply
            // that context even when the enclosing theorem has only C params.
            Some(Token::Number(value)) => Ok(ContractExpression::IntegerLiteral(value.to_string())),
            Some(Token::RustInteger(literal)) => literal.contract_expression(false).map_err(|message| self.error(message)),
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
            Some(Token::Int64MinimumMagnitude) => Err(self.error(
                "positive int64 literal `9223372036854775808i64` is outside 0..9223372036854775807; this magnitude is allowed only after unary minus",
            )),
            Some(Token::Int64Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::Int64(Bitvector32Term::Int64Constant(value))),
            )),
            Some(Token::UInt64Number(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(value))),
            )),
            Some(Token::CharLiteral(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(self.character_constant_value(value)?),
            )),
            Some(Token::LParen) => {
                let start = self.position;
                let expression = self.parse_contract_expression()?;
                if self.continues_as_rust_bool_value() {
                    // Rust's `(x > 3)` is a `bool` value: the proposition's
                    // truth value, as in a `-> bool` body.
                    self.position = start;
                    let proposition = self.parse_proposition()?;
                    self.expect(Token::RParen)?;
                    return proposition_bool_value(proposition)
                        .map_err(|message| self.error(message));
                }
                if self.peek() == Some(&Token::DotDot) {
                    self.position += 1;
                    let end = self.parse_contract_expression()?;
                    self.expect(Token::RParen)?;
                    return self.parse_range_fold(expression, end);
                }
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected contract expression, got {token}"))),
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
                        "expected `,` or `]` after sequence element, got {token}"
                    )));
                }
                None => return Err(self.error("expected `]` after sequence element")),
            }
        }
    }

    fn parse_contract_value_let_expression(&mut self) -> Result<ContractExpression, ClickError> {
        let bool_body = std::mem::take(&mut self.bool_value_context);
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
            let binding_was_in_scope = !self
                .names
                .insert(NameKind::ContractBinding, binding.name.clone());
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

        let body = self.parse_branch_value(bool_body);
        for (name, _, _, binding_was_in_scope, previous_integer_context) in bindings.iter().rev() {
            self.integer_literal_context = *previous_integer_context;
            if !*binding_was_in_scope {
                self.names.remove(NameKind::ContractBinding, name);
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

    /// The value of an `if` branch, `match` arm or `let` body: a `bool`
    /// value when the enclosing expression is one.
    fn parse_branch_value(&mut self, bool_value: bool) -> Result<ContractExpression, ClickError> {
        if bool_value {
            self.parse_bool_value()
        } else {
            self.parse_contract_expression()
        }
    }

    /// A value of a `bool` context: a pure function's `-> bool` body, or a
    /// branch of one. A proposition written here is its truth value, so
    /// `x > 0` is `if x > 0 { true } else { false }`; a value written alone
    /// is itself. `if`, `match` and `let` pass the context to their branches.
    fn parse_bool_value(&mut self) -> Result<ContractExpression, ClickError> {
        if matches!(self.peek_ident(), Some("if" | "match" | "let"))
            && self.peek_next() != Some(&Token::LParen)
        {
            let start = self.position;
            self.bool_value_context = true;
            let value = self.parse_contract_primary();
            self.bool_value_context = false;
            // `let ... where` is a proposition: read it as one below.
            if !(value.is_err()
                && self
                    .tokens
                    .get(start)
                    .is_some_and(|token| matches!(token, Token::Ident(word) if word == "let")))
            {
                return value;
            }
            self.position = start;
        }
        let proposition = self.parse_proposition()?;
        proposition_bool_value(proposition).map_err(|message| self.error(message))
    }

    /// In a Rust sidecar, whether a parenthesized value continues as a
    /// comparison or connective, which Rust reads as a `bool` value.
    fn continues_as_rust_bool_value(&self) -> bool {
        self.verifies_rust()
            && match self.peek() {
                Some(
                    Token::EqualEqual
                    | Token::BangEqual
                    | Token::LessThan
                    | Token::LessEqual
                    | Token::GreaterThan
                    | Token::GreaterEqual,
                ) => true,
                Some(Token::Ident(word)) => matches!(word.as_str(), "and" | "or" | "implies"),
                _ => false,
            }
    }

    /// Whether the token after a value ends the proposition it stands in.
    fn at_proposition_end(&self) -> bool {
        match self.peek() {
            None => true,
            Some(
                Token::Semicolon
                | Token::RParen
                | Token::RBrace
                | Token::LBrace
                | Token::RBracket
                | Token::Comma
                | Token::FatArrow,
            ) => true,
            Some(Token::Ident(word)) => matches!(
                word.as_str(),
                "and" | "or" | "implies" | "by" | "using" | "else" | "if" | "produces"
            ),
            Some(_) => false,
        }
    }

    fn parse_contract_if_expression(&mut self) -> Result<ContractExpression, ClickError> {
        let bool_branches = std::mem::take(&mut self.bool_value_context);
        self.position += 1;
        // These children are boxed in the AST. Box each one as soon as it is
        // parsed so a nested conditional does not retain large enum values in
        // every parser stack frame while parsing its next child.
        let condition = Box::new(self.parse_proposition()?);
        self.expect(Token::LBrace)?;
        let then_branch = Box::new(self.parse_branch_value(bool_branches)?);
        self.expect(Token::RBrace)?;
        if self.peek_ident() != Some("else") {
            return Err(self.error("expected `else` in `if` expression"));
        }
        self.position += 1;
        self.expect(Token::LBrace)?;
        let else_branch = Box::new(self.parse_branch_value(bool_branches)?);
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
            let (mut argument, parsed_c_type) = self.parse_click_type()?;
            if let Some(parsed) = parsed_c_type {
                if !algebraic_field_c_type_supported(parsed.c_type) {
                    return Err(self.error("algebraic datatype arguments must be value types"));
                }
                if parsed.c_type.is_pointer()
                    && let Some(struct_name) = parsed.struct_name
                {
                    argument = ClickType::CObjectPointer {
                        c_type: parsed.c_type,
                        struct_name,
                    };
                }
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

    /// Refuses `result` in a snapshot that precedes the return; see
    /// [`snapshot_can_name_result`]. Kept out of the recursive parser frame,
    /// like the other helpers here.
    #[inline(never)]
    fn refuse_result_in_snapshot_expression(
        &self,
        selector: Option<&SnapshotSelector>,
        expression: &ContractExpression,
    ) -> Result<(), ClickError> {
        let mut names = BTreeSet::new();
        collect_current_contract_expression_variables(expression, &mut names);
        self.refuse_result_in_snapshot(selector, names.contains("result"))
    }

    #[inline(never)]
    fn refuse_result_in_snapshot_proposition(
        &self,
        selector: &SnapshotSelector,
        proposition: &ClickProposition,
    ) -> Result<(), ClickError> {
        self.refuse_result_in_snapshot(Some(selector), proposition_names_result(proposition))
    }

    fn refuse_result_in_snapshot(
        &self,
        selector: Option<&SnapshotSelector>,
        names_result: bool,
    ) -> Result<(), ClickError> {
        if !names_result || snapshot_can_name_result(selector) {
            return Ok(());
        }
        let snapshot = match selector {
            None => "old(...)".to_string(),
            Some(selector) => format!(
                "at({}, ...)",
                diagnostics::describe_snapshot_selector(selector)
            ),
        };
        Err(self.error(format!(
            "`result` cannot be named inside `{snapshot}`: that snapshot precedes the \
             return, where `result` does not exist yet; state the claim about `result` \
             outside the snapshot, or at `function.exit`"
        )))
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
            if let Some((literal, end)) = self.negated_rust_literal() {
                self.position = end;
                return literal
                    .c_expression(true)
                    .map_err(|message| self.error(message));
            }
            if self.peek_next() == Some(&Token::Int64MinimumMagnitude) {
                self.position += 2;
                return Ok(C0Expression::Int64Literal(i64::MIN));
            }
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
        if self.peek() == Some(&Token::Amp) && self.at_reference_parameter_address() {
            let Some(Token::Ident(name)) = self.peek_next() else {
                unreachable!()
            };
            let carrier = self.reference_binding_carrier(name);
            self.position += 2;
            return Ok(C0Expression::Variable(carrier));
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
                    expression = C0Expression::Index(Box::new(expression), Box::new(index), None);
                }
                Some(Token::Arrow | Token::Dot) => {
                    self.position += 1;
                    let field_name = self.expect_field_name()?;
                    let base = expression;
                    expression = self
                        .resolve_c0_field_load(base.clone(), &field_name)?
                        .unwrap_or_else(|| C0Expression::Load(Box::new(base), None));
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
            Some(Token::Ident(name)) if self.is_reference_binding(&name) => {
                let carrier = self.reference_binding_carrier(&name);
                let is_struct = self.names.struct_params.contains_key(&carrier);
                let carrier = C0Expression::Variable(carrier);
                Ok(if is_struct {
                    carrier
                } else {
                    C0Expression::Index(
                        Box::new(carrier),
                        Box::new(C0Expression::Int32Literal(0)),
                        None,
                    )
                })
            }
            Some(Token::Ident(name)) => {
                let name = self.take_rust_slice_len(&name).unwrap_or(name);
                Ok(C0Expression::Variable(name))
            }
            Some(Token::RustInteger(literal)) => literal.c_expression(false).map_err(|message| self.error(message)),
            Some(Token::Number(value)) => Ok(C0Expression::Int32Literal(value)),
            Some(Token::UInt8Number(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::UInt32Number(value)) => Ok(C0Expression::UInt32Literal(value)),
            Some(Token::Int64MinimumMagnitude) => Err(self.error(
                "positive int64 literal `9223372036854775808i64` is outside 0..9223372036854775807; this magnitude is allowed only after unary minus",
            )),
            Some(Token::Int64Number(value)) => Ok(C0Expression::Int64Literal(value)),
            Some(Token::UInt64Number(value)) => Ok(C0Expression::UInt64Literal(value)),
            Some(Token::CharLiteral(value)) => Ok(
                match self.character_constant_value(value)? {
                    CValue::Int32(Bitvector32Term::Constant(bits)) => C0Expression::Int32Literal(bits),
                    _ => C0Expression::UInt8Literal(value),
                },
            ),
            Some(Token::LParen) => {
                self.position -= 1;
                if self.peek_next() == Some(&Token::Ident("void".to_string()))
                    && self.tokens.get(self.position + 2) == Some(&Token::Star)
                    && self.tokens.get(self.position + 3) == Some(&Token::RParen)
                {
                    self.position += 4;
                    let operand = self.parse_ensure_unary()?;
                    crate::surface::validation::validate_void_pointer_cast_source(
                        &operand.to_kernel_expression(), &self.names.c_parameter_types, "contract expression"
                    )?;
                    return Ok(C0Expression::Cast {
                        expression: Box::new(operand),
                        c_type: C0Type::VoidPointer,
                        struct_name: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    });
                }
                if let Some(cast) = self.peek_struct_pointer_cast() {
                    self.consume_struct_pointer_cast(&cast)?;
                    let operand = self.parse_ensure_unary()?;
                    self.record_parameter_struct_cast(
                        &operand.to_kernel_expression(), &cast.struct_name,
                    )?;
                    return Ok(C0Expression::Cast {
                        expression: Box::new(operand),
                        c_type: C0Type::Int32Pointer,
                        struct_name: Some(cast.struct_name),
                        pointee_volatile: false,
                        pointee_constant: cast.pointee_constant,
                        explicit_qualification: false,
                    });
                }
                self.position += 1;
                let expression = self.parse_ensure_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected result expression, got {token}"))),
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

    /// The Click declaration a written name refers to: a selectively
    /// imported name reads as its library declaration here, and only here,
    /// since only a reference reads the import. A C function, a binder or a
    /// declaration of the same spelling keeps its own meaning.
    fn expect_reference_name(&mut self, expected: &str) -> Result<String, ClickError> {
        let at = self.error_context();
        let name = self.expect_ident(expected)?;
        let Some(position) = at.clone() else {
            return Ok(name);
        };
        self.symbols
            .reference(name, &position)
            .map_err(|refusal| self.error_at(at, refusal))
    }

    /// A C or C++ declaration name as written. A library path such as
    /// `list::append` is joined before parsing into the library declaration
    /// it names; a C++ namespace member of that spelling reads it back.
    fn expect_c_declaration_ident(&mut self, expected: &str) -> Result<String, ClickError> {
        let written = self
            .here()
            .and_then(|position| self.symbols.written_path(&position))
            .map(str::to_string);
        let name = self.expect_ident(expected)?;
        Ok(written.unwrap_or(name))
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
            Some(Token::RustInteger(literal)) => {
                literal
                    .c_expression(false)
                    .map_err(|message| self.error_at(at.clone(), message))?;
                literal
                    .digits
                    .parse::<u32>()
                    .map_err(|_| self.error_at(at, format!("expected {expected} to fit in uint32")))
            }
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
            Some(Token::RustInteger(literal)) => {
                let value = literal
                    .signed_i64(negative)
                    .map_err(|message| self.error_at(at, message))?;
                if parenthesized {
                    self.expect(Token::RParen)?;
                }
                return Ok(value);
            }
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

    fn starts_contract_scalar_cast(&self) -> bool {
        (self.peek() == Some(&Token::LParen)
            && self.peek_next() == Some(&Token::Ident("void".to_string()))
            && self.tokens.get(self.position + 2) == Some(&Token::Star)
            && self.tokens.get(self.position + 3) == Some(&Token::RParen))
            || self.peek() == Some(&Token::LParen)
                && matches!(self.peek_next(), Some(Token::Ident(name)) if matches!(name.as_str(), "int8" | "uint8" | "int16" | "uint16" | "uint32" | "int32" | "uint64" | "int64" | "int128" | "uint128"))
    }

    fn parenthesized_atom_continues_as_contract_expression(&self) -> bool {
        if self.starts_contract_scalar_cast() {
            return true;
        }
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

    /// A `;` after a closing brace ends nothing: it is accepted there and
    /// never required.
    fn skip_redundant_semicolon(&mut self) {
        if self.peek() == Some(&Token::Semicolon) {
            self.position += 1;
        }
    }

    fn error_at(&self, at: Option<SourcePosition>, message: impl Into<String>) -> ClickError {
        match at {
            Some(position) => ClickError::new(format!("{position}: {}", message.into()))
                .with_kind(ClickErrorKind::Syntax),
            None => ClickError::new(message).with_kind(ClickErrorKind::Syntax),
        }
    }

    /// The value of a sidecar character constant, as C gives it (C11
    /// 6.4.4.4p10): the `int` value of a plain `char` holding the byte. A
    /// byte below 0x80 means the same under every target and stays an
    /// unsigned byte; a higher byte needs the target's plain `char`.
    fn character_constant_value(&self, byte: u8) -> Result<CValue, ClickError> {
        if byte < 0x80 {
            return Ok(CValue::UInt8(Bitvector32Term::Constant(u32::from(byte))));
        }
        match self.plain_char {
            Some(syntax::PlainChar::Unsigned) => {
                Ok(CValue::UInt8(Bitvector32Term::Constant(u32::from(byte))))
            }
            Some(plain @ syntax::PlainChar::Signed) => Ok(CValue::Int32(Bitvector32Term::Constant(
                plain.character_value(byte) as i32 as u32,
            ))),
            None => Err(self.error(format!(
                "character constant `'{}'` has a target-dependent value, and no C target is selected here",
                (byte as char).escape_default()
            ))),
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
        Some("load_uint16") => Some(CType::UInt16),
        Some("load_uint32") => Some(CType::UInt32),
        Some("load_int64") => Some(CType::Int64),
        Some("load_uint64") => Some(CType::UInt64),
        Some("load_int32_pointer") => Some(CType::Int32Pointer),
        Some("load_uint8_pointer") => Some(CType::UInt8Pointer),
        Some("load_uint16_pointer") => Some(CType::UInt16Pointer),
        Some("load_int32_pointer_pointer") => Some(CType::Int32PointerPointer),
        Some("load_uint8_pointer_pointer") => Some(CType::UInt8PointerPointer),
        Some("load_uint16_pointer_pointer") => Some(CType::UInt16PointerPointer),
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
        Requirement::Resource(resource) => expand_aggregate_resource_clause(resource)
            .into_iter()
            .map(Requirement::Resource)
            .collect(),
        requirement => vec![requirement],
    }
}

fn expand_aggregate_ensure_clause(clause: EnsureClause) -> Vec<EnsureClause> {
    let EnsureClause {
        proof_bindings,
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
                proof_bindings: proof_bindings.clone(),
                name: name.clone(),
                ensure: Ensure::Resource(resource),
                proof: proof.clone(),
                borrowed,
                condition: condition.clone(),
            })
            .collect(),
        ensure => vec![EnsureClause {
            proof_bindings,
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

pub(in crate::surface) fn flatten_array_indices(
    indexes: Vec<CExpression>,
    dimensions: &[u32],
) -> CExpression {
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

/// A scalar member load whose place is narrowed to the member, for a
/// contract's `&p->f`: the address keeps the member's extent as the C
/// frontend's member address does. The specification lowers the address as
/// one C fragment, so the kernel evaluates the narrowing.
fn contract_member_lvalue(load: &CExpression) -> CExpression {
    let mut load = load.clone();
    if let CExpression::TypedLoad {
        pointer,
        value_type,
        ..
    } = &mut load
    {
        let width = value_type.byte_width();
        if width != 0 {
            let member = std::mem::replace(pointer.as_mut(), CExpression::Variable(String::new()));
            **pointer = CExpression::Subobject {
                pointer: Box::new(member),
                width,
            };
        }
    }
    load
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
            access_class: None,
            source: Default::default(),
        }
    }
}

/// The key under which the struct-parameter map records that a parameter is
/// a `struct T**`. It is not an identifier, so no name lookup finds it.
fn struct_pointer_pointer_key(name: &str) -> String {
    format!("{name}**")
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
            | C0Type::Char(_)
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64(_)
            | C0Type::UInt64(_)
            | C0Type::Int32Array(_)
            | C0Type::Int128Array(_)
            | C0Type::Int64Array(_, _)
            | C0Type::UInt128Array(_)
            | C0Type::UInt64Array(_, _)
            | C0Type::CharArray(_, _)
            | C0Type::UInt8Array(_)
    )
}

fn scalar_array_field_element(field: &ResolvedField) -> Option<(u32, CType)> {
    if field.struct_name.is_some() || field.union_name.is_some() || field.array_shape.is_none() {
        return None;
    }
    match field.c_type {
        C0Type::Int32Array(_) => Some((4, CType::Int32)),
        C0Type::Int64Array(_, _) => Some((8, CType::Int64)),
        C0Type::Int128Array(_) => Some((16, CType::Int128)),
        C0Type::UInt64Array(_, _) => Some((8, CType::UInt64)),
        C0Type::UInt128Array(_) => Some((16, CType::UInt128)),
        C0Type::CharArray(plain, _) => Some((1, plain.byte_type().to_kernel_type())),
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
                    .is_some_and(|(_, parent_proof, _)| *parent_proof);
                let proof = pending_proof_blocks != 0 || parent_is_proof;
                pending_proof_blocks = pending_proof_blocks.saturating_sub(1);
                // Proof `if` else blocks are read by the iterative spine
                // parser. They retain a scope, but no recursive parser frame.
                let recursive_proof = proof
                    && !matches!(index.checked_sub(1).and_then(|i| tokens.get(i)),
                        Some(Token::Ident(name)) if name == "else");
                brace_kinds.push((quantifier, proof, recursive_proof));
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
                if recursive_proof {
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
                if let Some((quantifier, _, recursive_proof)) = brace_kinds.pop() {
                    if quantifier {
                        quantifier_depth = quantifier_depth.saturating_sub(1);
                    }
                    if recursive_proof {
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
                integer_mode: crate::kernel::CIntegerCastMode::Standard,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            })),
            Box::new(uint64(alignment - 1)),
        ),
        operator: ComparisonOperator::Equal,
        right: uint64(0),
    }
}

/// The alignment fact a required complete-object clause carries: a live
/// object of a struct type is placed at that type's alignment, so a
/// required `*p` states `aligned(p, alignof(struct))`, which the
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
    let alignment = match &segment.surface {
        ContractSegmentSurface::Object(struct_name) => {
            struct_layouts.get(struct_name)?.alignment_bytes()
        }
        ContractSegmentSurface::ObjectPlace { layout, .. } => layout.layout.alignment_bytes(),
        _ => return None,
    };
    let alignment = u64::from(alignment);
    (alignment >= 2).then(|| aligned_proposition(segment.base.clone(), alignment))
}

fn requirement_object_alignment_facts(
    requirement: &Requirement,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
    out: &mut Vec<ClickProposition>,
) {
    match requirement {
        Requirement::Resource(clause) => out.extend(object_alignment_fact(clause, struct_layouts)),
        Requirement::LoadableSegment { .. } | Requirement::Proposition(_) => {}
    }
}

#[cfg(test)]
mod authority_resource_parser_tests {
    use super::*;

    #[test]
    fn parses_exact_unary_authority_resource_type() {
        let mut parser = Parser::new("authority(reference(p))").unwrap();
        let clause = parser.parse_declared_resource_call().unwrap();
        let ResourceClause::Declared {
            name,
            arguments,
            resource_type_arguments,
            ..
        } = clause
        else {
            panic!("authority is a declared built-in resource");
        };
        assert_eq!(name, "authority");
        assert!(arguments.is_empty());
        let [
            ResourceClause::Declared {
                name: protected_name,
                arguments: protected_arguments,
                ..
            },
        ] = resource_type_arguments.as_slice()
        else {
            panic!("authority has one protected resource type");
        };
        assert_eq!(protected_name, "reference");
        assert_eq!(protected_arguments.len(), 1);
        assert!(
            Parser::new("authority()")
                .unwrap()
                .parse_declared_resource_call()
                .is_err()
        );
        assert!(
            Parser::new("authority(reference(p), reference(q))")
                .unwrap()
                .parse_declared_resource_call()
                .is_err()
        );
    }

    #[test]
    fn unfold_authority_retains_protected_resource_type() {
        let mut parser = Parser::new("unfold(authority(reference(p)));").unwrap();
        let ProofTactic::UnfoldResource(ResourceClause::Declared {
            name,
            resource_type_arguments,
            ..
        }) = parser.parse_proof_tactic_inner().unwrap()
        else {
            panic!("authority unfold must be a resource tactic");
        };
        assert_eq!(name, "authority");
        assert_eq!(resource_type_arguments.len(), 1);
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
        assert!(parser.names.is_empty(NameKind::IntegerParameter));
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
        assert!(parser.names.is_empty(NameKind::IntegerParameter));
        assert!(parser.names.is_empty(NameKind::ContractBinding));
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

/// Preserve the C parser's exact, widened struct byte stride in sidecars.
fn struct_byte_stride(index: CExpression, width: u32) -> CExpression {
    CExpression::Multiply(
        Box::new(CExpression::Cast {
            expression: Box::new(index),
            target_type: crate::kernel::CType::Int64,
            integer_mode: crate::kernel::CIntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        }),
        Box::new(CExpression::Value(crate::kernel::int64(
            crate::kernel::Bitvector32Term::Int64Constant(i64::from(width)),
        ))),
    )
}

fn struct_byte_base(base: CExpression) -> CExpression {
    CExpression::Cast {
        expression: Box::new(base),
        target_type: crate::kernel::CType::UInt8Pointer,
        integer_mode: crate::kernel::CIntegerCastMode::Standard,
        pointee_struct: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    }
}

/// Every named child slot of a composite resource body: its unmatched
/// body's and each match arm's, whichever resource each one owns.
/// Whether `expression` or an operand of its arithmetic is a population
/// count, looking through `old`.
fn has_count_operand(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::ResourceCount(_) => true,
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            has_count_operand(left) || has_count_operand(right)
        }
        ContractExpression::Negate(inner) | ContractExpression::Old(inner) => {
            has_count_operand(inner)
        }
        _ => false,
    }
}

/// Whether `expression` does `+`, `-`, `*` or negation at its top, looking
/// through `old`.
fn has_arithmetic_spine(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Add(..)
        | ContractExpression::Subtract(..)
        | ContractExpression::Multiply(..)
        | ContractExpression::Negate(_) => true,
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => has_arithmetic_spine(inner),
        _ => false,
    }
}
