mod cpp_class_objects;
mod cpp_generic_templates;
mod cpp_model;
mod cpp_syntax;
mod float_bits;
mod name_table;
mod rust_generic_functions;
mod rust_generic_resources;
mod rust_generic_traits;
mod rust_literals;
mod rust_reference_authority;
use super::names;
use crate::kernel::{bits32_constant, constant_u32};
mod rust_syntax;
mod rust_trait_objects;
mod spec_arithmetic;
pub(crate) use rust_trait_objects::implementation_interface_contract;
pub(in crate::surface) use spec_arithmetic::mixed_narrow_arithmetic_message;
pub(super) use spec_arithmetic::written_integer_parameters;
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
    pub expression: ProgramExpression,
    pub address: Option<ProgramExpression>,
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
const RETIRED_CLOSE_INVARIANTS: &str = "`close_invariants` is retired: a `preserve` script closes the loop's invariants and `decreases` when it reaches the back edge, as a function proof closes its `ensures` at the exit, each by `solve()`; prove one that needs help with `have <invariant> by { ... }` before the back edge";
const RETIRED_GUARDED_BY: &str = "`guarded_by` is retired: a mutex protects the resource its checked `pthread_mutex_init` step deposits, so remove the clause and pass the resource to that step";
/// The index shape and scalar element type of a C global or static array
/// visible to one function's contract. Resource lowering only knows parameter
/// types, so the element type travels with the name to give a byte or
/// halfword slice its physical element width instead of the `int32` default.
#[derive(Clone, Debug)]
pub(super) struct GlobalArrayShape {
    pub(super) shape: Vec<u32>,
    pub(super) element_type: ProgramType,
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
    /// The locals of pointer type, whose arithmetic keeps its C meaning.
    pub(in crate::surface) pointers: BTreeSet<String>,
    /// For a Rust function, the iterator each loop advances, by loop index.
    pub(in crate::surface) loop_iterators:
        Vec<Option<crate::languages::interface::RustLoopIterator>>,
}

/// C declarations indexed from the selected source, independent of facts or execution.
#[derive(Clone, Default)]
pub(in crate::surface) struct SourceBindingIndex {
    declarations: BTreeMap<crate::kernel::LocalBindingId, SourceBindingInfo>,
    statics: BTreeMap<crate::kernel::StaticBindingId, SourceBindingInfo>,
    static_files: BTreeSet<Option<String>>,
    owners: BTreeMap<String, BTreeSet<Option<String>>>,
    sites: BTreeMap<(Option<String>, String, Vec<u32>, String), crate::kernel::LocalBindingId>,
    field_places: BTreeMap<String, BTreeMap<crate::kernel::BindingName, Vec<super::FieldPlace>>>,
}
impl SourceBindingIndex {
    fn info(&self, binding: &crate::kernel::BindingName) -> Option<&SourceBindingInfo> {
        match binding {
            crate::kernel::BindingName::ReferenceCarrier(referent) => self.info(referent),
            crate::kernel::BindingName::Local(id) => self.declarations.get(id),
            crate::kernel::BindingName::Static(id) => self.statics.get(id),
            crate::kernel::BindingName::Named(_)
            | crate::kernel::BindingName::ContractResult
            | crate::kernel::BindingName::ContractException
            | crate::kernel::BindingName::Generated(_) => None,
        }
    }
}

#[derive(Clone, Default)]
struct SourceBindingInfo {
    struct_name: Option<String>,
    aggregate: bool,
    array_shape: Option<Vec<u32>>,
}

/// The program facts a sidecar is parsed against: its struct and union
/// layouts, and by function, the objects a contract may name and the locals
/// that are memory-backed.
#[derive(Clone, Default)]
pub(in crate::surface) struct ProgramLayouts {
    pub(in crate::surface) local_bindings: std::sync::Arc<SourceBindingIndex>,
    pub(in crate::surface) string_literal_values:
        std::sync::Arc<BTreeMap<crate::kernel::StringLiteralId, ProgramValue>>,
    pub(in crate::surface) string_literal_owners:
        std::sync::Arc<BTreeMap<String, BTreeSet<Option<String>>>>,
    /// A C definition's execution name, indexed by translation unit and source spelling.
    pub(in crate::surface) qualified_functions: BTreeMap<(String, String), String>,
    pub(in crate::surface) program_object_names: BTreeMap<String, std::sync::Arc<BTreeSet<String>>>,
    /// Library-provided C values with stable identities in the selected profile.
    pub(in crate::surface) hosted_stdout: BTreeMap<String, ProgramValue>,
    /// The other members of each function's recursive C component, for the
    /// functions in a component of two or more. An expression `decreases`
    /// measure ranks calls to these functions too.
    pub(in crate::surface) recursion_peers: BTreeMap<String, Vec<String>>,
    pub(in crate::surface) struct_layouts:
        BTreeMap<String, crate::languages::interface::RecordLayout>,
    pub(in crate::surface) union_layouts: BTreeMap<String, syntax::CUnionLayout>,
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
    /// The `extern` contracts the C front end writes for functions it
    /// introduces, such as the fixed-arity function of each `snprintf`
    /// format, parsed after the sidecar's own declarations.
    pub(in crate::surface) frontend_contracts: String,
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
    /// the generic function, the instance's parameter and result types, and
    /// its parameters' names as a head writes them: it has the generic
    /// function's contract at those types.
    pub(in crate::surface) rust_generic_instances: Vec<GenericInstance>,
    /// The C++ declarations that share a path, as overloads do, by the
    /// importer name of that path: a head there selects one by signature.
    pub(in crate::surface) cpp_overloads: BTreeMap<String, Vec<CppOverload>>,
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
    pub(in crate::surface) c_typedefs: BTreeMap<String, syntax::CHeadTypedef>,
}

/// An instance of a generic function the import declares: its name, the
/// generic function's, its parameter and result types, its parameters'
/// names as a head writes them, and whether a method's receiver is `const`.
pub(in crate::surface) type GenericInstance = (
    String,
    String,
    Vec<InterfaceType>,
    InterfaceType,
    Vec<String>,
    bool,
);

/// One of the C++ declarations that share a path: its importer name,
/// whether a method's receiver is `const`, and its parameters' types after
/// the receiver. A head at the path names the one whose constness and
/// parameter types it writes.
#[derive(Clone, Debug)]
pub(in crate::surface) struct CppOverload {
    pub(in crate::surface) name: String,
    pub(in crate::surface) constant: bool,
    pub(in crate::surface) parameters: Vec<InterfaceType>,
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
    mut layouts: ProgramLayouts,
) -> Result<ClickFile, ClickError> {
    // Appending keeps every position in the sidecar unchanged.
    let contracts = std::mem::take(&mut layouts.frontend_contracts);
    if contracts.is_empty() {
        return Parser::with_program_layouts(source, layouts, None)?.parse_file();
    }
    Parser::with_program_layouts(&format!("{source}\n{contracts}"), layouts, None)?.parse_file()
}

/// Whether a Click source declares only definitions for importers:
/// imports, the `arithmetic` directive, specification types, predicates,
/// pure functions, and resources, with no `verifying` or `target` source, no `runtime`, no theorem, no
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
                        | "arithmetic"
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

/// Parses file items as a library module reads them, for tests that state a
/// library declaration: its arithmetic keeps its native reading, which is the
/// one its kernel axiom states.
#[cfg(test)]
pub(super) fn parse_library_file_items(source: &str) -> Result<ClickFile, ClickError> {
    let mut parser = Parser::with_program_layouts(
        source,
        ProgramLayouts::default(),
        Some(&crate::source::SourceContainer::new(
            "library/test.click",
            0,
        )),
    )
    .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
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
    imported_proposition_functions: &BTreeSet<String>,
    imported_pointer_functions: &BTreeSet<String>,
    imported_integer_parameters: &BTreeMap<String, Vec<usize>>,
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
    // An imported `-> Integer` result is an exact Integer operand, as a
    // local one is.
    parser
        .integer_function_names
        .extend(imported_integer_functions.iter().cloned());
    parser
        .proposition_function_names
        .extend(imported_proposition_functions.iter().cloned());
    // An imported pointer result has only a C meaning, as a local one has.
    parser
        .pointer_result_functions
        .extend(imported_pointer_functions.iter().cloned());
    parser.integer_parameter_positions.extend(
        imported_integer_parameters
            .iter()
            .map(|(name, positions)| (name.clone(), positions.clone())),
    );
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
        // A `let` value parameter is mapped by its own name, as the
        // importing file's callee would be.
        if !named_contract {
            let witnesses = &parameters[parameters.len() - block.witness_count()..];
            for name in witnesses {
                parser
                    .callee_resource_binders
                    .entry(block.signature().name().to_string())
                    .or_default()
                    .insert(name.clone(), Parser::value_parameter_callee_binder());
            }
        }
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
    matches!(name, "let" | "by" | "sorry")
        || removed_tactic_refusal(name).is_some()
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
/// as an explicit `have P by solve();`. Out of line to keep recursive frames small.
#[inline(never)]
fn have_proof_as_written_in_full(proof: SourceProof) -> SourceProof {
    if proof == SourceProof::Tactic(SmartTactic::Solve) {
        SourceProof::Script(vec![ProofTactic::Solve])
    } else {
        proof
    }
}

fn is_tactic_name(name: &str) -> bool {
    name == "solve"
}

/// The refusal of a removed tactic spelling, naming what replaced it.
fn removed_tactic_refusal(name: &str) -> Option<&'static str> {
    Some(match name {
        "assumption" => {
            "`assumption()` is now `known()`; use `known()` to close a goal from available facts"
        }
        "auto" => {
            "`auto()` is removed: a `by auto();` proof is the omitted proof, so delete it, and a written `auto();` is `solve();`"
        }
        "arithmetic" => {
            "`arithmetic()` is now `solve() using { ... }`, which closes the goal from only the listed premises; `arithmetic()` with no list is `solve() using {}`"
        }
        "execute_until" => "`execute_until` is now `step_until`",
        "execute" => {
            "`execute()` is removed: end the script and its implicit tail runs the C that is left and closes every goal, or step to function exit with `step_until(function.exit)` to work there"
        }
        _ => return None,
    })
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
    local_bindings: std::sync::Arc<SourceBindingIndex>,
    string_literal_values: std::sync::Arc<BTreeMap<crate::kernel::StringLiteralId, ProgramValue>>,
    string_literal_owners: std::sync::Arc<BTreeMap<String, BTreeSet<Option<String>>>>,
    /// The loop clause currently being read, including its phase proofs.
    /// Source-aware parsing can reject unbound values before proof execution.
    loop_name_context: Option<String>,
    /// Binders declared in quantified goals and range bodies. This set only
    /// recognizes their spelling; lowering and proof checking still enforce
    /// their availability at the point of use.
    loop_proof_value_names: crate::persistent::PersistentSet<String>,
    /// A predicate goal may introduce its declared quantifiers when unfolded.
    loop_predicate_bodies: BTreeMap<String, ClickProposition>,
    resource_parameters: BTreeMap<String, usize>,
    program_object_names_by_function: BTreeMap<String, std::sync::Arc<BTreeSet<String>>>,
    hosted_stdout_by_function: BTreeMap<String, ProgramValue>,
    hosted_stdout: Option<ProgramValue>,
    recursion_peers_by_function: BTreeMap<String, Vec<String>>,
    /// Click library modules the program's C declarations bring.
    implied_library_modules: BTreeSet<&'static str>,
    /// Whether this parser reads a Click library module, which never looks
    /// up the library's own declarations while the library is loading.
    library_module: bool,
    /// Whether this parser reads one of the Click library modules built into
    /// the verifier, by identity and text. Only these declare a primitive
    /// `type`, a bodyless `function` or an `axiom`: each is trusted, so a
    /// sidecar or a file that merely lives under `library/` cannot.
    library_primitives: bool,
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
    /// The element type of each slice parameter read so far, by name: the
    /// latest parameter of that name, which is the current declaration's.
    rust_slice_elements: BinderMap<InterfaceType>,
    /// The `Vec` parameters of the Rust signature being parsed, and
    /// `result` when it returns one: each reads `v.len()` and `v[i]`, through
    /// `*v` when the parameter is a reference (`true`).
    rust_vec_params: BTreeMap<String, bool>,
    /// The iterator each loop of the Rust function being parsed advances,
    /// by loop index: `loop(i).iter` names its state.
    rust_loop_iterators: Vec<Option<crate::languages::interface::RustLoopIterator>>,
    /// How many `loop` blocks enclose the text being parsed: inside one,
    /// `iter` is that loop's iterator.
    loop_block_depth: usize,
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
    rust_generic_instances: Vec<GenericInstance>,
    /// The C++ overloads by their shared path, as the layouts give them.
    cpp_overloads: BTreeMap<String, Vec<CppOverload>>,
    /// The index of each `fn` token of a generic function's instance the
    /// parser wrote out: only these may name an instance.
    rust_written_instances: BTreeSet<usize>,
    /// The methods of generic C++ class templates' instances, which the
    /// sidecar does not write, each with its generic method: each is
    /// written out from its generic method.
    cpp_generic_instances: BTreeMap<String, String>,
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
    c_typedefs: BTreeMap<String, syntax::CHeadTypedef>,
    match_nesting: usize,
    proposition_nesting: usize,
    proof_nesting: usize,
    contract_expression_nesting: usize,
    /// Interval certificates juxtapose a term and two parenthesized bounds.
    certificate_operand_boundary: bool,
    contract_if_nesting: usize,
    algebraic_type_nesting: usize,
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    /// Whether the unary expression being parsed is the operand of a prefix
    /// operator (cast migration only).
    /// Every braced proof block parsed so far, in parse order: the block's
    /// braces and the first token of each tactic it holds.
    proof_block_spans: Vec<ProofBlockSpan>,
    proof_clause_spans: Vec<ProofClauseSpan>,
    /// The owner the next proof clause records, taken as the clause starts.
    proof_clause_owner: Option<SourcePosition>,
    implicit_proof_spans: Vec<ImplicitProofSpan>,
    matching_parentheses: Vec<Option<usize>>,
    position: usize,
    struct_layouts: BTreeMap<String, crate::languages::interface::RecordLayout>,
    /// See [`ProgramLayouts::rust_enum_types`].
    rust_enum_types: BTreeMap<String, crate::kernel::TypeParameterName>,
    union_layouts: BTreeMap<String, syntax::CUnionLayout>,
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
    /// The C type of the current function's `result`, which keeps its C
    /// meaning in a comparison when it is a pointer or a float.
    current_result_interface_type: Option<InterfaceType>,
    /// The current function's locals of pointer type that no parameter
    /// shadows.
    current_local_pointers: BTreeSet<String>,
    /// The lexical names bound at the cursor that carry no further data:
    /// contract bindings, Integer parameters and lets, theorem parameters
    /// and proof binders (see [`NameKind`]).
    names: NameTable,
    /// The pure functions of this module that take a slice, indexed with
    /// their names: each one's written parameter count and the positions of
    /// its `name: &[T]` parameters. A call passes such a parameter a slice,
    /// which stands for its pointer and its length.
    pure_function_slices: BTreeMap<String, (usize, Vec<usize>)>,
    /// The pure functions whose result is a slice, `-> &[T]`: a call's
    /// `.len()`, `.as_ptr()` and `[i]` read the slice value.
    slice_result_functions: BTreeSet<String>,
    /// Pure functions declared `-> Integer`, whose calls are Integer
    /// operands.
    integer_function_names: BTreeSet<String>,
    proposition_function_names: BTreeSet<String>,
    /// The pure functions whose declared result is a pointer: a call of one
    /// is a pointer operand, so arithmetic on it is pointer arithmetic and
    /// a comparison of it keeps its C meaning.
    pointer_result_functions: BTreeSet<String>,
    /// The positions of the `Integer` parameters of each pure function and
    /// theorem this module declares or imports, where an argument's
    /// arithmetic is exact.
    integer_parameter_positions: BTreeMap<String, Vec<usize>>,
    /// What each `let` in scope is as an arithmetic operand, so a later
    /// binding's arithmetic on it has a meaning.
    let_operands: spec_arithmetic::LetOperands,
    /// The machine types of the current theorem's or pure function's
    /// parameters, which a diagnostic names.
    spec_parameter_types: BinderMap<InterfaceType>,
    /// The casts written as `address(p)`, which convert a C pointer to its
    /// `uint64` address. Arithmetic on them is
    /// pointer-word arithmetic, such as a tag added to an aligned address,
    /// and keeps its C meaning as a pointer operand does.
    address_casts: std::collections::HashSet<ProgramExpression>,
    /// The pointer parameters of the theorem being parsed. Arithmetic on one
    /// is pointer arithmetic and keeps its C meaning, as it does on a C
    /// function's pointer parameter.
    theorem_pointer_params: BTreeSet<String>,
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
    /// comparisons: in every file, except inside a native rule result such
    /// as `unsigned_sum_bound`'s.
    integer_arithmetic: bool,
    /// Quantifier variables open at the cursor, innermost last. Each hides
    /// a fact of the same name inside its body.
    quantifier_binders: Vec<SurfaceBinder>,
    integer_literal_context: bool,
    /// Instance binders declared by each C function block already parsed,
    /// keyed by function name. A call step reads exactly the entry for its
    /// callee, so binding a call site costs one lookup per written entry.
    ///
    /// This is an index over the clauses, not a second source for a binder's
    /// spelling: every entry is copied from the `ResourceClause::Named`
    /// binding the clause already carries, which is also the name lowering
    /// copies into `ResourceSpec::Instance::binder`. The parser cannot read
    /// that kernel field instead, because it resolves a call map while
    /// parsing, before any clause is lowered; and it needs each binder's
    /// identity, resource family, and `owns`/`produces` kind keyed by callee,
    /// which no lowered spec offers.
    callee_resource_binders: BTreeMap<String, BTreeMap<String, CalleeResourceBinder>>,
    contract_resource_binders: BTreeMap<String, BTreeMap<String, CalleeResourceBinder>>,
    /// Set while a `contract` block's embedded function block is parsed: its
    /// signature names an interface, not a callable C function.
    in_contract_definition: bool,
    /// Set while a function contract's `owns`, `consumes`, or `produces`
    /// clause is parsed: the only places `uninitialized(p[a..b])` is accepted.
    uninitialized_memory_allowed: bool,
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
/// block, recorded so a caller's call step can bind it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct CalleeResourceBinder {
    pub(in crate::surface) identity: Variable,
    // None denotes a supplied resource assertion parameter. Its concrete
    // family is checked by the instantiated runtime contract in the kernel.
    pub(in crate::surface) family: Option<String>,
    /// The named resource clause as written by the callee. A call output needs
    /// this richer target, not just the family used for binder transport, so
    /// later `unfold(name)` can recover the resource body and its arguments.
    pub(in crate::surface) resource: Option<ResourceClause>,
    /// C parameter names in declaration order, used to instantiate the
    /// resource arguments with the call's actual expressions.
    pub(in crate::surface) parameter_names: Vec<String>,
    pub(in crate::surface) kind: CalleeResourceBinderKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface) enum CalleeResourceBinderKind {
    /// `owns` and `consumes`: the caller supplies the instance through the map.
    Supplied,
    /// `produces`: the caller introduces the instance with `let`.
    Produced,
    /// A runtime binder that names a resource type, not an instance:
    /// `atomic_init`'s `payload`.
    Type,
    /// A `let` value parameter, `let n: uint64;`: the caller may give its
    /// value, or leave it to the instance its clause selects.
    Value,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    interface_type: InterfaceType,
    struct_name: Option<String>,
    struct_pointer: bool,
    constant: bool,
    pointee_constant: bool,
    /// Written `T&`: `interface_type` is the pointer that carries the reference.
    reference: bool,
}

/// A recognized `(struct name *)` cast target in a contract expression.
struct StructPointerCast {
    struct_name: String,
    pointee_constant: bool,
    /// Tokens the prefix occupies, from `(` through `)`.
    tokens: usize,
}

impl StructPointerCast {
    /// The target as Click writes it inside the parentheses of `as (...)`.
    fn spelling(&self) -> String {
        let constant = if self.pointee_constant { "const " } else { "" };
        format!("{constant}struct {} *", self.struct_name)
    }
}

/// The module that specifies Rust slices, brought in where a sidecar
/// declares a slice.
pub(super) const SLICE_MODULE: &str = "library/rust/slice.click";

/// Whether `name` is the library's `slice::from_raw_parts`, a slice made of
/// a pointer and a length.
fn is_slice_from_raw_parts(name: &str) -> bool {
    matches!(
        name,
        "slice::from_raw_parts" | "click::rust::slice::from_raw_parts"
    )
}

pub(super) fn is_c_type_keyword(name: &str) -> bool {
    matches!(
        name,
        "void"
            | "_Bool"
            | "bool"
            | "Bool"
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

pub(in crate::surface) fn algebraic_field_c_type_supported(interface_type: InterfaceType) -> bool {
    !matches!(
        interface_type,
        InterfaceType::Void
            | InterfaceType::FunctionPointer(_)
            | InterfaceType::Int8Array(_)
            | InterfaceType::Int16Array(_)
            | InterfaceType::Int32Array(_)
            | InterfaceType::CharArray(_, _)
            | InterfaceType::UInt8Array(_)
            | InterfaceType::UInt16Array(_)
            | InterfaceType::UInt32Array(_)
            | InterfaceType::Int128Array(_)
            | InterfaceType::Int64Array(_, _)
            | InterfaceType::UInt128Array(_)
            | InterfaceType::UInt64Array(_, _)
            | InterfaceType::Float32Array(_)
            | InterfaceType::Float64Array(_)
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

impl ProgramLayouts {
    pub(in crate::surface) fn register_local_bindings(
        &mut self,
        function: &crate::languages::interface::ImportedFunction,
    ) {
        self.register_function_static_bindings(function);
        let index = std::sync::Arc::make_mut(&mut self.local_bindings);
        // Declarations normally share one owner. Retain the typed owner so a
        // long function/source spelling is copied once, not per temporary.
        let mut last_owner = None;
        let mut record = |binding: &crate::kernel::BindingName,
                          site: Option<&syntax::CSite>,
                          materialized: bool| {
            let Some(id) = binding.local_id() else {
                return;
            };
            if last_owner.as_ref() != Some(id.owner()) {
                index
                    .owners
                    .entry(id.function().to_owned())
                    .or_default()
                    .insert(id.source().map(str::to_owned));
                last_owner = Some(id.owner().clone());
            }
            let parameter = id
                .is_parameter()
                .then(|| function.parameters().get(id.ordinal() as usize))
                .flatten();
            let struct_name = id.struct_name().map(str::to_owned).or_else(|| {
                function
                    .local_struct_pointers()
                    .get(binding)
                    .or_else(|| function.local_struct_values().get(binding))
                    .cloned()
                    .or_else(|| parameter.and_then(|p| p.struct_name().map(str::to_owned)))
            });
            let aggregate = materialized
                || id
                    .program_type()
                    .is_some_and(|ty| ty.array_element_type().is_some())
                || function.local_struct_values().contains_key(binding)
                || parameter.is_some_and(|p| p.is_struct_value());
            let array_shape = id.array_shape().map(<[u32]>::to_vec);
            if !aggregate
                && id.program_type().is_some_and(ProgramType::is_pointer)
                && let Some(layout) = struct_name
                    .as_ref()
                    .and_then(|name| function.structs().get(name))
            {
                index
                    .field_places
                    .entry(function.name().to_owned())
                    .or_default()
                    .insert(
                        binding.clone(),
                        super::scalar_field_places(layout, function.structs()),
                    );
            }
            index.declarations.insert(
                id.clone(),
                SourceBindingInfo {
                    struct_name,
                    aggregate,
                    array_shape,
                },
            );
            if let Some(path) = site
                .and_then(syntax::CSite::get)
                .and_then(|site| site.source_path())
                && let Some(name) = id.spelling()
            {
                index.sites.insert(
                    (
                        id.source().map(str::to_owned),
                        id.function().to_owned(),
                        path.to_vec(),
                        name.to_owned(),
                    ),
                    id.clone(),
                );
            }
        };
        for parameter in function.parameters() {
            record(parameter.binding_name(), None, false);
        }
        let mut statements = vec![function.body()];
        let mut expressions = Vec::new();
        while !statements.is_empty() || !expressions.is_empty() {
            while let Some(statement) = statements.pop() {
                match statement {
                    syntax::CStatement::Declare { name, .. }
                    | syntax::CStatement::DeclareStructValue { name, .. } => {
                        record(name.binding(), statement.site(), false)
                    }
                    _ => {}
                }
                crate::languages::c::address_taken::child_statements(
                    statement,
                    &mut expressions,
                    &mut statements,
                );
            }
            while let Some(expression) = expressions.pop() {
                crate::languages::c::address_taken::child_expressions(
                    expression,
                    &mut expressions,
                    &mut statements,
                );
            }
        }
        if let Some(lowered) = function.prelowered_kernel_function() {
            use crate::kernel::ProgramStatement;
            let mut pending = vec![lowered.body()];
            while let Some(statement) = pending.pop() {
                crate::instrumentation::record_deterministic_work(1);
                match statement {
                    ProgramStatement::Declare { name, .. } => record(name.binding(), None, false),
                    ProgramStatement::DeclareAggregate { name, .. } => {
                        record(name.binding(), None, true)
                    }
                    ProgramStatement::TryCatchInt32 {
                        try_body,
                        binding,
                        handler,
                        ..
                    } => {
                        record(binding, None, false);
                        pending.extend([try_body.as_ref(), handler.as_ref()]);
                    }
                    ProgramStatement::UnwindCleanup { body, cleanup } => {
                        pending.extend([body.as_ref(), cleanup.as_ref()]);
                    }
                    ProgramStatement::Seq(sequence) => {
                        pending.extend(sequence.iter().map(|s| s.as_ref()))
                    }
                    ProgramStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => pending.extend([then_branch.as_ref(), else_branch.as_ref()]),
                    ProgramStatement::Loop {
                        body, update, test, ..
                    } => pending.extend(crate::kernel::program_loop_regions(
                        body,
                        update.as_deref(),
                        Some(test),
                    )),
                    ProgramStatement::Switch { cases, .. } => {
                        pending.extend(cases.iter().map(|case| case.body.as_ref()))
                    }
                    _ => {}
                }
            }
        }
        // A lowering that places declarations at source statements, as
        // Rust's does a repeated name's, names each by its statement.
        if let Some(sites) = function.source_sites() {
            for (binding, site) in &sites.declarations {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(id) = binding.local_id()
                    && let Some(name) = id.spelling()
                    && let Some(path) = sites.paths.get(*site as usize)
                {
                    index.sites.insert(
                        (
                            id.source().map(str::to_owned),
                            id.function().to_owned(),
                            path.clone(),
                            name.to_owned(),
                        ),
                        id.clone(),
                    );
                }
            }
        }
    }

    pub(in crate::surface) fn register_string_literals(
        &mut self,
        function: &crate::languages::interface::ImportedFunction,
    ) {
        for literal in function.string_literals() {
            let literal = literal.to_kernel();
            let id = literal.identity().clone();
            std::sync::Arc::make_mut(&mut self.string_literal_owners)
                .entry(id.function().to_owned())
                .or_default()
                .insert(id.source().map(str::to_owned));
            let pointer =
                crate::kernel::SymbolicMemory::string_literal_pointer(&id, literal.bytes());
            std::sync::Arc::make_mut(&mut self.string_literal_values).insert(
                id,
                ProgramValue::typed_pointer(
                    pointer,
                    literal
                        .element_type()
                        .pointer_to()
                        .expect("character pointer"),
                ),
            );
        }
    }
}

/// Give a concrete replacement for scalar and slice signatures. Record and
/// method contracts need an `impl` and the imported type identity instead.
impl Parser {
    fn verifies_rust(&self) -> bool {
        self.language == SourceLanguage::Rust
    }
}

/// The machine types of a theorem's or pure function's parameters.
fn spec_parameter_types(parameters: &[FunctionParameter]) -> BinderMap<InterfaceType> {
    parameters
        .iter()
        .filter_map(|parameter| match parameter.click_type() {
            ClickType::Program(interface_type) => {
                Some((parameter.name().to_string(), *interface_type))
            }
            _ => None,
        })
        .collect()
}

fn algebraic_parameter_types(
    parameters: &[FunctionParameter],
) -> BTreeMap<String, (AlgebraicTypeApplication, usize)> {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| match parameter.click_type() {
            ClickType::Resource => None,
            ClickType::Algebraic(application) => {
                Some((parameter.name().to_string(), (application.clone(), index)))
            }
            ClickType::Parameter(_)
            | ClickType::Program(_)
            | ClickType::CObjectPointer { .. }
            | ClickType::Proposition
            | ClickType::Function { .. }
            | ClickType::Integer => None,
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedField {
    interface_type: InterfaceType,
    pointee_constant: bool,
    struct_name: Option<String>,
    union_name: Option<String>,
    function_pointer_signature: Option<crate::languages::interface::CallbackInterface>,
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
        struct_layouts: BTreeMap<String, crate::languages::interface::RecordLayout>,
        union_layouts: BTreeMap<String, syntax::CUnionLayout>,
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
            &layouts.record_spellings,
        )
        .map_err(|error| error.with_kind(ClickErrorKind::Syntax))?;
        parser.local_bindings = layouts.local_bindings;
        parser.string_literal_values = layouts.string_literal_values;
        parser.string_literal_owners = layouts.string_literal_owners;
        parser.program_object_names_by_function = layouts.program_object_names;
        parser.hosted_stdout_by_function = layouts.hosted_stdout;
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
        parser.cpp_overloads = layouts.cpp_overloads;
        // A generic function's instances are written out at their types.
        let mut function_instances = BTreeMap::<String, rust_generic_functions::Instances>::new();
        let mut impl_instances = BTreeMap::<String, BTreeSet<Vec<String>>>::new();
        for (instance, generic, _, _, parameters, _) in &parser.rust_generic_instances {
            if let Some(arguments) =
                crate::languages::rust::names::instance_type_arguments(instance, generic)
            {
                function_instances
                    .entry(generic.clone())
                    .or_default()
                    .insert(arguments, parameters.clone());
            } else if let Some((record, arguments)) =
                crate::languages::rust::names::impl_instance_arguments(instance, generic)
            {
                impl_instances.entry(record).or_default().insert(arguments);
            } else if let (Some(instance), Some(generic)) = (
                instance.strip_suffix("_drop_glue"),
                generic.strip_suffix("_drop_glue"),
            ) {
                // A generic struct's drop glue at an instance, `Node<u32>`'s
                // of `Node<T>`'s, is written from its `impl<T> Destruct`
                // block.
                let (record, arguments) =
                    crate::languages::rust::names::split_type_arguments(instance);
                if crate::languages::rust::names::split_type_arguments(generic).0 == record
                    && !arguments.is_empty()
                {
                    impl_instances
                        .entry(rust_generic_functions::destruct_instances_key(&record))
                        .or_default()
                        .insert(arguments);
                }
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
            // A reference parameter's type grants the authority a safe
            // caller holds over its referent.
            let (tokens, positions) = rust_reference_authority::derive_reference_authority(
                tokens,
                positions,
                &parser.struct_layouts,
                &parser.rust_enum_types,
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
                let (tokens, positions, methods) = cpp_class_objects::rewrite_class_objects(
                    tokens,
                    positions,
                    &layouts.record_spellings,
                )?;
                parser.matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
                parser.tokens = tokens;
                parser.positions = positions;
                parser.cpp_object_methods = methods;
            }
            parser.language = SourceLanguage::Cpp;
            // A generic class template's method is written out at each of
            // its instances the import declares, by the generic's path and
            // the instance's constness: an overload is named by neither.
            let paths = parser
                .cpp_overloads
                .iter()
                .flat_map(|(path, overloads)| {
                    overloads
                        .iter()
                        .map(move |overload| (overload.name.as_str(), path.as_str()))
                })
                .collect::<BTreeMap<_, _>>();
            let mut method_instances = BTreeMap::<String, cpp_generic_templates::Instances>::new();
            for (instance, generic, _, _, parameters, constant) in &parser.rust_generic_instances {
                let path = paths.get(instance.as_str()).copied().unwrap_or(instance);
                let arguments =
                    cpp_generic_templates::instance_arguments(path).ok_or_else(|| {
                        ClickError::new(format!(
                            "the C++ generic instance `{instance}` names no class template instance"
                        ))
                    })?;
                // The receiver is implicit in a head.
                let parameters = match parameters.split_first() {
                    Some((receiver, rest)) if receiver == "this" => rest,
                    _ => parameters,
                };
                let generic_path = paths.get(generic.as_str()).copied().unwrap_or(generic);
                method_instances
                    .entry(generic_path.to_string())
                    .or_default()
                    .insert((*constant, arguments), parameters.to_vec());
                parser
                    .cpp_generic_instances
                    .insert(instance.clone(), generic.clone());
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
        struct_layouts: BTreeMap<String, crate::languages::interface::RecordLayout>,
        union_layouts: BTreeMap<String, syntax::CUnionLayout>,
        aggregate_objects_by_function: BTreeMap<String, BTreeMap<String, String>>,
        aggregate_array_objects_by_function: BTreeMap<String, BTreeSet<String>>,
        global_array_shapes_by_function: BTreeMap<String, BTreeMap<String, GlobalArrayShape>>,
        container: Option<&crate::source::SourceContainer>,
        rust_trait_instances: &BTreeMap<String, BTreeSet<Vec<String>>>,
        record_spellings: &BTreeMap<String, String>,
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
        let library_primitives = container.is_some_and(|container| {
            super::CLICK_LIBRARY_MODULES
                .iter()
                .any(|(identity, text)| *identity == &*container.filename && *text == source)
        });
        // Specification arithmetic is over Integer in every file, library
        // modules included. A library statement that means the C operation
        // observes it exactly, as `to_integer(value + 1) <= to_integer(upper)`.
        let integer_arithmetic = true;
        // Source clauses may follow declarations. Choose the spelling for the
        // whole file so moving the clause cannot bypass a Rust syntax check.
        let language =
            SourceLanguage::of_sources(tokens.windows(2).filter_map(|pair| match pair {
                [Token::Ident(keyword), Token::String(path)] if keyword == "verifying" => {
                    Some(path.as_str())
                }
                _ => None,
            }));
        // Reserve written binder identities before desugaring allocates any names.
        for window in tokens.windows(4) {
            if let [Token::Ident(name), Token::LParen, number, Token::RParen] = window
                && name == "binder"
            {
                let number = match number {
                    Token::Number(n) => Some(u64::from(*n)),
                    Token::UnsuffixedUInt64(n) | Token::UInt64Number(n) => Some(*n),
                    Token::UnsuffixedInt64(n) | Token::Int64Number(n) => u64::try_from(*n).ok(),
                    Token::RustInteger(n) => n.digits.parse::<u64>().ok(),
                    _ => None,
                };
                if let Some(number) = number {
                    crate::kernel::GeneratedBinderId::from_spelling(number);
                }
            }
        }
        let mut tokens = tokens;
        if language == SourceLanguage::Rust {
            rust_literals::normalize_tokens(&mut tokens);
        } else if let Some(index) = tokens.iter().enumerate().find_map(|(index, token)| {
            (matches!(token, Token::RustInteger(_)) && !float_bits::literal_token(&tokens, index))
                .then_some(index)
        }) {
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
            rust_trait_objects::rewrite_trait_objects(tokens, positions, rust_trait_instances)?
        } else {
            (tokens, positions, BTreeSet::new())
        };
        // So is a C++ sidecar's class object state.
        let (tokens, positions, cpp_object_methods) = if language == SourceLanguage::Cpp {
            let (tokens, positions) = cpp_syntax::rewrite_function_references(tokens, positions);
            cpp_class_objects::rewrite_class_objects(tokens, positions, record_spellings)?
        } else {
            (
                tokens,
                positions,
                cpp_class_objects::ObjectMethods::default(),
            )
        };
        let matching_parentheses = validate_parenthesis_nesting(&tokens, &positions)?;
        Ok(Self {
            local_bindings: Default::default(),
            string_literal_values: Default::default(),
            string_literal_owners: Default::default(),
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
            rust_slice_elements: BinderMap::new(),
            rust_vec_params: BTreeMap::new(),
            rust_loop_iterators: Vec::new(),
            loop_block_depth: 0,
            rust_impl_type: None,
            rust_impl_method_suffix: None,
            rust_impl_module: None,
            rust_impl_trait: None,
            rust_trait_interface: None,
            rust_trait_type_parameters: BTreeSet::new(),
            rust_abstract_type_parameters: BTreeSet::new(),
            rust_generic_instances: Vec::new(),
            cpp_overloads: BTreeMap::new(),
            rust_written_instances: BTreeSet::new(),
            cpp_generic_instances: BTreeMap::new(),
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
            certificate_operand_boundary: false,
            contract_if_nesting: 0,
            algebraic_type_nesting: 0,
            position: 0,
            struct_layouts,
            rust_enum_types: BTreeMap::new(),
            union_layouts,
            loop_name_context: None,
            loop_proof_value_names: Default::default(),
            loop_predicate_bodies: BTreeMap::new(),
            program_object_names_by_function: BTreeMap::new(),
            hosted_stdout_by_function: BTreeMap::new(),
            hosted_stdout: None,
            recursion_peers_by_function: BTreeMap::new(),
            implied_library_modules: path_library_modules,
            library_module,
            library_primitives,
            symbols,
            aggregate_objects_by_function,
            aggregate_array_objects_by_function,
            global_array_shapes_by_function,
            local_struct_pointers_by_function: BTreeMap::new(),
            current_reference_result: false,
            current_result_interface_type: None,
            current_local_pointers: BTreeSet::new(),
            names: NameTable::default(),
            pure_function_slices: BTreeMap::new(),
            slice_result_functions: BTreeSet::new(),
            integer_function_names: BTreeSet::new(),
            proposition_function_names: BTreeSet::new(),
            pointer_result_functions: BTreeSet::new(),
            integer_parameter_positions: BTreeMap::new(),
            let_operands: Default::default(),
            spec_parameter_types: BinderMap::new(),
            address_casts: std::collections::HashSet::new(),
            theorem_pointer_params: BTreeSet::new(),
            pending_slice_params: None,
            bool_value_context: false,
            algebraic_variant_fields: BTreeMap::new(),
            integer_arithmetic,
            quantifier_binders: Vec::new(),
            callee_resource_binders: BTreeMap::new(),
            contract_resource_binders: BTreeMap::new(),
            in_contract_definition: false,
            uninitialized_memory_allowed: false,
            contract_value_parameters: Vec::new(),
            closure_captures: BTreeMap::new(),
            contract_value_parameter_names: BTreeMap::new(),
            in_function_block: false,
            resource_parameters: BTreeMap::new(),
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
                    if self.declares_named_result(parameters, "Prop") {
                        self.proposition_function_names.insert(name.clone());
                    }
                    if self.declares_slice_result(parameters) {
                        self.slice_result_functions.insert(name.clone());
                    }
                    if names::declares_pointer_result(&self.tokens, parameters) {
                        self.pointer_result_functions.insert(name.clone());
                    }
                    if let Some(positions) =
                        spec_arithmetic::written_integer_parameters(&self.tokens, parameters)
                    {
                        self.integer_parameter_positions
                            .insert(name.clone(), positions);
                    }
                    if let Some(slices) = self.written_slice_parameters(parameters) {
                        crate::surface::diagnostics::record_pure_function_slices(&name, &slices.1);
                        self.pure_function_slices.insert(name, slices);
                    }
                }
                names::DeclarationKind::Theorem => {
                    if let Some(positions) = spec_arithmetic::written_integer_parameters(
                        &self.tokens,
                        declaration.at + 1,
                    ) {
                        self.integer_parameter_positions
                            .insert(declaration.name, positions);
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

    /// The slice parameter `expression` reads at another point:
    /// `old(bytes)` or `at(point, bytes)`.
    fn read_slice_parameter<'a>(&self, expression: &'a ContractExpression) -> Option<&'a str> {
        let (ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        }) = expression
        else {
            return None;
        };
        match inner.as_ref() {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(slice),
            )) if self.rust_slice_params.contains(slice) => Some(slice),
            _ => None,
        }
    }

    /// The arguments of a call to a pure function that takes a slice, with
    /// each slice argument written as the pointer and the length it stands
    /// for. A slice argument is one value: a slice parameter in scope, such
    /// as `bytes`, or `slice::from_raw_parts(p, n)` for a pointer and a
    /// length.
    fn spread_slice_arguments(
        &self,
        name: &str,
        arguments: Vec<ContractExpression>,
    ) -> Result<Vec<ContractExpression>, ClickError> {
        let Some((count, slices)) = self.pure_function_slices.get(name) else {
            return Ok(arguments);
        };
        if arguments.len() != *count {
            return Err(self.error(format!(
                "`{name}` takes {count} argument{}, and each slice is one argument; pass a pointer and a length as `slice::from_raw_parts(p, n)`",
                if *count == 1 { "" } else { "s" }
            )));
        }
        let mut spread = Vec::with_capacity(count + slices.len());
        for (index, argument) in arguments.into_iter().enumerate() {
            if !slices.contains(&index) {
                spread.push(argument);
                continue;
            }
            match argument {
                ContractExpression::Call {
                    name: constructor,
                    arguments: parts,
                } if is_slice_from_raw_parts(&constructor) && parts.len() == 2 => {
                    spread.extend(parts);
                }
                // A subslice, `bytes[a..b]`, is its pointer and its length.
                ContractExpression::AlgebraicConstructor {
                    algebraic_type,
                    variant,
                    arguments: parts,
                } if algebraic_type.name() == "Slice" && variant == "Slice" && parts.len() == 2 => {
                    spread.extend(parts);
                }
                // A slice read at another point, as a printed proof writes
                // it: its pointer at that point, and its length, which a
                // shared slice parameter never changes.
                argument @ (ContractExpression::Old(_) | ContractExpression::At { .. })
                    if self.read_slice_parameter(&argument).is_some() =>
                {
                    let slice = self
                        .read_slice_parameter(&argument)
                        .expect("matched above")
                        .to_string();
                    spread.push(argument);
                    spread.push(ContractExpression::ProgramExpression(
                        ProgramExpression::Variable(format!("{slice}_len").into()),
                    ));
                }
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::BindingName::Named(slice),
                )) if self.rust_slice_params.contains(&slice) => {
                    let length = ContractExpression::ProgramExpression(
                        ProgramExpression::Variable(format!("{slice}_len").into()),
                    );
                    spread.push(ContractExpression::ProgramExpression(
                        ProgramExpression::Variable(slice.into()),
                    ));
                    spread.push(length);
                }
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::BindingName::Named(slice),
                )) => {
                    return Err(self.error(format!(
                        "argument {} of `{name}` is a slice, but `{slice}` is not a slice parameter; pass one, or `slice::from_raw_parts(p, n)` for a pointer and a length",
                        index + 1
                    )));
                }
                // A slice value passes its pointer and its length, its
                // methods `as_ptr()` and `len()`, resolved by its type.
                argument
                    if self.is_rust_slice_value(&argument)
                        || self.is_click_valued_receiver(&argument) =>
                {
                    let method = |method: &str| ContractExpression::MethodCall {
                        receiver: Box::new(argument.clone()),
                        method: method.to_string(),
                        arguments: vec![],
                    };
                    spread.push(method("as_ptr"));
                    spread.push(method("len"));
                }
                _ => {
                    return Err(self.error(format!(
                        "argument {} of `{name}` is a slice; pass a slice parameter, such as `bytes`, or `slice::from_raw_parts(p, n)` for a pointer and a length",
                        index + 1
                    )));
                }
            }
        }
        Ok(spread)
    }

    fn parse_file_items(&mut self) -> Result<ClickFile, ClickError> {
        self.index_algebraic_variant_fields();
        let mut imports = Vec::new();
        let mut verifying_sources = Vec::new();
        let mut c_target_name = None;
        let mut c_mode = None;
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
        let mut termination_proof = None;
        let mut termination_span = None;
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
            } else if self.peek_ident() == Some("termination") {
                let start = self.positions[self.position].clone();
                self.position += 1;
                if termination_proof.is_some() {
                    return Err(self.error("only one `termination by` block is allowed"));
                }
                self.expect_ident_spelling("by")?;
                termination_proof = Some(self.parse_possibly_empty_tactic_block()?);
                termination_span = Some((start, self.positions[self.position - 1].clone()));
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
                // The migration directive for Integer-default arithmetic,
                // which is now the only reading.
                return Err(self.error(
                    "specification arithmetic is over `Integer` by default; remove the `arithmetic` directive",
                ));
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
            } else if self.peek_ident() == Some("type")
                && matches!(self.peek_next(), Some(Token::Ident(_)))
            {
                algebraic_type_definitions.push(self.parse_primitive_type_definition()?);
            } else if self.peek_ident() == Some("predicate") {
                predicate_definitions.push(self.parse_predicate_definition()?);
            } else if self.peek_ident() == Some("function") {
                click_function_definitions.push(self.parse_click_function_definition()?);
            } else if self.peek_ident() == Some("theorem")
                || (self.peek_ident() == Some("axiom")
                    && matches!(self.peek_next(), Some(Token::Ident(_))))
            {
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
            } else if self.verifies_cpp()
                && self.peek_ident() == Some("template")
                && self.cpp_template_contract_follows()
            {
                contract_definitions.push(self.parse_cpp_template_contract()?);
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
        for (instance, generic, parameter_types, return_type, _, _) in
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
        let mut program_function_names = self
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
                    program_function_names.insert(signature.name().to_string(), target.clone());
                }
            }
        }
        // A declaration can imply a library module as it is read: a slice
        // type in a Rust sidecar brings in the module that defines `Slice`.
        for identity in &self.implied_library_modules {
            let identity = (*identity).to_string();
            if !library_imports.contains(&identity) {
                library_imports.push(identity);
            }
        }
        let c_target = self.resolve_c_target(c_target_name, c_mode)?;
        let file = ClickFile {
            struct_sizes: std::sync::Arc::new(
                self.struct_layouts
                    .iter()
                    .map(|(name, layout)| (name.clone(), layout.size_bytes()))
                    .collect(),
            ),
            program_function_names: std::sync::Arc::new(program_function_names),
            imports,
            library_imports,
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
            tactic_definitions,
            termination_proof,
            termination_span,
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
        let (name, type_parameters) = self.parse_algebraic_type_head()?;
        if super::LIBRARY_PRIMITIVE_TYPES.contains(&name.as_str()) {
            return Err(self.error(format!(
                "`{name}` is a Click library primitive type; a `spec enum` cannot redeclare it"
            )));
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
            primitive: false,
        })
    }

    /// `type Vec<T>;` in a Click library module: a primitive type with no
    /// definition, like `uint32`. Its meaning is the library's bodyless
    /// functions over it and the axioms that relate them.
    fn parse_primitive_type_definition(&mut self) -> Result<AlgebraicTypeDefinition, ClickError> {
        if !self.library_primitives {
            return Err(self.error(
                "a primitive `type` declaration is reserved for the Click library; declare a `spec enum` instead",
            ));
        }
        self.expect_ident_spelling("type")?;
        let (name, type_parameters) = self.parse_algebraic_type_head()?;
        if !super::LIBRARY_PRIMITIVE_TYPES.contains(&name.as_str()) {
            return Err(self.error(format!(
                "`{name}` is not a Click library primitive type; list it in `LIBRARY_PRIMITIVE_TYPES`"
            )));
        }
        self.expect(Token::Semicolon)?;
        Ok(AlgebraicTypeDefinition {
            name,
            type_parameters,
            variants: Vec::new(),
            primitive: true,
        })
    }

    fn parse_algebraic_type_head(&mut self) -> Result<(String, Vec<String>), ClickError> {
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
        Ok((name, type_parameters))
    }

    fn parse_algebraic_field_type(
        &mut self,
        type_parameters: &[String],
    ) -> Result<AlgebraicFieldType, ClickError> {
        if let Some(element) = self.take_rust_slice_value_type()? {
            return Ok(AlgebraicFieldType::Algebraic {
                name: "Slice".to_string(),
                arguments: vec![AlgebraicFieldType::C {
                    interface_type: element,
                    struct_name: None,
                    object_class: None,
                }],
            });
        }
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
            if self.peek() == Some(&Token::Star) {
                self.position += 1;
                return Ok(AlgebraicFieldType::ParameterPointer(name));
            }
            return Ok(AlgebraicFieldType::Parameter(name));
        }
        if rust_type.is_some() || is_c_type_keyword(&name) {
            let parsed = match rust_type {
                Some(parsed) => parsed,
                None => self.parse_type()?,
            };
            if !algebraic_field_c_type_supported(parsed.interface_type) {
                return Err(self.error(
                    "algebraic datatype fields must be C scalar, data-pointer, or algebraic values",
                ));
            }
            // Only a declared `struct tag*` records a tag: a bare
            // `struct tag` is not a pointer to a laid-out object and a
            // `struct tag**` does not point at one either, so neither is a
            // memory base in a match arm.
            let object_class = self.declared_object_class(&parsed);
            let struct_name =
                if parsed.struct_pointer && parsed.interface_type == InterfaceType::Int32Pointer {
                    parsed.struct_name
                } else {
                    None
                };
            return Ok(AlgebraicFieldType::C {
                interface_type: parsed.interface_type,
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
            self.refuse_cast_type_binder(&alias)?;
            if alias == "program" {
                return Err(self.error(
                    "`program` names the verified program's bindings (`program::name`) and cannot be a source alias",
                ));
            }
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

    fn is_qualified_program_name(&self) -> bool {
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

    fn parse_qualified_program_name(&mut self) -> Result<(String, ProgramExpression), ClickError> {
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
            None => ProgramExpression::Variable((qualified.clone()).into()),
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

    fn parse_segment_primary(
        &mut self,
    ) -> Result<(ContractExpression, ProgramExpression), ClickError> {
        if let Some(expression) = self.take_local_binding_reference()? {
            let lowered = contract_expression_as_program_expression(&expression)
                .ok_or_else(|| self.error("a C declaration reference must denote a C place"))?;
            return Ok((expression, lowered));
        }
        if self.peek_next() == Some(&Token::ColonColon) {
            let (name, expression) = self.parse_qualified_program_name()?;
            return Ok((
                ContractExpression::ProgramExpression(ProgramExpression::Variable((name).into())),
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
        Ok((ContractExpression::ProgramExpression(expression), lowered))
    }

    /// Wraps a bare global-array name in a cast to its element pointer type.
    /// A parameter shadowing the global is not in the per-function shape map,
    /// so it keeps the parameter's own type.
    fn retype_global_array_pointer(&self, expression: &ProgramExpression) -> ProgramExpression {
        let ProgramExpression::Variable(crate::kernel::BindingName::Named(name)) = expression
        else {
            return expression.clone();
        };
        match self
            .names
            .global_array_shapes
            .get(name)
            .and_then(|array| array.element_type.pointer_to())
        {
            Some(target_type) => ProgramExpression::Cast {
                expression: Box::new(expression.clone()),
                target_type,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
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
        self.loop_predicate_bodies
            .insert(name.clone(), body.clone());
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
        let parsed_parameters = self
            .parse_parameters_with_resources_and_functions(false, true)
            .map(|(parameters, _)| parameters);
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
        if matches!(return_type, ClickType::Function { .. }) {
            return Err(
                self.error("specification function declaration results are not supported yet")
            );
        }

        let return_object_class = parsed_c_return_type
            .as_ref()
            .and_then(|parsed| self.declared_object_class(parsed));
        if let Some(parsed_return_type) = parsed_c_return_type {
            if parsed_return_type.struct_name.is_some() && !parsed_return_type.struct_pointer {
                return Err(self.error("only pointer-to-struct types are supported"));
            }
            if parsed_return_type.interface_type == InterfaceType::Void {
                return Err(self.error("pure Click functions must return a value"));
            }
        }
        let decreases = if self.peek_ident() == Some("decreases") {
            self.position += 1;
            Some(self.parse_measure_component()?)
        } else {
            None
        };
        // A primitive operation of the Click library, `function len<T>(v:
        // Vec<T>) -> uint64;`, has no definition: its axioms say what it is.
        if self.peek() == Some(&Token::Semicolon) {
            if !self.library_primitives {
                return Err(self.error(format!(
                    "function `{name}` needs a body; only the Click library declares a function without one"
                )));
            }
            if decreases.is_some() {
                return Err(self.error(format!(
                    "function `{name}` has no body, so it has no recursion to measure"
                )));
            }
            self.position += 1;
            self.names
                .replace(NameKind::TypeParameter, previous_type_parameters);
            self.rust_slice_params = previous_slice_params;
            return Ok(ClickFunctionDefinition {
                name,
                type_parameters,
                parameters: parsed_parameters.parameters,
                return_type,
                return_object_class,
                decreases: None,
                body: None,
            });
        }
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
        let previous_spec_parameter_types = std::mem::replace(
            &mut self.spec_parameter_types,
            spec_parameter_types(&parsed_parameters.parameters),
        );
        let shadowed_callbacks = parsed_parameters
            .parameters
            .iter()
            .filter(|parameter| matches!(parameter.click_type(), ClickType::Function { .. }))
            .map(|parameter| {
                self.bind_let_operand(parameter.name(), Some(parameter.click_type()), None)
            })
            .collect();
        let body = if return_type == ClickType::Proposition {
            self.parse_proposition()
                .map(|body| ContractExpression::Proposition(Box::new(body)))
        } else {
            self.parse_branch_value(return_type == ClickType::Program(InterfaceType::Bool))
        };
        self.unbind_let_operands(shadowed_callbacks);
        self.spec_parameter_types = previous_spec_parameter_types;
        let body = body?;
        // A `-> Integer` body is read where its result is used.
        let body = if return_type == ClickType::Integer {
            self.at_integer_position(body)
        } else {
            body
        };
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
            body: Some(body),
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
                !algebraic_field_c_type_supported(ty.interface_type)
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
                    let Some(interface_type) = click_type.interface_type() else {
                        return Err(self.error(
                            "resource witnesses must have a C pointer type, not an algebraic type",
                        ));
                    };
                    if !interface_type.is_pointer() {
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
                        interface_type,
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
        if click_type != ClickType::Program(InterfaceType::Int32) {
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
            binder: binder.into(),
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
        self.parse_parameters_with_resources_and_functions(allow_resources, false)
    }

    fn parse_parameters_with_resources_and_functions(
        &mut self,
        allow_resources: bool,
        allow_functions: bool,
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
                    if let Some(pointee) = element.interface_type.pointee_type() {
                        self.rust_slice_elements.insert(name.clone(), pointee);
                    }
                    self.implied_library_modules.insert(SLICE_MODULE);
                    parameters.push(self.parse_parameter_array_suffix(name, element)?.parameter);
                    parameters.push(FunctionParameter {
                        click_type: ClickType::Program(InterfaceType::UInt64(LongRank::Long)),
                        name: length,
                        struct_name: None,
                        function_pointer_signature: None,
                        constant: false,
                        pointee_constant: false,
                        reference: false,
                    });
                } else {
                    let (click_type, parsed_c_type) = self.parse_click_type()?;
                    if click_type == ClickType::Proposition
                        || (!allow_functions && matches!(click_type, ClickType::Function { .. }))
                    {
                        return Err(self.error(
                            "specification function declaration parameters are not supported yet",
                        ));
                    }

                    let parsed_parameter = if let Some(parsed_type) = parsed_c_type {
                        if self.peek() == Some(&Token::LParen) {
                            let (interface_type, function_pointer_signature) =
                                self.parse_abstract_function_pointer_type(parsed_type)?;
                            ParsedParameter {
                                parameter: FunctionParameter {
                                    click_type: ClickType::Program(interface_type),
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
                            == ClickType::Program(InterfaceType::Int32PointerPointer)
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
                        reference_params.insert(parsed_parameter.parameter.name.clone());
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
        // `axiom` states a trusted fact about the library's primitive
        // operations; it has the shape of a theorem without proofs.
        let axiom = self.peek_ident() == Some("axiom");
        if axiom {
            if !self.library_primitives {
                return Err(self.error(
                    "an `axiom` is reserved for the Click library; state a `theorem` and prove it",
                ));
            }
            self.position += 1;
        } else {
            self.expect_ident_spelling("theorem")?;
        }
        let name = self.expect_ident("theorem name")?;
        let type_parameters = self.parse_click_type_parameters()?;
        let previous_type_parameters = self.names.replace(
            NameKind::TypeParameter,
            type_parameters.iter().cloned().collect(),
        );
        self.expect(Token::LParen)?;
        let parsed_parameters = self.parse_click_parameters()?;
        self.expect(Token::RParen)?;
        let previous_resource_parameters = std::mem::replace(
            &mut self.resource_parameters,
            parsed_parameters
                .parameters
                .iter()
                .enumerate()
                .filter(|(_, p)| p.click_type() == &ClickType::Resource)
                .map(|(i, p)| (p.name().to_string(), i))
                .collect(),
        );
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
        let previous_let_operands = self.take_let_operands();
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
        if axiom && executes.is_some() {
            return Err(self.error(format!(
                "axiom `{name}` relates pure values; it cannot state an execution"
            )));
        }
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
        let previous_spec_parameter_types = std::mem::replace(
            &mut self.spec_parameter_types,
            spec_parameter_types(&parsed_parameters.parameters),
        );
        let previous_theorem_pointer_params = std::mem::replace(
            &mut self.theorem_pointer_params,
            parsed_parameters
                .parameters
                .iter()
                .filter(|parameter| {
                    parameter
                        .click_type()
                        .interface_type()
                        .is_some_and(|interface_type| interface_type.is_pointer())
                })
                .map(|parameter| parameter.name().to_string())
                .collect(),
        );
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
                    self.bind_contract_let_operand(&binding);
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
                                "`let name: type;` declares a value parameter of a function contract; a theorem takes its values as parameters",
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
        self.spec_parameter_types = previous_spec_parameter_types;
        self.theorem_pointer_params = previous_theorem_pointer_params;
        self.resource_parameters = previous_resource_parameters;
        self.names
            .replace(NameKind::IntegerParameter, previous_integer_params);
        self.names
            .replace(NameKind::IntegerLet, previous_integer_lets);
        self.restore_let_operands(previous_let_operands);
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
        if axiom {
            if ensure_kinds
                .iter()
                .any(|kind| *kind != ClaimClauseKind::Ensures)
                || requires
                    .iter()
                    .any(|requirement| !matches!(requirement, Requirement::Proposition(_)))
            {
                return Err(self.error(format!(
                    "axiom `{name}` states only `requires` and `ensures` propositions"
                )));
            }
            if ensures
                .iter()
                .any(|ensure| !matches!(ensure.proof, SourceProof::Default))
            {
                return Err(self.error(format!(
                    "axiom `{name}` is trusted, so its clauses carry no proof"
                )));
            }
        }
        Ok(TheoremDefinition {
            axiom,
            generic_pointer_parameters: parsed_parameters
                .parameters
                .iter()
                .filter(|parameter| {
                    matches!(
                        parameter.click_type(),
                        ClickType::Program(InterfaceType::ParameterPointer(_))
                    )
                })
                .map(|parameter| parameter.name().to_owned())
                .collect(),
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
                match (field.interface_type(), field.struct_name()) {
                    (InterfaceType::Parameter(_), _) => return true,
                    (InterfaceType::Int32, Some(embedded)) => pending.push(embedded.to_string()),
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
        let names = self.parse_cpp_template_parameters()?;
        let previous_abstract = self.rust_abstract_type_parameters.clone();
        self.rust_abstract_type_parameters.extend(names);
        // A pure virtual method of a class template has no body: its
        // interface is written `extern`.
        let external = self.peek_ident() == Some("extern");
        let block = self.parse_function_block_in_scope(external);
        self.rust_abstract_type_parameters = previous_abstract;
        block
    }

    /// Whether `template<...>` introduces a named contract, as a generic
    /// method's interface on its class's memory is written.
    fn cpp_template_contract_follows(&self) -> bool {
        let mut index = self.position + 1;
        if self.tokens.get(index) != Some(&Token::LessThan) {
            return false;
        }
        while let Some(token) = self.tokens.get(index) {
            index += 1;
            if *token == Token::GreaterThan {
                return matches!(self.tokens.get(index), Some(Token::Ident(word)) if word == "contract");
            }
        }
        false
    }

    /// A named contract of a class template's method, stated once for every
    /// type argument.
    fn parse_cpp_template_contract(&mut self) -> Result<ContractDefinition, ClickError> {
        let names = self.parse_cpp_template_parameters()?;
        let previous_abstract = self.rust_abstract_type_parameters.clone();
        self.rust_abstract_type_parameters.extend(names);
        let contract = self.parse_contract_definition();
        self.rust_abstract_type_parameters = previous_abstract;
        contract
    }

    /// `template<class T, ...>`, the names of its type parameters.
    fn parse_cpp_template_parameters(&mut self) -> Result<Vec<String>, ClickError> {
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
        Ok(names)
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
        if !self.in_contract_definition {
            self.contract_value_parameters.clear();
        }
        let block_scope = self.names.scope();
        let previous_resource_targets = std::mem::take(&mut self.names.resource_targets);
        let previous_resource_bindings = std::mem::take(&mut self.names.resource_bindings);
        let written_instance = self.rust_written_instances.contains(&self.position);
        // A crate trait's method is declared without `extern`, as Rust
        // writes it in the `trait` block.
        if external && self.rust_trait_interface.is_none() {
            self.expect_ident_spelling("extern")?;
        }
        // Rust marks a generated instance at `fn`, after `extern`; C++
        // marks its declaration at `extern` itself.
        let written_instance =
            written_instance || self.rust_written_instances.contains(&self.position);
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
            && let Some(generic) = self.cpp_generic_instances.get(signature.name())
        {
            // A sidecar states neither a library interface nor an instance of it.
            if crate::languages::cpp::standard_library::is_library_generic(generic) {
                return Err(self.error(format!(
                    "`{}` has the Click library's contract (`library/cpp/`); a sidecar does \
                     not restate a library interface",
                    crate::languages::display_source_names(signature.name())
                )));
            }
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
        // A Rust function's loops each advance an iterator its proof names
        // `iter` there and `loop(i).iter` elsewhere.
        let loop_iterators = self
            .local_struct_pointers_by_function
            .get(&table_name)
            .map(|locals| locals.loop_iterators.clone())
            .unwrap_or_default();
        let signature = signature.with_rust_loop_iterators(&loop_iterators);
        let previous_loop_iterators =
            std::mem::replace(&mut self.rust_loop_iterators, loop_iterators);

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
        let previous_let_operands = self.take_let_operands();
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
                .filter(|parameter| parameter.interface_type() == InterfaceType::VoidPointer)
                .map(|parameter| parameter.name().to_string())
                .collect(),
        );
        let previous_c_object_names = std::mem::replace(
            &mut self.names.program_object_names,
            self.program_object_names_by_function
                .get(&table_name)
                .cloned(),
        );
        let previous_hosted_stdout = std::mem::replace(
            &mut self.hosted_stdout,
            self.hosted_stdout_by_function.get(&table_name).cloned(),
        );
        let previous_c_parameter_types = std::mem::replace(
            &mut self.names.program_parameter_types,
            signature
                .parameters()
                .iter()
                .map(|parameter| (parameter.name().to_string(), parameter.interface_type()))
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
        let previous_result_c_type = self
            .current_result_interface_type
            .replace(signature.return_type());
        let local_pointers = self
            .local_struct_pointers_by_function
            .get(&table_name)
            .into_iter()
            .flat_map(|locals| &locals.pointers)
            .filter(|name| {
                !signature
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.name() == name.as_str())
            })
            .cloned()
            .collect();
        let previous_local_pointers =
            std::mem::replace(&mut self.current_local_pointers, local_pointers);
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
                    self.bind_contract_let_operand(&binding);
                    if binding.kind == ContractLetBindingKind::Parameter {
                        // A clause would read the value where the body reads
                        // the program's variable.
                        if self.names.is_program_variable(&binding.name) {
                            return Err(self.error(format!(
                                "contract value parameter `{}` takes the name of a C variable; a clause would read the value where the body reads the variable; choose another name",
                                binding.name
                            )));
                        }
                        let interface_type = binding
                            .click_type
                            .as_ref()
                            .and_then(ClickType::interface_type)
                            .filter(|interface_type| {
                                !interface_type.is_pointer()
                                    && *interface_type != InterfaceType::Void
                            })
                            .ok_or_else(|| {
                                self.error(format!(
                                    "contract value parameter `{}` must have a scalar type",
                                    binding.name
                                ))
                            })?;
                        self.contract_value_parameters.push(FunctionParameter {
                            click_type: ClickType::Program(interface_type),
                            name: binding.name.clone(),
                            struct_name: None,
                            function_pointer_signature: None,
                            constant: false,
                            pointee_constant: false,
                            reference: false,
                        });
                        // A caller's call map names an ordinary function's
                        // value parameter, `{ n: k }`.
                        if !self.in_contract_definition {
                            self.callee_resource_binders
                                .entry(signature.name().to_string())
                                .or_default()
                                .insert(
                                    binding.name.clone(),
                                    Self::value_parameter_callee_binder(),
                                );
                        }
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
                        let resource = self.parse_function_contract_memory_binding()?;
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
                        let first = self.parse_measure_component()?;
                        if self.peek() == Some(&Token::Comma) {
                            components.push(first);
                            while self.peek() == Some(&Token::Comma) {
                                self.position += 1;
                                components.push(self.parse_measure_component()?);
                            }
                            self.expect(Token::RParen)?;
                        } else {
                            self.position = start;
                        }
                    }
                    if components.is_empty() {
                        let measure = self.parse_measure_component()?;
                        self.expect(Token::Semicolon)?;
                        decreases = Some(FunctionDecrease::Unresolved(
                            substitute_contract_expression(&measure, &substitutions)
                                .map_err(|message| self.error(message))?,
                        ));
                    } else {
                        self.expect(Token::Semicolon)?;
                        decreases = Some(FunctionDecrease::Lexicographic(
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
                    if self.value_binder_follows(false) {
                        return Err(self.value_binder_refusal(false));
                    }
                    let resource = self.parse_function_contract_memory_binding()?;
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
                    if self.value_binder_follows(true) {
                        return Err(self.value_binder_refusal(true));
                    }
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
                    if self.value_binder_follows(false) {
                        return Err(self.value_binder_refusal(false));
                    }
                    let resource = self.parse_function_contract_memory_binding()?;
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
                    let resource = self.parse_function_contract_memory_binding()?;
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
                            "`exceptional ensures` requires `throws` in the signature of `{}`",
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
        if external && written_instance {
            // Generated externs inherit the generic declaration's contract at
            // concrete types. Its clause proofs are checked on the generic
            // body, not copied into the extern contracts of its instances.
            for clause in ensures.iter_mut().chain(exceptional_ensures.iter_mut()) {
                clause.proof = SourceProof::Default;
            }
        }
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
                || requires.iter().any(|requirement| matches!(requirement, Requirement::Resource(resource)
                    if !matches!(resource, ResourceClause::OwnMemory(_) | ResourceClause::ViewMemory(_) | ResourceClause::MemoryAggregate { .. })))
                || ensures.iter().any(|ensure| {
                    matches!(ensure.ensure(), Ensure::Resource(_)) && !ensure.borrowed
                })
                || requires
                    .iter()
                    .filter(|requirement| matches!(requirement, Requirement::Resource(_)))
                    .count()
                    != ensures.iter().filter(|ensure| ensure.borrowed).count()
                        + requires
                            .iter()
                            .filter(|requirement| {
                                matches!(
                                    requirement,
                                    Requirement::Resource(
                                        ResourceClause::ViewMemory(_)
                                            | ResourceClause::MemoryAggregate {
                                                access: ResourceAccessMode::View,
                                                ..
                                            }
                                    )
                                )
                            })
                            .count())
        {
            return Err(self.error("throwing contracts support borrowed memory `owns` and `views`, not resource transitions"));
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
        let program_object_names = self
            .program_object_names_by_function
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
        self.names.program_parameter_types = previous_c_parameter_types;
        self.names.program_object_names = previous_c_object_names;
        self.hosted_stdout = previous_hosted_stdout;
        self.rust_loop_iterators = previous_loop_iterators;
        let parameter_struct_casts = std::mem::replace(
            &mut self.names.parameter_struct_casts,
            previous_parameter_struct_casts,
        );
        self.in_function_block = previous_function_block;
        self.names.end_declaration(block_scope);
        self.names.resource_bindings = previous_resource_bindings;
        self.names.resource_targets = previous_resource_targets;
        self.names.aggregate_objects = previous_aggregate_objects;
        self.names.global_array_shapes = previous_global_array_shapes;
        self.names
            .replace(NameKind::StructArrayParameter, previous_struct_array_params);
        self.names
            .replace(NameKind::ReferenceParameter, previous_reference_params);
        self.current_reference_result = previous_reference_result;
        self.current_result_interface_type = previous_result_c_type;
        self.current_local_pointers = previous_local_pointers;
        self.names
            .replace(NameKind::IntegerParameter, previous_integer_params);
        self.names
            .replace(NameKind::IntegerLet, previous_integer_lets);
        self.restore_let_operands(previous_let_operands);
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
                    crate::kernel::BindingName::from(parameter.name()),
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
                    crate::kernel::BindingName::from(name),
                    super::scalar_field_places(layout, &self.struct_layouts),
                );
            }
        }
        if let Some(places) = self.local_bindings.field_places.get(&table_name) {
            parameter_field_places.extend(
                places
                    .iter()
                    .map(|(binding, fields)| (binding.clone(), fields.clone())),
            );
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
        // An ordinary function's value parameters follow its C parameters
        // too, as the contract value parameters a call supplies and its body
        // is proved for every value of.
        let witness_count = if self.in_contract_definition {
            0
        } else {
            let value_parameters = std::mem::take(&mut self.contract_value_parameters);
            let count = value_parameters.len();
            signature.parameters.extend(value_parameters);
            count
        };
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
            program_object_names,
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
            witness_count,
        })
    }

    fn parse_contract_let_binding(&mut self) -> Result<ContractLetBinding, ClickError> {
        self.expect_ident_spelling("let")?;
        let name = self.expect_ident("let binding name")?;
        self.refuse_bool_literal_binder(&name)?;
        let mut click_type = if self.peek() == Some(&Token::Colon) {
            self.position += 1;
            let (mut click_type, parsed_type) = self.parse_click_type()?;
            if let Some(parsed_type) = parsed_type
                && let Some(struct_name) = parsed_type.struct_name
            {
                if !parsed_type.struct_pointer {
                    return Err(self.error("only pointer-to-struct types are supported"));
                }
                click_type = ClickType::CObjectPointer {
                    interface_type: click_type
                        .interface_type()
                        .expect("a parsed struct pointer has a C interface type"),
                    struct_name,
                };
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
            let value = value?;
            // The annotation is the value's expected type; without one,
            // arithmetic on a machine value has no meaning.
            let value = match &click_type {
                Some(ClickType::Integer) => self.at_integer_position(value),
                Some(ClickType::Program(interface_type)) => {
                    let value = self.typed_let_literal(&name, *interface_type, value)?;
                    self.refuse_mixed_narrow_arithmetic(&name, *interface_type, &value)?;
                    value
                }
                Some(_) => value,
                None => {
                    self.refuse_untyped_machine_arithmetic(&name, &value)?;
                    // An untyped `let` has its value's type, so one whose
                    // value is an exact Integer is an Integer binding.
                    if self.integer_operand(&value) {
                        click_type = Some(ClickType::Integer);
                    }
                    value
                }
            };
            ContractLetBindingKind::Value(value)
        } else if self.peek_ident() == Some("where") {
            self.position += 1;
            if click_type.is_none() {
                return Err(self.error("`let ... where` requires an explicit type annotation"));
            }
            ContractLetBindingKind::Where(self.parse_proposition()?)
        } else if self.peek() == Some(&Token::Semicolon) && click_type.is_some() {
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
                .find(|parameter| parameter.click_type().interface_type().is_none())
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
                    return_type: InterfaceType::Void,
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
        self.rust_vec_params.clear();
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
                interface_type: InterfaceType::Void,
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
            parsed_return_type.interface_type
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
        let mut receiver_constant = false;
        let has_receiver = receiver.is_some();
        if let Some(record) = receiver {
            // `Rec::m(...) const` reads through a `const Rec* this`.
            let constant = self.peek_ident() == Some("const");
            if constant {
                self.position += 1;
            }
            receiver_constant = constant;
            let this = self.parse_parameter_array_suffix(
                "this".into(),
                ParsedType {
                    interface_type: InterfaceType::Int32Pointer,
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
        // A path several C++ declarations share, as overloads do, names the
        // one whose receiver constness and parameter types the head writes.
        let name = match self.cpp_overloads.get(&name) {
            Some(overloads) => {
                let written = &parsed_parameters.parameters[usize::from(has_receiver)..];
                let mut selected =
                    overloads.iter().filter(|overload| {
                        overload.constant == receiver_constant
                            && overload.parameters.len() == written.len()
                            && overload.parameters.iter().zip(written).all(
                                |(expected, parameter)| *expected == parameter.interface_type(),
                            )
                    });
                match (selected.next(), selected.next()) {
                    (Some(overload), None) => overload.name.clone(),
                    (selected, _) => {
                        return Err(self.error(format!(
                            "`{}` names C++ overloads, {} this head's receiver constness \
                             and parameter types",
                            crate::languages::display_source_names(&name),
                            if selected.is_some() {
                                "more than one with"
                            } else {
                                "none with"
                            }
                        )));
                    }
                }
            }
            None => name,
        };
        let exceptional_type = if self.peek_ident() == Some("throws") {
            self.position += 1;
            let parsed = self.parse_type()?;
            if parsed.constant
                || parsed.pointee_constant
                || parsed.reference
                || parsed.struct_pointer
            {
                return Err(self.error("an exception payload is an unqualified value type"));
            }
            match (parsed.interface_type, parsed.struct_name) {
                (_, Some(name)) if self.verifies_cpp() => Some(InterfaceType::Parameter(
                    crate::languages::cpp::names::opaque_exception_type(&name),
                )),
                (ty @ (InterfaceType::Int32 | InterfaceType::Parameter(_)), None) => Some(ty),
                _ => {
                    return Err(self.error(
                        "the exceptional payload must be int32 or a resolved opaque value type",
                    ));
                }
            }
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

    /// The right operand of a binary operator, with any `as` casts.
    #[inline(never)]
    fn parse_binary_operand(&mut self) -> Result<ContractExpression, ClickError> {
        let operand = self.parse_contract_unary()?;
        self.parse_casts(operand)
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
        let shadowed = self.names.program_parameter_types.contains_key(name)
            || self
                .names
                .program_object_names
                .as_ref()
                .is_some_and(|names| names.contains(name))
            || self.names.contains(NameKind::ProofBinder, name)
            || self.names.arm_binding_types.contains_key(name);
        (!shadowed).then_some(value)
    }

    /// Refuse a Click binder spelled `true` or `false`: inside Click those
    /// spellings are the `bool` literals, so the binder could never be read.
    fn refuse_bool_literal_binder(
        &self,
        name: &(impl binders::BinderKey + ?Sized),
    ) -> Result<(), ClickError> {
        let Some(binders::BinderKeyRef::Written(name)) = name.binder_key() else {
            return Ok(());
        };
        if matches!(name, "true" | "false") {
            return Err(self.error(format!(
                "`{name}` is a `Bool` literal and cannot name a Click binder"
            )));
        }
        Ok(())
    }

    /// Refuse an unbound loop value only when the frontend supplied the
    /// function's complete object-name table.
    fn refuse_unknown_loop_value(&self, name: &str) -> Result<(), ClickError> {
        if let Some(context) = &self.loop_name_context
            && self.names.program_object_names.is_some()
            // A loop's returning arm may close the function's postcondition.
            // Execution checking decides when this built-in value exists.
            && name != "result"
            // A loop's pass count is built in.
            && name != crate::surface::LOOP_ITERATIONS_NAME
            && !self.names.is_bound(name)
            && !self.quantifier_binders.iter().any(|bound| bound == name)
            && !self.loop_proof_value_names.contains(name)
        {
            return Err(self
                .error(format!("unknown name `{name}` in {context}"))
                .with_kind(ClickErrorKind::Type));
        }
        Ok(())
    }

    /// A C variable, or the length a slice parameter's `name.len()` denotes.
    #[inline(never)]
    fn c_variable_expression(&mut self, name: String) -> Result<ContractExpression, ClickError> {
        if let Some(expression) = self.take_rust_iterator_method(&name, None)? {
            return Ok(expression);
        }
        self.refuse_unknown_loop_value(&name)?;
        if let Some(expression) = self.take_rust_vec_method(&name)? {
            return Ok(expression);
        }
        if name == "stdout"
            && let Some(value) = &self.hosted_stdout
        {
            return Ok(ContractExpression::QualifiedC {
                name,
                lowered: ProgramExpression::Value(value.clone()),
            });
        }
        let name = self.take_rust_slice_len(&name).unwrap_or(name);
        Ok(ContractExpression::ProgramExpression(
            ProgramExpression::Variable((name).into()),
        ))
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
                None => self.parse_program_function_pointer_typedef()?,
            };
            if let Some((interface_type, function_pointer_signature)) = callable {
                let name = self.expect_ident("parameter name")?;
                parameters.push(FunctionParameter {
                    click_type: ClickType::Program(interface_type),
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
                    interface_type: element,
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
                let (name, interface_type, function_pointer_signature) =
                    self.parse_function_pointer_declarator(parsed_type.clone())?;
                ParsedParameter {
                    parameter: FunctionParameter {
                        click_type: ClickType::Program(interface_type),
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
                    == ClickType::Program(InterfaceType::Int32PointerPointer)
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
                reference_params.insert(parsed_parameter.parameter.name.clone());
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
        // Opaque standard exception values have no addressable layout.
        if self.verifies_cpp()
            && (self.peek_ident() == Some("std::ios_base::failure")
                || (self.peek_ident() == Some("std")
                    && self.tokens.get(self.position + 1) == Some(&Token::ColonColon)
                    && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(name)) if name == "ios_base")
                    && self.tokens.get(self.position + 3) == Some(&Token::ColonColon)
                    && matches!(self.tokens.get(self.position + 4), Some(Token::Ident(name)) if name == "failure")))
        {
            self.position += if self.peek_ident() == Some("std::ios_base::failure") {
                1
            } else {
                5
            };
            if matches!(self.peek(), Some(Token::Amp | Token::Star)) {
                return Err(self.error("opaque exception payloads have no addressable layout"));
            }
            return Ok(ParsedType {
                interface_type: InterfaceType::Parameter(crate::kernel::TypeParameterName::intern(
                    "std::ios_base::failure",
                )),
                struct_name: None,
                struct_pointer: false,
                constant: is_constant,
                pointee_constant: false,
                reference: false,
            });
        }
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
                    interface_type: InterfaceType::ParameterPointer(parameter),
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: is_constant,
                    reference,
                });
            }
            return Ok(ParsedType {
                interface_type: InterfaceType::Parameter(parameter),
                struct_name: None,
                struct_pointer: false,
                constant: is_constant,
                pointee_constant: false,
                reference: false,
            });
        }
        // C++'s `std::byte` is a byte, Click's `uint8`.
        let std_byte = self.verifies_cpp()
            && self.peek_ident() == Some("std")
            && self.tokens.get(self.position + 1) == Some(&Token::ColonColon)
            && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(word)) if word == "byte");
        // C++ names a record by its own name or path, `std::span<int>`; C
        // writes `struct name`.
        let qualified_record = if self.verifies_cpp() && !std_byte {
            self.parse_cpp_record_type()
        } else {
            None
        };
        let spelling = match &qualified_record {
            Some(record) => record.clone(),
            None if std_byte => {
                self.position += 3;
                "uint8".to_string()
            }
            None => self.expect_ident("type")?,
        };
        let cpp_record = qualified_record.is_some()
            || (self.verifies_cpp() && self.struct_layouts.contains_key(&spelling));
        // A function head may write a typedef name of the verified C source
        // for the type it stands for, where the name is not a standard
        // spelling; a specification writes Click's type.
        let typedef_struct = match self.c_typedefs.get(&spelling) {
            Some(syntax::CHeadTypedef::Struct {
                name,
                interface_type,
                constant,
                pointee_constant,
            }) => {
                self.check_head_typedef(&spelling)?;
                is_constant |= constant;
                Some((name.clone(), *interface_type, *pointee_constant))
            }
            _ => None,
        };
        // A pointer alias has already supplied its `*`s: a `const` written
        // before it qualifies the pointer, as in C.
        let alias_pointer = typedef_struct
            .as_ref()
            .filter(|(_, interface_type, _)| *interface_type != InterfaceType::Int32)
            .map(|(_, interface_type, pointee_constant)| (*interface_type, *pointee_constant));
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
                    interface_type: InterfaceType::Int32Pointer,
                    struct_name: Some(struct_name),
                    struct_pointer: true,
                    constant: false,
                    pointee_constant: object_constant,
                    reference: true,
                });
            }
            if self.peek() == Some(&Token::Star) || alias_pointer.is_some() {
                let (mut interface_type, mut pointee_constant) =
                    alias_pointer.unwrap_or((InterfaceType::Int32, false));
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
                    interface_type = match interface_type {
                        InterfaceType::Int32 => InterfaceType::Int32Pointer,
                        InterfaceType::Int32Pointer => InterfaceType::Int32PointerPointer,
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
                    interface_type,
                    struct_name: Some(struct_name),
                    struct_pointer: true,
                    constant: object_constant,
                    pointee_constant,
                    reference: false,
                });
            }
            return Ok(ParsedType {
                interface_type: InterfaceType::Int32Pointer,
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
        let integer = integer.map(|(interface_type, count)| {
            if self.exact_long_rank {
                (interface_type, count)
            } else {
                (interface_type.erase_long_rank(), count)
            }
        });
        let typedef_rank = if self.exact_long_rank {
            self.int64_t_rank
        } else {
            LongRank::Long
        };
        // A scalar pointer alias's pointee qualification, as for a struct one.
        let mut alias_scalar_pointer = None;
        let scalar_type = if let Some((interface_type, count)) = integer {
            self.position += count - 1;
            interface_type
        } else {
            match spelling.as_str() {
                "void" => InterfaceType::Void,
                // Stage 5 (decision D4): a function head restates its
                // language's declaration, `bool` or `_Bool`; Click's own
                // positions write `Bool`, and a Rust sidecar writes Rust's
                // `bool` there as it writes `i32`.
                "_Bool" | "bool" => {
                    if !self.exact_long_rank && !self.verifies_rust() {
                        return Err(
                            self.error(format!("`{spelling}` is not a Click type; write `Bool`"))
                        );
                    }
                    InterfaceType::Bool
                }
                "Bool" => InterfaceType::Bool,
                "int8" | "int8_t" => InterfaceType::Int8,
                "int16" | "int16_t" => InterfaceType::Int16,
                "int32" | "int32_t" => InterfaceType::Int32,
                "uint8" | "uint8_t" => InterfaceType::UInt8,
                "uint16" | "uint16_t" => InterfaceType::UInt16,
                "uint32" | "uint32_t" => InterfaceType::UInt32,
                "int64" | "ssize_t" => InterfaceType::Int64(LongRank::Long),
                "int64_t" => InterfaceType::Int64(typedef_rank),
                "uint64" | "size_t" => InterfaceType::UInt64(LongRank::Long),
                "uint64_t" => InterfaceType::UInt64(typedef_rank),
                "int128" => InterfaceType::Int128,
                "uint128" => InterfaceType::UInt128,
                "float" => InterfaceType::Float32,
                "double" => InterfaceType::Float64,
                "volatile" => {
                    return Err(self.error("the `volatile` qualifier is not supported by Click"));
                }
                _ if let Some(typedef) = self.c_typedefs.get(&spelling) => {
                    self.check_head_typedef(&spelling)?;
                    let syntax::CHeadTypedef::Scalar {
                        interface_type,
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
                    if interface_type.is_pointer() {
                        alias_scalar_pointer = Some(pointee_constant);
                    }
                    interface_type
                }
                _ => {
                    return Err(self.error(format!(
                    "unknown C type `{spelling}`; expected a supported standard spelling or `struct`"
                )));
                }
            }
        };
        let mut interface_type = scalar_type;
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
            interface_type = match interface_type {
                InterfaceType::Void if reference => {
                    return Err(self.error("a reference to `void` is not a type"));
                }
                InterfaceType::Void => InterfaceType::VoidPointer,
                InterfaceType::Int8 => InterfaceType::Int8Pointer,
                InterfaceType::Int16 => InterfaceType::Int16Pointer,
                InterfaceType::UInt16 => InterfaceType::UInt16Pointer,
                InterfaceType::Int32 => InterfaceType::Int32Pointer,
                InterfaceType::Char(plain) => InterfaceType::CharPointer(plain),
                InterfaceType::UInt8 => InterfaceType::UInt8Pointer,
                InterfaceType::UInt32 => InterfaceType::UInt32Pointer,
                InterfaceType::Int64(rank) => InterfaceType::Int64Pointer(rank),
                InterfaceType::Int128 => InterfaceType::Int128Pointer,
                InterfaceType::UInt64(rank) => InterfaceType::UInt64Pointer(rank),
                InterfaceType::UInt128 => InterfaceType::UInt128Pointer,
                InterfaceType::Float32 if !reference => InterfaceType::Float32Pointer,
                InterfaceType::Float64 if !reference => InterfaceType::Float64Pointer,
                InterfaceType::Int8Pointer => InterfaceType::Int8PointerPointer,
                InterfaceType::Int16Pointer => InterfaceType::Int16PointerPointer,
                InterfaceType::UInt16Pointer => InterfaceType::UInt16PointerPointer,
                InterfaceType::Int32Pointer => InterfaceType::Int32PointerPointer,
                InterfaceType::CharPointer(plain) => InterfaceType::CharPointerPointer(plain),
                InterfaceType::UInt8Pointer => InterfaceType::UInt8PointerPointer,
                InterfaceType::UInt32Pointer => InterfaceType::UInt32PointerPointer,
                InterfaceType::Int64Pointer(rank) => InterfaceType::Int64PointerPointer(rank),
                InterfaceType::Int128Pointer => InterfaceType::Int128PointerPointer,
                InterfaceType::UInt64Pointer(rank) => InterfaceType::UInt64PointerPointer(rank),
                InterfaceType::UInt128Pointer => InterfaceType::UInt128PointerPointer,
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
            interface_type,
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
                parsed.interface_type,
                struct_name.as_deref(),
                &self.struct_layouts,
            ),
        }
    }

    fn parse_click_type(&mut self) -> Result<(ClickType, Option<ParsedType>), ClickError> {
        if self.peek_ident() == Some("Prop") {
            self.position += 1;
            return Ok((ClickType::Proposition, None));
        }
        if self.peek_ident() == Some("fn") && self.peek_next() == Some(&Token::LParen) {
            if self.algebraic_type_nesting >= MATCH_NESTING_LIMIT {
                return Err(self
                    .error("specification function type nesting exceeds Click's supported depth"));
            }
            self.algebraic_type_nesting += 1;
            self.position += 2;
            let mut parameters = Vec::new();
            if self.peek() != Some(&Token::RParen) {
                loop {
                    parameters.push(self.parse_click_type()?.0);
                    if self.peek() != Some(&Token::Comma) {
                        break;
                    }
                    self.position += 1;
                }
            }
            self.expect(Token::RParen)?;
            self.expect(Token::Arrow)?;
            let (result, _) = self.parse_click_type()?;
            self.algebraic_type_nesting -= 1;
            return Ok((
                ClickType::Function {
                    parameters,
                    result: Box::new(result),
                },
                None,
            ));
        }
        if let Some(element) = self.take_rust_slice_value_type()? {
            return Ok((
                ClickType::Algebraic(AlgebraicTypeApplication {
                    rigid: false,
                    name: "Slice".to_string(),
                    arguments: vec![ClickType::Program(element)],
                }),
                None,
            ));
        }
        if let Some(parsed) = self.parse_rust_click_type()? {
            return Ok((ClickType::Program(parsed.interface_type), Some(parsed)));
        }
        let Some(name) = self.peek_ident() else {
            return Err(self.error("expected Click type"));
        };
        // A C++ generic method's or resource's abstract type parameter.
        let interface_type = is_c_type_keyword(name)
            || (self.verifies_cpp() && self.rust_abstract_type_parameters.contains(name));
        if interface_type || self.at_cpp_record_type() {
            let parsed = self.parse_type()?;
            return Ok((ClickType::Program(parsed.interface_type), Some(parsed)));
        }
        let Some(name) = self.peek_ident() else {
            return Err(self.error("expected Click type"));
        };
        if name == "Resource" {
            self.position += 1;
            return Ok((ClickType::Resource, None));
        }
        if name == "Integer" {
            self.position += 1;
            return Ok((ClickType::Integer, None));
        }
        if self.names.contains(NameKind::TypeParameter, name) {
            let name = name.to_string();
            self.position += 1;
            if self.peek() == Some(&Token::Star) {
                self.position += 1;
                return Ok((
                    ClickType::Program(InterfaceType::ParameterPointer(
                        crate::kernel::TypeParameterName::intern(&name),
                    )),
                    None,
                ));
            }
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

    fn scalar_struct_value_type(&self, struct_name: &str) -> Result<InterfaceType, ClickError> {
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
            if field.interface_type() == InterfaceType::Int32
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
                || (field.struct_name().is_some() && !field.interface_type().is_pointer())
                || !matches!(
                    field.interface_type(),
                    InterfaceType::Int8 | InterfaceType::Int16
                        | InterfaceType::Int32
                        | InterfaceType::Char(_)
                        | InterfaceType::UInt8
                        | InterfaceType::UInt16
                        | InterfaceType::UInt32
                        | InterfaceType::Int64(_)
                        | InterfaceType::UInt64(_)
                        | InterfaceType::Float32
                        | InterfaceType::Float64
                        | InterfaceType::Int32Array(_)
                        | InterfaceType::UInt32Array(_)
                        | InterfaceType::Int128Array(_)
                        | InterfaceType::Int64Array(_, _)
                        | InterfaceType::UInt128Array(_)
                        | InterfaceType::UInt64Array(_, _)
                        | InterfaceType::CharArray(_, _)
                        | InterfaceType::UInt8Array(_)
                        | InterfaceType::Float32Array(_)
                        | InterfaceType::Float64Array(_)
                        | InterfaceType::Int32Pointer
                        | InterfaceType::CharPointer(_)
                        | InterfaceType::UInt8Pointer
                        | InterfaceType::UInt32Pointer
                        | InterfaceType::Float32Pointer
                        | InterfaceType::Float64Pointer
                        | InterfaceType::Int32PointerPointer
                        | InterfaceType::CharPointerPointer(_)
                        | InterfaceType::UInt8PointerPointer
                        | InterfaceType::Float32PointerPointer
                        | InterfaceType::Float64PointerPointer
                        // A callback field is an eight-byte pointer value,
                        // matching the C boundary's own by-value field set.
                        | InterfaceType::FunctionPointer(_)
                        // A generic Rust struct's field of a type parameter.
                        | InterfaceType::Parameter(_)
                )
            {
                return Err(self.error(format!(
                    "struct-by-value currently supports modeled integer and floating-point fields, fixed scalar arrays, fixed-dimensional embedded-struct arrays, data-pointer fields, function-pointer fields, embedded struct fields, and named union fields; `struct {struct_name}` contains an unsupported field shape"
                )));
            }
        }
        Ok(InterfaceType::UInt8Array(layout.size_bytes()))
    }

    fn parse_function_pointer_declarator(
        &mut self,
        return_type: ParsedType,
    ) -> Result<
        (
            String,
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
        if return_type.struct_name.is_some() && !return_type.struct_pointer {
            return Err(self.error(
                "function-pointer return values must use modeled scalars or struct pointers",
            ));
        }
        self.expect(Token::LParen)?;
        self.expect(Token::Star)?;
        let name = self.expect_ident("function-pointer parameter name")?;
        self.expect(Token::RParen)?;
        let (interface_type, function_pointer_signature) =
            self.parse_function_pointer_signature_tail(return_type)?;
        Ok((name, interface_type, function_pointer_signature))
    }

    /// A parameter type that is a function-pointer typedef name of the
    /// verified C source, `unary f`: its callable type. `None`, with nothing
    /// consumed, for any other type.
    fn parse_program_function_pointer_typedef(
        &mut self,
    ) -> Result<
        Option<(
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        )>,
        ClickError,
    > {
        let Some(name) = self.peek_ident() else {
            return Ok(None);
        };
        let Some(syntax::CHeadTypedef::FunctionPointer {
            interface_type,
            signature,
        }) = self.c_typedefs.get(name)
        else {
            return Ok(None);
        };
        // `unary *f` is a pointer to a function pointer, which the type
        // parser refuses.
        if !matches!(self.peek_next(), Some(Token::Ident(_))) {
            return Ok(None);
        }
        let callable = (*interface_type, signature.clone());
        self.check_head_typedef(name)?;
        self.position += 1;
        Ok(Some(callable))
    }

    /// A parameter type that is a scalar array typedef name of the verified
    /// C source, `triple values`: its element type, length and element
    /// `const`. `None`, with nothing consumed, for any other type.
    fn parse_c_array_typedef(&mut self) -> Result<Option<(InterfaceType, u32, bool)>, ClickError> {
        let Some(name) = self.peek_ident() else {
            return Ok(None);
        };
        let Some(syntax::CHeadTypedef::Array {
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
    ) -> Result<
        Option<(
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        )>,
        ClickError,
    > {
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
    ) -> Result<
        (
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
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
    ) -> Result<
        (
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                let parsed_type = self.parse_type()?;
                if parsed_type.interface_type == InterfaceType::Void {
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
                parameters.push(crate::languages::interface::CallbackParameter::new(
                    parsed_parameter.parameter.interface_type(),
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
                    parameter.interface_type().to_kernel_type(),
                    parameter.pointee_is_constant(),
                )
            })
            .collect::<Vec<_>>();
        let signature = crate::kernel::ProgramType::qualified_function_pointer_signature(
            return_type.interface_type.to_kernel_type(),
            return_type.pointee_constant,
            &parameter_types,
        );
        if signature == crate::kernel::CallbackSignature::UNSPECIFIED {
            return Err(self.error("function-pointer signature uses an unsupported modeled type"));
        }
        let function_pointer_signature = crate::languages::interface::CallbackInterface::new(
            return_type.interface_type,
            return_type.struct_name,
            parameters,
            return_type.pointee_constant,
        );
        Ok((
            InterfaceType::FunctionPointer(signature),
            function_pointer_signature,
        ))
    }

    fn parse_parameter_array_suffix(
        &mut self,
        name: String,
        parsed_type: ParsedType,
    ) -> Result<ParsedParameter, ClickError> {
        if parsed_type.interface_type == InterfaceType::Void {
            return Err(self.error("parameters cannot have type `void`"));
        }
        if self.peek() != Some(&Token::LBracket) {
            let struct_name = parsed_type.struct_name;
            let interface_type = if let Some(struct_name) = struct_name.as_deref()
                && !parsed_type.struct_pointer
            {
                self.scalar_struct_value_type(struct_name)?
            } else {
                parsed_type.interface_type
            };
            return Ok(ParsedParameter {
                parameter: FunctionParameter {
                    click_type: ClickType::Program(interface_type),
                    // The parameter is the pointer that carries the
                    // reference; the written name is the referent.
                    name,
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
                    click_type: ClickType::Program(InterfaceType::Int32Pointer),
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
        let (pointer_type, element_width) = match parsed_type.interface_type {
            InterfaceType::Int8 => (InterfaceType::Int8Pointer, 1),
            InterfaceType::Int16 => (InterfaceType::Int16Pointer, 2),
            InterfaceType::Int32 => (InterfaceType::Int32Pointer, 4),
            InterfaceType::Char(plain) => (InterfaceType::CharPointer(plain), 1),
            InterfaceType::UInt8 => (InterfaceType::UInt8Pointer, 1),
            InterfaceType::UInt16 => (InterfaceType::UInt16Pointer, 2),
            InterfaceType::UInt32 => (InterfaceType::UInt32Pointer, 4),
            InterfaceType::Int64(rank) => (InterfaceType::Int64Pointer(rank), 8),
            InterfaceType::Int128 => (InterfaceType::Int128Pointer, 16),
            InterfaceType::UInt64(rank) => (InterfaceType::UInt64Pointer(rank), 8),
            InterfaceType::UInt128 => (InterfaceType::UInt128Pointer, 16),
            InterfaceType::Int8Pointer => (InterfaceType::Int8PointerPointer, 8),
            InterfaceType::Int16Pointer => (InterfaceType::Int16PointerPointer, 8),
            InterfaceType::UInt16Pointer => (InterfaceType::UInt16PointerPointer, 8),
            InterfaceType::Int32Pointer => (InterfaceType::Int32PointerPointer, 8),
            InterfaceType::CharPointer(plain) => (InterfaceType::CharPointerPointer(plain), 8),
            InterfaceType::UInt8Pointer => (InterfaceType::UInt8PointerPointer, 8),
            InterfaceType::UInt32Pointer => (InterfaceType::UInt32PointerPointer, 8),
            InterfaceType::Int64Pointer(rank) => (InterfaceType::Int64PointerPointer(rank), 8),
            InterfaceType::Int128Pointer => (InterfaceType::Int128PointerPointer, 8),
            InterfaceType::UInt64Pointer(rank) => (InterfaceType::UInt64PointerPointer(rank), 8),
            InterfaceType::UInt128Pointer => (InterfaceType::UInt128PointerPointer, 8),
            _ => return Err(self.error("only scalar array parameters are supported")),
        };
        let declared_bytes = length.and_then(|length| length.checked_mul(element_width));
        Ok(ParsedParameter {
            parameter: FunctionParameter {
                click_type: ClickType::Program(pointer_type),
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
        match self.parse_viewable_proposition()? {
            ClickProposition::Loadable { segment } => Ok(Requirement::LoadableSegment { segment }),
            proposition => {
                self.expect(Token::Semicolon)?;
                Ok(Requirement::Proposition(proposition))
            }
        }
    }

    fn parse_viewable_proposition(&mut self) -> Result<ClickProposition, ClickError> {
        let saved = self.position;
        self.expect_ident_spelling("viewable")?;
        self.expect(Token::LParen)?;
        if let Ok(resource) = self.parse_resource_subject()
            && self.peek() == Some(&Token::RParen)
        {
            self.position += 1;
            return Ok(ClickProposition::ResourceViewable { resource });
        }
        self.position = saved;
        Ok(ClickProposition::Loadable {
            segment: self.parse_loadable_segment()?,
        })
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
        let mut left = self.parse_resource_subject_atom()?;
        let mut operands = 1;
        while self.peek() == Some(&Token::Star) {
            self.check_expression_chain_limit(operands)?;
            operands += 1;
            self.position += 1;
            left = ResourceSubject::Star(
                Box::new(left),
                Box::new(self.parse_resource_subject_atom()?),
            );
        }
        Ok(left)
    }

    fn empty_resource_token_len(&self, position: usize) -> Option<usize> {
        let mut start = position;
        if self.tokens.get(start) == Some(&Token::Ident("click".into()))
            && self.tokens.get(start + 1) == Some(&Token::ColonColon)
        {
            start += 2;
        }
        (self.tokens.get(start) == Some(&Token::Ident("separation".into()))
            && self.tokens.get(start + 1) == Some(&Token::ColonColon)
            && self.tokens.get(start + 2) == Some(&Token::Ident("emp".into())))
        .then_some(start + 3 - position)
    }

    fn parse_resource_subject_atom(&mut self) -> Result<ResourceSubject, ClickError> {
        if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            let resource = self.parse_resource_subject()?;
            self.expect(Token::RParen)?;
            return Ok(resource);
        }
        if let Some(length) = self.empty_resource_token_len(self.position) {
            self.position += length;
            return Ok(ResourceSubject::Emp);
        }
        if let Some(name) = self.peek_ident()
            && self.peek_next() != Some(&Token::LParen)
            && let Some((identity, _)) = self.names.resource_bindings.get(name)
        {
            let subject = ResourceSubject::Instance {
                name: name.to_string(),
                identity: *identity,
                at: None,
            };
            self.position += 1;
            return Ok(subject);
        }
        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let selector = self.parse_program_point_selector()?;
            self.expect(Token::Comma)?;
            let resource = self.parse_resource_subject()?;
            self.expect(Token::RParen)?;
            let mut names = BTreeSet::new();
            collect_current_resource_subject_variables(&resource, &mut names);
            self.refuse_result_in_program_point(Some(&selector), names.contains("result"))?;
            return Ok(ResourceSubject::At {
                selector,
                resource: Box::new(resource),
            });
        }
        if let Some(name) = self.peek_ident()
            && let Some(index) = self.resource_parameters.get(name).copied()
        {
            let name = name.to_string();
            self.position += 1;
            return Ok(ResourceSubject::Parameter { name, index });
        }
        if self.peek_ident() == Some("memory") && self.peek_next() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::LParen)?;
            if matches!(self.peek_ident(), Some("at" | "old"))
                && self.peek_next() == Some(&Token::LParen)
            {
                let base = self.parse_contract_primary()?;
                self.expect(Token::LBracket)?;
                let start = self.parse_contract_expression()?;
                let end = if self.peek() == Some(&Token::DotDot) {
                    self.position += 1;
                    Some(self.parse_contract_expression()?)
                } else {
                    None
                };
                self.expect(Token::RBracket)?;
                self.expect(Token::RParen)?;
                return Ok(ResourceSubject::SavedMemory { base, start, end });
            }
            let segment = self.parse_current_contract_segment()?;
            self.expect(Token::RParen)?;
            return Ok(ResourceSubject::Memory(segment));
        }

        let saved = self.position;
        if let Ok(region) = self.parse_code_region_ref()
            && self.peek() == Some(&Token::Dot)
            && self.peek_next() == Some(&Token::Ident("footprint".into()))
        {
            self.position += 2;
            return Ok(ResourceSubject::Footprint(region));
        }
        self.position = saved;
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
        if self.peek_ident() == Some("uninitialized") && self.peek_next() == Some(&Token::LParen) {
            return self.parse_uninitialized_memory_target(access);
        }
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

    /// `uninitialized(p[a..b])`: memory held with no claim that its bytes
    /// are initialized. A viewed range is read, so it is always initialized.
    fn parse_uninitialized_memory_target(
        &mut self,
        access: ResourceAccessMode,
    ) -> Result<ResourceClause, ClickError> {
        if access == ResourceAccessMode::View {
            return Err(self.error(
                "a viewed range is read, so its bytes are initialized: write `views p[a..b]`; `uninitialized(p[a..b])` is for owned memory",
            ));
        }
        if !self.uninitialized_memory_allowed {
            return Err(self.error(
                "`uninitialized(p[a..b])` is accepted only in a function contract's `owns`, `consumes`, or `produces` clause",
            ));
        }
        self.position += 2;
        self.uninitialized_memory_allowed = false;
        let segments = self.parse_current_contract_segments_inner(true);
        self.uninitialized_memory_allowed = true;
        let segments = segments?
            .into_iter()
            .map(ContractSegment::into_uninitialized)
            .collect::<Vec<_>>();
        self.expect(Token::RParen)?;
        if segments.len() > 1 {
            return Ok(ResourceClause::MemoryAggregate { access, segments });
        }
        Ok(ResourceClause::OwnMemory(
            segments
                .into_iter()
                .next()
                .expect("resource target parser returns at least one segment"),
        ))
    }

    /// A `step(` argument that opens the chunk-5 call form: an identifier, a
    /// parenthesized argument list, and a comma introducing the binder map.
    /// The closing parenthesis comes from the precomputed nesting table, so
    /// the decision costs one lookup rather than a scan.
    /// Whether `step(Name, { ... })` follows: a contract or function name, a
    /// C++ or Rust path `a::b` and a Rust instance's type arguments `<u32>`
    /// included, then the comma before the map.
    fn named_step_follows(&self) -> bool {
        let mut at = self.position;
        if !matches!(self.tokens.get(at), Some(Token::Ident(_))) {
            return false;
        }
        at += 1;
        while self.tokens.get(at) == Some(&Token::ColonColon)
            && matches!(self.tokens.get(at + 1), Some(Token::Ident(_)))
        {
            at += 2;
        }
        if self.tokens.get(at) == Some(&Token::LessThan) {
            while !matches!(self.tokens.get(at), Some(Token::GreaterThan) | None) {
                at += 1;
            }
            at += 1;
        }
        self.tokens.get(at) == Some(&Token::Comma)
    }

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
        // field map is: a call step writes `step(callee, { ... })` and a
        // tactic application writes `name(..., { ... })`, where the map is
        // optional when the tactic supplies no binder.
        let form = if tactic { "name(...)" } else { "step(...)" };
        // `step(Name, { ... })` names a named contract or a C function by
        // its contract; the call's arguments come from the call at the
        // frontier, which the step is checked against when it runs.
        let name_only = !tactic && self.peek() == Some(&Token::Comma);
        let named_contract = name_only && self.contract_resource_binders.contains_key(&callee);
        let named_function = name_only && !named_contract;
        if !tactic && !name_only {
            return Err(self.error(format!(
                "`step({callee}(...), {{ ... }})` is retired: write `step({callee}, {{ ... }})`; the call's arguments come from the call at the frontier"
            )));
        }
        if !name_only {
            self.expect(Token::LParen)?;
        }
        let mut arguments = Vec::new();
        let mut has_map = !tactic;
        while !name_only && self.peek() != Some(&Token::RParen) {
            if self.peek() == Some(&Token::LBrace) {
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
            declared = self.library_callee_value_parameters(&callee)?;
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
                // A `let` value parameter takes a value.
                let argument = self.parse_contract_expression()?;
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
            // `step(snprintf, { ... })` names the formatted-output function
            // without its format, so the `%s` lengths `nN` it takes are
            // checked against the call's format when the step runs.
            if named_function && callee == "snprintf" && !declared.contains_key(&binder) {
                if !bound.insert(binder.clone()) {
                    return Err(self.error(format!("duplicate binder `{binder}` in the call map")));
                }
                value_arguments.push((binder, self.parse_contract_expression()?));
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
                call_arguments: Vec::new(),
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
                    // A step that names its function takes the call's
                    // arguments from the frontier: the produced instance's
                    // resource arguments are the values it binds as
                    // `name.parameter` when it runs.
                    let argument_names = if named_function {
                        declaration
                            .parameter_names
                            .iter()
                            .map(|parameter| format!("{name}.{parameter}"))
                            .collect::<Vec<_>>()
                    } else {
                        Vec::new()
                    };
                    let call_arguments = if named_function {
                        argument_names
                            .iter()
                            .map(|argument| ContractExpression::Binding(argument.clone()))
                            .collect()
                    } else {
                        arguments.clone()
                    };
                    let mut binding = self.bind_produced_call_instance(
                        &name,
                        &binder,
                        declaration,
                        &call_arguments,
                    )?;
                    binding.call_arguments = argument_names;
                    produced.push(binding);
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
            // A named function's arguments are the frontier call's.
            frontier: named_function,
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
        let target = substitute_resource_clause_bindings(resource, &substitutions.into())
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
            call_arguments: Vec::new(),
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
                        arguments: vec![ContractExpression::ProgramExpression(
                            ProgramExpression::Variable(("mutex".to_string()).into()),
                        )],
                        parameter_types: vec![InterfaceType::VoidPointer],
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

    /// The value parameters of the C library function `callee`, such as
    /// `strlen`'s `n`, for a call map in a program's sidecar. The library's
    /// declarations are parsed apart from the sidecar, so its parameters are
    /// not in the sidecar's registry. A library module itself never asks:
    /// the library is not loaded while it is being parsed.
    fn library_callee_value_parameters(
        &self,
        callee: &str,
    ) -> Result<BTreeMap<String, CalleeResourceBinder>, ClickError> {
        if self.library_module
            || crate::languages::c::syntax::library_contract_module_named(callee).is_none()
        {
            return Ok(BTreeMap::new());
        }
        crate::instrumentation::record_deterministic_work(1);
        Ok(
            super::validation::library_program_function_value_parameters(callee)?
                .into_iter()
                .map(|name| (name, Self::value_parameter_callee_binder()))
                .collect(),
        )
    }

    /// A callee's value parameter, `let n: uint64;`, as its callers' call maps
    /// name it: the map gives its value.
    fn value_parameter_callee_binder() -> CalleeResourceBinder {
        CalleeResourceBinder {
            identity: Variable(0),
            family: None,
            resource: None,
            parameter_names: Vec::new(),
            kind: CalleeResourceBinderKind::Value,
        }
    }

    /// Whether a retired value binder follows: `name: R(...)` where the
    /// clause is a `views` clause, or one of `R`'s arguments is `_`. An
    /// `owns` or `consumes` binder without `_` names an instance.
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

    /// The refusal of a value binder, `owns s: R(a, _)` or `views s: R(a)`:
    /// a contract declares a value its clauses take as `let n: T;`.
    fn value_binder_refusal(&self, view: bool) -> ClickError {
        if view {
            self.error(
                "a `views` clause is not named; declare each value it fixes as `let n: type;` and write `views resource(..., n);`",
            )
        } else {
            self.error(
                "`_` leaves a resource argument open only in a count pattern; declare the value as `let n: type;` and write `resource(..., n)`",
            )
        }
    }

    /// Records an instance binder in the selected function/interface registry.
    /// Call maps name those declarations, including produced identities.
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

    /// A function contract's `owns`, `consumes`, or `produces` target, which
    /// may be `uninitialized(p[a..b])`.
    fn parse_function_contract_memory_binding(&mut self) -> Result<ResourceClause, ClickError> {
        self.uninitialized_memory_allowed = true;
        let resource = self.parse_owned_resource_binding();
        self.uninitialized_memory_allowed = false;
        resource
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
        self.names.resource_targets.hidden(resource).cloned()
    }

    /// A resource whose every field is retained from children may be held
    /// without an explicit binder: `owns pair(p);`. Its internal instance
    /// name is unwritable; field paths use the resource call. Naming
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

    /// An application (or an `at` around one) followed by an index.
    fn indexed_resource_target_follows(&self) -> bool {
        self.peek_ident().is_some()
            && self.peek_next() == Some(&Token::LParen)
            && self.matching_parentheses[self.position + 1]
                .is_some_and(|close| self.tokens.get(close + 1) == Some(&Token::LBracket))
    }

    fn parse_iterated_slot(&mut self) -> Result<Box<IteratedSlot>, ClickError> {
        let point = if self.peek_ident() == Some("at") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let point = self.parse_program_point_selector()?;
            self.expect(Token::Comma)?;
            Some(point)
        } else {
            None
        };
        let resource = self.parse_declared_resource_call_with_access(ResourceAccessMode::Own)?;
        if point.is_some() {
            self.expect(Token::RParen)?;
        }
        self.expect(Token::LBracket)?;
        let index = self.parse_contract_expression()?;
        self.expect(Token::RBracket)?;
        self.expect(Token::RParen)?;
        Ok(Box::new(IteratedSlot {
            resource,
            point,
            index,
        }))
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
            let ClickType::Program(interface_type) = click_type else {
                return Err(self.error(
                    "`let ... where` quantifies a C value; algebraic quantifiers are not supported yet",
                ));
            };
            let body = self.parse_proposition()?;
            return Ok(ClickProposition::Exists {
                click_type: ClickType::Program(interface_type),
                name: binding.name.into(),
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
            let proposition_at_program_point =
                self.parse_program_point_selector().and_then(|selector| {
                    self.expect(Token::Comma)?;
                    let proposition = self.parse_proposition()?;
                    self.expect(Token::RParen)?;
                    Ok(ClickProposition::At {
                        selector,
                        proposition: Box::new(proposition),
                    })
                });
            if proposition_at_program_point.is_ok()
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
                }) = &proposition_at_program_point
                {
                    self.refuse_result_in_program_point_proposition(selector, proposition)?;
                }
                return proposition_at_program_point;
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
            return self.parse_viewable_proposition();
        }

        if self.peek_ident() == Some("aligned") && self.peek_next() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::LParen)?;
            let pointer = self.parse_contract_expression()?;
            let Some(pointer) = contract_expression_as_program_expression(&pointer) else {
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

        if self.peek_ident().is_some_and(|name| {
            self.names.contains(NameKind::ContractBinding, name)
                || matches!(
                    self.specification_binding_kind(name),
                    Some(spec_arithmetic::SpecificationBinding::Function { .. })
                )
        }) && self.peek_next() == Some(&Token::LParen)
        {
            return self.parse_proposition_comparison();
        }

        if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_ident() != Some("old")
            && self.peek_ident() != Some("at")
            && !(self.peek_ident() == Some("program")
                && self.peek_next() == Some(&Token::ColonColon))
            // The earlier `c(name)` / `rust(name)` forms reach their refusal.
            && self.peek_ident() != Some("c")
            && self.peek_ident() != Some("rust")
            && !(self.peek_ident() == Some("count")
                && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_)))
                && self.tokens.get(self.position + 3) == Some(&Token::LParen))
            && !matches!(
                self.peek_ident(),
                Some(
                    "address"
                        | "binder"
                        | "byte_offset"
                        | "sizeof"
                        | "float32_from_bits"
                        | "float64_from_bits"
                )
            )
            && typed_load_type_from_name(self.peek_ident()).is_none()
            && self.peek_next() == Some(&Token::LParen)
            && !self.looks_like_region_result()
        {
            if let Some(name) = self.peek_ident()
                && let Some(value_parameters) = self.contract_value_parameter_names.get(name)
                && !value_parameters.is_empty()
            {
                return self.parse_contract_value_application();
            }
            if let Some(kind) = self
                .peek_ident()
                .and_then(crate::kernel::TerminationAtomKind::from_spelling)
            {
                let name = self.expect_ident("termination predicate")?;
                self.expect(Token::LParen)?;
                let arguments = if kind == crate::kernel::TerminationAtomKind::Callbacks {
                    Vec::new()
                } else {
                    vec![ContractExpression::Binding(
                        self.expect_string("function name")?,
                    )]
                };
                self.expect(Token::RParen)?;
                return Ok(ClickProposition::PredicateCall { name, arguments });
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
                    | Token::Dot
                    | Token::LBracket,
                ) => {
                    self.position = start;
                    return self.parse_proposition_comparison();
                }
                _ if self.proposition_function_names.contains(&name) => {
                    return Ok(ClickProposition::Value(ContractExpression::Call {
                        name,
                        arguments,
                    }));
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
            name: SurfaceBinder,
            negations: usize,
            previous_integer_context: bool,
            /// Where the bindings this binder makes and hides start.
            names: NameScope,
            operand: spec_arithmetic::ShadowedLet,
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
                        let name = self.expect_surface_binder(if forall {
                            "forall variable name"
                        } else {
                            "exists variable name"
                        })?;
                        self.refuse_bool_literal_binder(&name)?;
                        if name.written().is_some_and(is_c_type_keyword) {
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
                        // the fact and resource instance of its name, and the
                        // field a resource body reads by it, until its body
                        // ends.
                        let names = self.names.scope();
                        self.names.hide_for_proof_binder(&name, false);
                        self.names.hide_resource_field(&name);
                        match &click_type {
                            ClickType::Resource => {
                                return Err(self.error(
                                    "Resource is currently supported only for theorem parameters",
                                ));
                            }
                            ClickType::Integer => {
                                self.names
                                    .set_scoped(NameKind::ContractBinding, &name, false);
                                self.names
                                    .set_scoped(NameKind::IntegerParameter, &name, true);
                                self.integer_literal_context = true;
                            }
                            ClickType::Program(_) | ClickType::CObjectPointer { .. } => {
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
                            ClickType::Proposition
                            | ClickType::Function { .. }
                            | ClickType::Parameter(_) => {
                                return Err(self.error(
                                    "quantifier type must be a concrete C, Integer, or algebraic type",
                                ));
                            }
                        }
                        let operand = self.bind_let_operand(&name, Some(&click_type), None);
                        self.quantifier_binders.push(name.clone());
                        scopes.push(Scope {
                            forall,
                            operand,
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
                    self.unbind_let_operands(vec![scope.operand]);
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
        // An untyped item binder is contextual sugar for a predicate lambda.
        // A typed literal or another expression is an ordinary predicate value.
        let untyped_binder = self.peek() == Some(&Token::Pipe)
            && matches!(self.peek_next(), Some(Token::Ident(_)))
            && self.tokens.get(self.position + 2) == Some(&Token::Pipe);
        if !untyped_binder {
            let predicate = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(lambdas::range_proposition(
                start,
                end,
                predicate,
                method == "all",
            ));
        }
        self.expect(Token::Pipe)?;
        let item = self.expect_surface_binder("range item name")?;
        self.expect(Token::Pipe)?;
        let binder_scope = self.loop_proof_value_names.clone();
        if let Some(name) = item.written() {
            self.loop_proof_value_names = self.loop_proof_value_names.with_value(name.to_owned());
        }
        let body = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            body
        } else {
            self.parse_proposition()?
        };
        self.expect(Token::RParen)?;

        self.loop_proof_value_names = binder_scope;
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
        let arguments = self.observe_integer_arguments(&name, arguments);
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
            let proposition_binding = match &left {
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::BindingName::Generated(id),
                )) => {
                    self.specification_binding_kind(id)
                        == Some(spec_arithmetic::SpecificationBinding::Proposition)
                }
                ContractExpression::Binding(name)
                | ContractExpression::ProgramBinding(name)
                | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::BindingName::Named(name),
                )) => {
                    self.specification_binding_kind(name)
                        == Some(spec_arithmetic::SpecificationBinding::Proposition)
                }
                _ => false,
            };
            if proposition_binding
                || crate::surface::bool_literal_value(&left).is_some()
                || matches!(&left, ContractExpression::Call { name, .. } if self.proposition_function_names.contains(name))
                || matches!(
                    left,
                    ContractExpression::Apply { .. }
                        | ContractExpression::Let { .. }
                        | ContractExpression::Proposition(_)
                )
            {
                return Ok(ClickProposition::Value(left));
            }
            return Ok(bool_truth(left));
        }
        let operator = self.parse_comparison_operator("proposition")?;
        let right = self.parse_comparison_operand()?;

        Ok(self.specification_comparison(left, operator, right))
    }

    /// Whether the function header whose parameter list opens at `start`
    /// declares `-> Integer`: the parenthesis is matched, then the result
    /// type follows the arrow.
    fn declares_slice_result(&self, start: usize) -> bool {
        if self.tokens.get(start) != Some(&Token::LParen) {
            return false;
        }
        let Some(close) = self.matching_parentheses.get(start).copied().flatten() else {
            return false;
        };
        let mut at = close + 2;
        if self.tokens.get(close + 1) != Some(&Token::Arrow)
            || self.tokens.get(at) != Some(&Token::Amp)
        {
            return false;
        }
        at += 1;
        if self.tokens.get(at) == Some(&Token::Ident("mut".into())) {
            at += 1;
        }
        self.tokens.get(at) == Some(&Token::LBracket)
    }

    /// Whether `expression` is a value of a Click type whose methods the
    /// parser cannot place, because its type is known only once types are
    /// inferred: a binder, a pure function's result, a constructed value, a
    /// method's result, or one of those at another point. A C object or a
    /// resource instance is not: the parser resolves its fields.
    fn is_click_valued_receiver(&self, expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Binding(name) => {
                !self.names.global_array_shapes.contains_key(name)
                    && !self.names.resource_bindings.contains_key(name)
            }
            ContractExpression::AlgebraicVariable { .. }
            | ContractExpression::AlgebraicConstructor { .. }
            | ContractExpression::MethodCall { .. }
            | ContractExpression::Call { .. } => true,
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.is_click_valued_receiver(inner),
            _ => false,
        }
    }

    /// `receiver[i]`, `receiver[a..b]`, `receiver[a..]`, `receiver[..b]` or
    /// `receiver[..]` as the method `[]` or a range method, with the written
    /// bounds as its arguments.
    fn parse_method_index(
        &mut self,
        receiver: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let range = self.contract_bracket_is_range();
        self.expect(Token::LBracket)?;
        let method_call = |method: &str, arguments| ContractExpression::MethodCall {
            receiver: Box::new(receiver),
            method: method.to_string(),
            arguments,
        };
        if !range {
            let index = self.parse_place_index()?;
            self.expect(Token::RBracket)?;
            return Ok(method_call("[]", vec![index]));
        }
        let start = (self.peek() != Some(&Token::DotDot))
            .then(|| self.parse_contract_expression())
            .transpose()?;
        self.expect(Token::DotDot)?;
        let end = (self.peek() != Some(&Token::RBracket))
            .then(|| self.parse_contract_expression())
            .transpose()?;
        self.expect(Token::RBracket)?;
        let literal = |bound: &Option<ContractExpression>| match bound {
            Some(ContractExpression::IntegerLiteral(text)) => text.parse::<u64>().ok(),
            Some(bound @ ContractExpression::ProgramExpression(ProgramExpression::Value(_))) => {
                crate::surface::diagnostics::describe_contract_expression(bound)
                    .strip_suffix("u64")?
                    .parse::<u64>()
                    .ok()
            }
            _ => None,
        };
        if let (Some(start), Some(end)) = (literal(&start), literal(&end))
            && start > end
        {
            return Err(self.error(format!(
                "the subslice `[{start}..{end}]` starts past its end; Rust panics on a reversed range"
            )));
        }
        Ok(match (start, end) {
            (None, None) => method_call("[..]", vec![]),
            (Some(start), None) => method_call("[a..]", vec![start]),
            (None, Some(end)) => method_call("[..b]", vec![end]),
            (Some(start), Some(end)) => method_call("[a..b]", vec![start, end]),
        })
    }

    /// A method call's parenthesized arguments.
    fn parse_method_arguments(&mut self) -> Result<Vec<ContractExpression>, ClickError> {
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                arguments.push(self.parse_contract_expression()?);
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
        Ok(arguments)
    }

    /// Whether `expression` is a slice value a Rust sidecar reads with
    /// Rust's slice methods: a call of a pure function whose result is a
    /// slice, or a `Slice` binder.
    fn is_rust_slice_value(&self, expression: &ContractExpression) -> bool {
        if !self.verifies_rust() {
            return false;
        }
        match expression {
            ContractExpression::Call { name, .. } => {
                self.slice_result_functions.contains(name) || is_slice_from_raw_parts(name)
            }
            ContractExpression::AlgebraicVariable { algebraic_type, .. }
            | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
                algebraic_type.name() == "Slice"
            }
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.is_rust_slice_value(inner),
            _ => false,
        }
    }

    /// The slice parameter `expression` names: `bytes`, or `bytes` at another
    /// point, `old(bytes)` or `at(point, bytes)`.
    fn rust_slice_parameter_read<'a>(&self, expression: &'a ContractExpression) -> Option<&'a str> {
        match expression {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(slice),
            )) if self.rust_slice_params.contains(slice) => Some(slice),
            _ => self.read_slice_parameter(expression),
        }
    }

    /// The slice value a slice parameter read stands for, `bytes` or
    /// `old(bytes)`: the constructor of its pointer, as written, and its
    /// length, which a parameter never changes, at its element type.
    fn slice_parameter_value(&self, expression: &ContractExpression) -> Option<ContractExpression> {
        let parameter = self.rust_slice_parameter_read(expression)?;
        let element = *self.rust_slice_elements.get(parameter)?;
        Some(ContractExpression::AlgebraicConstructor {
            algebraic_type: AlgebraicTypeApplication {
                rigid: false,
                name: "Slice".to_string(),
                arguments: vec![ClickType::Program(element)],
            },
            variant: "Slice".to_string(),
            arguments: vec![
                expression.clone(),
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    format!("{parameter}_len").into(),
                )),
            ],
        })
    }

    fn declares_integer_result(&self, start: usize) -> bool {
        self.declares_named_result(start, "Integer")
    }

    fn declares_named_result(&self, start: usize, result: &str) -> bool {
        if self.tokens.get(start) != Some(&Token::LParen) {
            return false;
        }
        let Some(close) = self.matching_parentheses.get(start).copied().flatten() else {
            return false;
        };
        self.tokens.get(close + 1) == Some(&Token::Arrow)
            && matches!(self.tokens.get(close + 2), Some(Token::Ident(name)) if name == result)
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
        let value_scope = self.loop_proof_value_names.clone();
        let result = self.parse_by_clause_body();
        self.names.end(scope);
        self.names
            .replace(NameKind::ProofBinder, previous_proof_let_names);
        self.loop_proof_value_names = value_scope;
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
        if self.resource_parameters.contains_key(name) {
            return Err(self.error(format!(
                "`{name}` names a Resource theorem parameter; choose another proof binder name"
            )));
        }
        if resource
            && self.names.is_program_variable(name)
            && self.names.resource_bindings.contains_key(name)
        {
            return Err(self.error(format!(
                "`{name}` names both a C variable and the contract's resource instance `{name}`; a proof binder cannot hide the C variable, so the instance cannot be bound again under this name; rename the instance in the contract"
            )));
        }
        if self.names.is_program_variable(name) {
            return Err(self.error(format!(
                "`{name}` names a C variable here; a proof binder cannot hide it, since execution keeps reading the program's `{name}`; choose another name"
            )));
        }
        self.names.hide_for_proof_binder(name, resource);
        self.loop_proof_value_names = self.loop_proof_value_names.with_value(name.to_string());
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
            // A removed spelling is refused with its replacement.
            Some(name) if removed_tactic_refusal(name).is_some() => true,
            // Route a bare `solve` through the missing-parentheses diagnostic.
            Some("solve") => self.peek_next() != Some(&Token::LParen),
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

        // `solve()` uses whole-proof automation. Other single calls are one-step scripts.
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

    fn remember_loop_goal_binders(&mut self, proposition: &ClickProposition) {
        if self.loop_name_context.is_none() {
            return;
        }
        let mut pending = vec![proposition];
        let mut predicates = BTreeSet::new();
        while let Some(proposition) = pending.pop() {
            match proposition {
                ClickProposition::PredicateCall { name, .. } => {
                    if predicates.insert(name)
                        && let Some(body) = self.loop_predicate_bodies.get(name)
                    {
                        pending.push(body);
                    }
                }
                ClickProposition::ForAll {
                    name,
                    written_name,
                    body,
                    ..
                }
                | ClickProposition::Exists {
                    name,
                    written_name,
                    body,
                    ..
                } => {
                    self.loop_proof_value_names = self
                        .loop_proof_value_names
                        .with_value(written_name.clone().unwrap_or_else(|| name.to_string()));
                    pending.push(body);
                }
                ClickProposition::RangeAll {
                    item,
                    written_item,
                    body,
                    ..
                }
                | ClickProposition::RangeAny {
                    item,
                    written_item,
                    body,
                    ..
                } => {
                    self.loop_proof_value_names = self
                        .loop_proof_value_names
                        .with_value(written_item.clone().unwrap_or_else(|| item.to_string()));
                    pending.push(body);
                }
                ClickProposition::And(left, right)
                | ClickProposition::Or(left, right)
                | ClickProposition::Implies(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                ClickProposition::Not(body) => pending.push(body),
                ClickProposition::At { proposition, .. } => pending.push(proposition),
                _ => {}
            }
        }
    }

    fn parse_loop_phase_proof(
        &mut self,
        items: &[StructuralItem],
    ) -> Result<SourceProof, ClickError> {
        let binder_scope = self.loop_proof_value_names.clone();
        for item in items {
            self.remember_loop_goal_binders(&item.claim);
        }
        let proof = self.parse_by_clause();
        self.loop_proof_value_names = binder_scope;
        let proof = proof?;
        // A lone phase `solve()` owns the generated execution and closure steps,
        // with either brace spelling. Keep it out of per-step source capture.
        if matches!(&proof, SourceProof::Script(tactics) if matches!(tactics.as_slice(), [ProofTactic::Solve]))
        {
            Ok(SourceProof::Tactic(SmartTactic::Solve))
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
            if self.names.contains(NameKind::ContractBinding, &name)
                || matches!(
                    self.specification_binding_kind(&name),
                    Some(spec_arithmetic::SpecificationBinding::Function { .. })
                )
            {
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
                        field.name == slot && matches!(field.click_type, ClickType::Program(_))
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
                self.names.set_child_instance_target(
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
            _ => self.parse_other_proof_tactic(name),
        }
    }

    // `let ... = fold(...)` has a large parsing frame. Keep it out of the
    // common tactic dispatcher so nested proof bodies fit the bounded stack.
    #[inline(never)]
    fn parse_let_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        // Generated logical identities are valid intro outputs, while
        // resource and call output patterns retain their written names.
        if self.peek_ident() == Some("binder") && self.peek_next() == Some(&Token::LParen) {
            let binder = self.expect_surface_binder("introduced variable")?;
            self.expect(Token::Equal)?;
            self.expect_ident_spelling("intro")?;
            if self.tactic_names.contains("intro") {
                return Err(self.error("generated binder outputs require the built-in `intro`"));
            }
            self.expect_empty_tactic_args("intro")?;
            self.expect(Token::Semicolon)?;
            return self.named_intro(binder);
        }
        if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            let mut names = vec![self.expect_ident("existential witness name")?];
            self.expect(Token::Comma)?;
            loop {
                names.push(self.expect_ident("existential witness name")?);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::RParen)?;
            self.expect(Token::Equal)?;
            self.expect_ident_spelling("obtain")?;
            return self.parse_obtain(names);
        }
        let output = self.parse_let_output_pattern()?;
        self.expect(Token::Equal)?;
        if self.peek_ident() == Some("obtain") && !self.tactic_names.contains("obtain") {
            self.position += 1;
            let CallOutputPattern::Single(name) = output else {
                return Err(self.error("use positional witness names on the left of `obtain`"));
            };
            return self.parse_obtain(vec![name]);
        }
        if matches!(self.peek_ident(), Some("intro" | "induct"))
            && !self.tactic_names.contains(self.peek_ident().unwrap())
        {
            let tactic = self.expect_ident("binding-producing tactic")?;
            let CallOutputPattern::Single(name) = output else {
                return Err(self.error(format!(
                    "`{tactic}` produces one binding: write `let name = {tactic}(...);`"
                )));
            };
            if tactic == "intro" {
                self.expect_empty_tactic_args("intro")?;
                self.expect(Token::Semicolon)?;
                return self.named_intro(name.into());
            }
            self.refuse_cast_type_binder(&name)?;
            self.expect(Token::LParen)?;
            let parameter = self.expect_ident("induction parameter")?;
            self.expect(Token::RParen)?;
            self.expect(Token::Semicolon)?;
            return Ok(ProofTactic::Induct {
                parameter,
                hypothesis: name,
            });
        }
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
            if self.peek() == Some(&Token::LBrace) {
                return Err(self.error(
                    "`step({ ... })` is retired: name the function or contract the map fills in, `step(callee, { ... })`",
                ));
            }
            if !self.call_binder_transport_follows() && !self.named_step_follows() {
                return Err(self.error(
                            "a call output binding requires a binder map: `let { result: name } = step(callee, { binder: instance })`",
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
            return self.parse_step_proof(ProofTactic::UserTactic(application));
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
        if self.names.contains_any(NameKind::VALUES, &name)
            || self.specification_binding_kind(&name).is_some()
        {
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
        // A resource whose every field is retained from children has no
        // declared field initializer, so its one brace is the child map; a map whose
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
                // An `Integer` field's value is read where an Integer is
                // expected.
                let value = if declared.iter().any(|declared| {
                    declared.name() == field && declared.click_type() == &ClickType::Integer
                }) {
                    self.at_integer_position(value)
                } else {
                    value
                };
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

    /// Parse the source before adding any of the output names to scope.
    #[inline(never)]
    fn parse_obtain(&mut self, names: Vec<String>) -> Result<ProofTactic, ClickError> {
        self.expect(Token::LParen)?;
        let proposition = self.parse_proposition()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Semicolon)?;
        let mut source = match &proposition {
            ClickProposition::At { proposition, .. } => proposition.as_ref(),
            proposition => proposition,
        };
        let mut bindings = Vec::with_capacity(names.len());
        let previous_integer_context = self.integer_literal_context;
        for name in names {
            let ClickProposition::Exists {
                click_type, body, ..
            } = source
            else {
                return Err(self.error(
                    "`obtain` needs an existential proposition with at least one binder per output",
                ));
            };
            self.refuse_cast_type_binder(&name)?;
            if self.names.contains(NameKind::ProofBinder, &name) {
                return Err(self.error(format!("`{name}` is already in scope")));
            }
            self.bind_proof_name(&name, false)?;
            let integer = *click_type == ClickType::Integer;
            self.names
                .set_scoped(NameKind::ContractBinding, &name, !integer);
            self.names.set_scoped(NameKind::IntegerLet, &name, integer);
            self.names.insert(NameKind::ProofBinder, name.clone());
            bindings.push((name, click_type.clone()));
            source = body;
        }
        self.integer_literal_context = previous_integer_context;
        Ok(ProofTactic::LetSatisfy(ProofLetSatisfy {
            bindings,
            proposition,
        }))
    }

    #[inline(never)]
    fn parse_both_proof_tactic(&mut self) -> Result<ProofTactic, ClickError> {
        // The first-written blocks that hold only a nested `both`,
        // outermost first. Keep this descent iterative for deep proofs.
        let mut nested_blocks = Vec::new();
        let mut first_is_left;
        let mut first_tactics = loop {
            let nested_both = nested_blocks.len();
            if nested_both > 0 && self.proof_nesting + nested_both >= STRUCTURAL_NESTING_LIMIT {
                return Err(self.error(format!(
                    "structural proof nesting exceeds Click's supported depth of {STRUCTURAL_NESTING_LIMIT}"
                )));
            }
            self.expect(Token::LBrace)?;
            first_is_left = match self.peek_ident() {
                Some("left") => true,
                Some("right") => false,
                _ => return Err(self.error("`both` expects a `left` or `right` arm")),
            };
            self.position += 1;
            self.expect(Token::FatArrow)?;
            self.expect(Token::LBrace)?;
            if self.peek_ident() == Some("both") {
                nested_blocks.push((
                    first_is_left,
                    self.positions[self.position - 1].clone(),
                    self.positions[self.position].clone(),
                ));
                self.position += 1;
            } else {
                break self.parse_tactics_until_rbrace()?;
            }
        };
        self.expect(Token::RBrace)?;

        loop {
            self.expect_ident_spelling(if first_is_left { "right" } else { "left" })?;
            self.expect(Token::FatArrow)?;
            let second_tactics = self.parse_possibly_empty_tactic_block()?;
            self.expect(Token::RBrace)?;
            self.skip_redundant_semicolon();
            let (left_tactics, right_tactics) = if first_is_left {
                (first_tactics, second_tactics)
            } else {
                (second_tactics, first_tactics)
            };
            let current = ProofTactic::Both(ProofBoth {
                left_tactics,
                right_tactics,
            });
            let Some((parent_first_is_left, open, start)) = nested_blocks.pop() else {
                return Ok(current);
            };
            self.record_proof_block(open, vec![start]);
            self.expect(Token::RBrace)?;
            first_is_left = parent_first_is_left;
            first_tactics = vec![current];
        }
    }

    /// `have P;`, `have P by solve();` or `have P by { ... }`, after the word
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
        // proof is `solve` here; it never executes C to reach the fact.
        if self.peek() == Some(&Token::Semicolon) {
            self.position += 1;
            return Ok(ProofTactic::Have(ProofHave {
                proposition,
                proof: have_proof_as_written_in_full(SourceProof::Tactic(SmartTactic::Solve)),
            }));
        }
        // `have P by solve();` proves the fact where it is stated: with no C
        // to run toward the fact, `solve` is `solve`.
        let binder_scope = self.loop_proof_value_names.clone();
        self.remember_loop_goal_binders(&proposition);
        let proof = self.parse_by_clause();
        self.loop_proof_value_names = binder_scope;
        let proof = proof?;
        self.skip_redundant_semicolon();
        // `have P;`, `have P by solve();` and `have P by { solve(); }` are
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
            if self.peek_ident() == Some("by") {
                return Err(self.error(
                    "`open` takes no trailing `by`; prove the closing fact with `have` inside the block",
                ));
            }
            self.skip_redundant_semicolon();
            return Ok(ProofTactic::Open(ProofOpen {
                resource,
                tactics,
                deferred_tail: false,
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
                let value_scope = self.loop_proof_value_names.clone();
                for binding in &bindings {
                    self.bind_proof_name(binding, false)?;
                }
                self.bind_arm_binding_types(&type_name, &variant, &bindings);
                let tactics = self.parse_possibly_empty_tactic_block();
                self.names.end(scope);
                self.names.arm_binding_types = saved_arm_binding_types;
                self.loop_proof_value_names = value_scope;
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
            let ensuring = self.parse_optional_join_interface()?;
            self.expect(Token::LBrace)?;
            let mut then_tactics = None;
            let mut else_tactics = None;
            while self.peek() != Some(&Token::RBrace) {
                let arm = self.expect_ident("`true` or `false`")?;
                let slot = match arm.as_str() {
                    "true" => &mut then_tactics,
                    "false" => &mut else_tactics,
                    _ => {
                        return Err(self
                            .error(format!("`branch` arms are `true` and `false`, got `{arm}`")));
                    }
                };
                if slot.is_some() {
                    return Err(self.error(format!("duplicate `branch` arm `{arm}`")));
                }
                self.expect(Token::FatArrow)?;
                *slot = Some(self.parse_possibly_empty_tactic_block()?);
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
            }
            self.expect(Token::RBrace)?;
            let (Some(then_tactics), Some(else_tactics)) = (then_tactics, else_tactics) else {
                return Err(self.error("`branch` needs both a `true` and a `false` arm"));
            };
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
            let mut payload_bindings = [None, None];
            while self.peek() != Some(&Token::RBrace) {
                let arm = self.expect_ident("`returned` or `threw`")?;
                let (index, slot) = match arm.as_str() {
                    "returned" => (0, &mut returned_tactics),
                    "threw" => (1, &mut threw_tactics),
                    _ => {
                        return Err(self.error(format!(
                            "`outcomes` arms are `returned` and `threw`, got `{arm}`"
                        )));
                    }
                };
                if slot.is_some() {
                    return Err(self.error(format!("duplicate `outcomes` arm `{arm}`")));
                }
                let binding = if self.peek() == Some(&Token::LParen) {
                    self.expect(Token::LParen)?;
                    let name = self.expect_ident("call payload name")?;
                    self.refuse_cast_type_binder(&name)?;
                    self.refuse_fact_name_in_scope(&name)?;
                    self.expect(Token::RParen)?;
                    Some(name)
                } else {
                    None
                };
                self.expect(Token::FatArrow)?;
                let scope = self.names.scope();
                let value_scope = self.loop_proof_value_names.clone();
                if let Some(name) = &binding {
                    self.bind_proof_name(name, false)?;
                    self.names.set_scoped(NameKind::ContractBinding, name, true);
                }
                let tactics = self.parse_possibly_empty_tactic_block();
                self.names.end(scope);
                self.loop_proof_value_names = value_scope;
                *slot = Some(tactics?);
                payload_bindings[index] = binding;
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
                payload_bindings,
                returned_tactics,
                threw_tactics,
            }));
        }
        if name == "loop" {
            let label = if self.peek_ident() == Some("as") {
                self.position += 1;
                let label = self.expect_ident("loop label")?;
                self.refuse_cast_type_binder(&label)?;
                Some(label)
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
            let enclosing_name_context = self.loop_name_context.take();
            // The loop's pass count, an Integer, is in scope in its clauses
            // and proofs, so a comparison with it reads its other side as an
            // Integer, as one with a population count does.
            // A program binding of that name is `program::iterations`.
            let iterations_was_bound = self.names.contains(
                NameKind::IntegerParameter,
                crate::surface::LOOP_ITERATIONS_NAME,
            );
            self.names.insert(
                NameKind::IntegerParameter,
                crate::surface::LOOP_ITERATIONS_NAME.to_string(),
            );
            self.loop_block_depth += 1;
            while self.peek() != Some(&Token::RBrace) {
                self.loop_name_context = Some(format!(
                    "loop {} clause",
                    self.peek_ident().unwrap_or("specification")
                ));
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
                    initialize_proof = Some(self.parse_loop_phase_proof(&items)?);
                    continue;
                }
                if self.peek_ident() == Some("preserve") {
                    self.proof_clause_owner = self.here();
                    self.position += 1;
                    if preserve_proof.is_some() {
                        return Err(self.error("duplicate `preserve` proof"));
                    }
                    preserve_proof = Some(self.parse_loop_phase_proof(&items)?);
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
            self.loop_name_context = enclosing_name_context;
            self.loop_block_depth -= 1;
            if !iterations_was_bound {
                self.names.remove(
                    NameKind::IntegerParameter,
                    crate::surface::LOOP_ITERATIONS_NAME,
                );
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
                    scope: BinderMap::new(),
                },
            )));
        }
        self.parse_named_proof_tactic(name)
    }

    fn named_intro(&mut self, name: SurfaceBinder) -> Result<ProofTactic, ClickError> {
        if let Some(name) = name.written() {
            self.refuse_cast_type_binder(name)?;
        }
        self.names.hide_for_proof_binder(&name, false);
        if let Some(name) = name.written() {
            self.names.ended_fact_names.remove(name);
        }
        Ok(match name {
            SurfaceBinder::Written(name) => ProofTactic::IntroAs(name),
            name => ProofTactic::IntroBinder(name),
        })
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
            return self.parse_step_proof(ProofTactic::UserTactic(application));
        }
        let tactic = match name.as_str() {
            "step" => {
                self.expect(Token::LParen)?;
                let step = if self.peek() == Some(&Token::RParen) {
                    ProofTactic::Step
                } else if self.peek() == Some(&Token::LBrace) {
                    return Err(self.error(
                    "`step({ ... })` is retired: name the function or contract the map fills in, `step(callee, { ... })`",
                ));
                } else if self.call_binder_transport_follows() || self.named_step_follows() {
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
                return Err(self.error(RETIRED_CLOSE_INVARIANTS));
            }
            "step_until" => {
                self.expect(Token::LParen)?;
                let region_ref = if self.peek_ident() == Some("function")
                    && self.peek_next() == Some(&Token::Dot)
                    && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(kind)) if kind == "exit")
                {
                    self.position += 3;
                    CodeRegionRef::FunctionExit
                } else {
                    self.parse_code_region_ref()?
                };
                self.expect(Token::RParen)?;
                ProofTactic::ExecuteUntil(region_ref)
            }
            "unfold" => {
                self.expect(Token::LParen)?;
                if self.indexed_resource_target_follows() {
                    let slot = self.parse_iterated_slot()?;
                    self.expect(Token::Semicolon)?;
                    return Ok(ProofTactic::Iterated(IteratedTactic::UnfoldSlot(slot)));
                }
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
                } else if self.peek_ident().is_some_and(|name| {
                    self.contract_value_parameter_names
                        .get(name)
                        .is_some_and(|parameters| !parameters.is_empty())
                }) || matches!(
                    self.peek_ident(),
                    Some("at" | "forall" | "exists" | "prop")
                ) || self.peek() == Some(&Token::LParen)
                    || self
                        .peek_ident()
                        .is_some_and(|name| self.names.fact_names.contains_key(name))
                {
                    ProofTactic::UnfoldProposition(self.parse_proposition()?)
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
                    return Err(self.error("unfold requires an application, such as `unfold(p(x))`, or an owned resource"));
                };
                self.expect(Token::RParen)?;
                if self.peek_ident() == Some("using") {
                    return Err(self.error(
                        "`unfold` takes no `using` list; its guards are ordinary proof obligations",
                    ));
                }
                if self.peek_ident() == Some("as") {
                    return Err(self.error(
                        "`unfold` takes no `as` map; name the opened pieces on the left: `let { slot: name } = unfold(resource);`",
                    ));
                }
                tactic
            }
            "apply" => {
                self.expect(Token::LParen)?;
                // A call remains a theorem application. Other propositions,
                // including named facts and parenthesized implications, are facts.
                let start = self.position;
                let application = if self.peek_ident().is_some()
                    && self.peek_next() == Some(&Token::LParen)
                    && !matches!(self.peek_ident(), Some("at" | "old" | "forall" | "exists"))
                {
                    let application = self.parse_theorem_application()?;
                    if self.peek() == Some(&Token::RParen) {
                        Some(application)
                    } else {
                        self.position = start;
                        None
                    }
                } else {
                    None
                };
                if application.is_none() {
                    let fact = self.parse_proposition()?;
                    self.expect(Token::RParen)?;
                    if self.peek_ident() == Some("using") {
                        let premises = self.parse_exact_premises()?;
                        self.skip_redundant_semicolon();
                        return Ok(ProofTactic::ApplyFactUsing { fact, premises });
                    }
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::ApplyFact(fact));
                }
                let application = application.unwrap();
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
                if matches!(self.peek_ident(), Some("at" | "old"))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let base = self.parse_contract_primary()?;
                    self.expect(Token::LBracket)?;
                    let start = self.parse_contract_expression()?;
                    self.expect(Token::DotDot)?;
                    let end = self.parse_contract_expression()?;
                    self.expect(Token::RBracket)?;
                    self.expect(Token::RParen)?;
                    ProofTactic::ObserveSavedMemory { base, start, end }
                } else {
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
                        self.parse_resource_target(ResourceAccessMode::View)?
                    };
                    self.expect(Token::RParen)?;
                    ProofTactic::ObserveResource(resource)
                }
            }
            "witness" => {
                self.expect(Token::LParen)?;
                let mut values = Vec::new();
                while self.peek() != Some(&Token::RParen) {
                    values.push(self.parse_contract_expression()?);
                    if self.peek() != Some(&Token::Comma) {
                        break;
                    }
                    self.position += 1;
                }
                self.expect(Token::RParen)?;
                if values.is_empty() {
                    return Err(self.error("`witness` needs at least one value"));
                }
                ProofTactic::Witness(ProofWitness::new(values))
            }
            "obtain" => return Err(self.error("write `let name = obtain(exists (k: Type) { P });` to name an existential witness")) ,
            "check_termination_local" => {
                self.expect(Token::LParen)?;
                let function = self.expect_string("function name")?;
                self.expect(Token::RParen)?;
                ProofTactic::CheckTerminationLocal(function)
            }
            "check_termination_component" => {
                self.expect(Token::LParen)?;
                let function = self.expect_string("function name")?;
                self.expect(Token::Comma)?;
                let strict = match self.expect_ident("strict or normal")?.as_str() {
                    "strict" => true,
                    "normal" => false,
                    _ => return Err(self.error("expected `strict` or `normal`")),
                };
                self.expect(Token::RParen)?;
                ProofTactic::CheckTerminationComponent { function, strict }
            }
            "check_termination_callbacks" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::CheckTerminationCallbacks
            }
            "known" => {
                self.expect_empty_tactic_args(&name)?;
                ProofTactic::Known
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
            "normalize" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::NormalizeUsing(premises));
                }
                ProofTactic::Normalize
            }
            "preserve" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_resource_subject()?;
                self.expect(Token::Comma)?;
                let region = self.parse_code_region_ref()?;
                self.expect(Token::RParen)?;
                let separation = ClickProposition::Separate {
                    left: ResourceSubject::Footprint(region),
                    right: resource,
                };
                ProofTactic::Preserve(separation)
            }
            "intro" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("as") {
                    return Err(self.error("`intro() as name` is now `let name = intro();`"));
                }
                ProofTactic::Intro
            }
            "split" | "left" | "right" => {
                return Err(self.error(format!(
                    "`{name}()` is now `known()`, which closes a conjunction whose sides are facts and a disjunction with one side a fact"
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
                let left = self.parse_contract_expression()?;
                if self.peek() == Some(&Token::EqualEqual) {
                    return Err(self.error("`rewrite` takes two expressions: write `rewrite(x, y)`, not `rewrite(x == y)`"));
                }
                self.expect(Token::Comma)?;
                let right = self.parse_contract_expression()?;
                self.expect(Token::RParen)?;
                ProofTactic::Rewrite(self.specification_comparison(
                    left,
                    ComparisonOperator::Equal,
                    right,
                ))
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
                if self.peek_ident() == Some("using") {
                    return Err(self.error("`instantiate` takes no `using` list; prove guards with ordinary `have` steps"));
                }
                ProofTactic::Instantiate {
                    quantified,
                    argument,
                }
            }
            "solve" => {
                self.expect_empty_tactic_args(&name)?;
                if self.peek_ident() == Some("using") {
                    let premises = self.parse_exact_premises()?;
                    self.skip_redundant_semicolon();
                    return Ok(ProofTactic::SolveUsing(ProofSolveUsing { premises }));
                }
                ProofTactic::Solve
            }
            "fold" => {
                self.expect(Token::LParen)?;
                if self.indexed_resource_target_follows() {
                    let slot = self.parse_iterated_slot()?;
                    self.expect(Token::Semicolon)?;
                    return Ok(ProofTactic::Iterated(IteratedTactic::FoldSlot(slot)));
                }
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
            "induct" => return Err(self.error("induction uses `let ih = induct(value);`; follow structural induction with `match value { ... }`")),
            _ if let Some(refusal) = removed_tactic_refusal(&name) => {
                return Err(self.error(refusal));
            }
            _ => return Err(self.error(format!("unknown tactic `{name}`"))),
        };
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    /// A proof `if` uses `then` when an interface precedes its arms.
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
                let scope = self.names.scope();
                let names = self.names.take(NameKind::ProofBinder);
                let value_scope = self.loop_proof_value_names.clone();
                scopes.push((scope, names, value_scope));
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
                let (scope, names, value_scope) = scopes.pop().expect("an else block owns a scope");
                self.names.end(scope);
                self.names.replace(NameKind::ProofBinder, names);
                self.loop_proof_value_names = value_scope;
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
        while let Some((scope, names, value_scope)) = scopes.pop() {
            self.names.end(scope);
            self.names.replace(NameKind::ProofBinder, names);
            self.loop_proof_value_names = value_scope;
        }
        result
    }

    /// What follows a `step(...)` head: `;`, `by` and the proof of its one
    /// open obligation, or a block of `requires P by ...` entries.
    #[inline(never)]
    fn parse_step_proof(&mut self, step: ProofTactic) -> Result<ProofTactic, ClickError> {
        let tactic = if matches!(step, ProofTactic::FoldResource(_)) {
            "fold"
        } else {
            "step"
        };
        if self.peek_ident() == Some("by") {
            self.position += 1;
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
        let value_scope = self.loop_proof_value_names.clone();
        let result = self.parse_tactic_list_to_rbrace();
        self.names.end(scope);
        self.names
            .replace(NameKind::ProofBinder, previous_proof_let_names);
        self.loop_proof_value_names = value_scope;
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
            matches!(argument, ContractExpression::ProgramExpression(ProgramExpression::Variable(crate::kernel::BindingName::Named(name))) | ContractExpression::Binding(name)
                if self.names.resource_bindings.contains_key(name))
                || matches!(argument, ContractExpression::Resource(subject)
                    if matches!(subject.as_ref(), ResourceSubject::Instance { .. }))
        });
        if let Some(first) = first_reference {
            for argument in arguments.drain(first..) {
                let reference = match argument {
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) => {
                        name.named()
                            .ok_or_else(|| self.error("resource arguments must name instances"))?
                            .to_owned()
                    }
                    ContractExpression::Binding(name) => name,
                    ContractExpression::Resource(subject) => match *subject {
                        ResourceSubject::Instance { name, .. } => name,
                        _ => return Err(self.error("resource arguments must name instances")),
                    },
                    _ => {
                        return Err(self.error(
                            "resource arguments must be named resources after ordinary arguments",
                        ));
                    }
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

    /// Whether `.step(` continues a path through the statements as written,
    /// for one of `steps`, rather than `.entry` or `.exit` ending it.
    fn chained_region_follows(&self, steps: &[&str]) -> bool {
        self.peek() == Some(&Token::Dot)
            && matches!(
                self.peek_next(),
                Some(Token::Ident(step)) if steps.contains(&step.as_str())
            )
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
    }

    fn source_path_step_follows(&self) -> bool {
        self.chained_region_follows(&[
            "statement",
            "region",
            "call",
            "test",
            "assignment",
            "read",
            "and",
            "or",
            "ternary",
        ])
    }

    /// Refuses a reference parameter as an assignment's local: binding a
    /// reference is not an assignment to it.
    fn expect_assignment_local(&mut self) -> Result<String, ClickError> {
        let local = self.expect_ident("assignment local")?;
        if self.names.contains(NameKind::ReferenceParameter, &local) {
            return Err(self.error(format!(
                "`{local}` is a reference, and binding a reference is not an assignment; a store through `{local}` is a store to what it refers to, so select the statement itself with `region(N)`"
            )));
        }
        Ok(local)
    }

    /// The rest of a path through the statements as written, after its first
    /// step: `.statement(j)` any number of times, then optionally one
    /// `.region(j)`, `.call(f, j)`, `.assignment(x, j)` or `.read(j)`, which
    /// ends it.
    fn parse_source_path(
        &mut self,
        mut steps: Vec<SourcePathStep>,
    ) -> Result<CodeRegionRef, ClickError> {
        while self.source_path_step_follows() {
            self.expect(Token::Dot)?;
            let step = self.expect_ident("region in a chain")?;
            self.expect(Token::LParen)?;
            match step.as_str() {
                "statement" => {
                    let index = self.expect_index("statement index")?;
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::Statement(index));
                }
                "region" => {
                    let index = self.expect_index("region index")?;
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::Region(index));
                    break;
                }
                "assignment" => {
                    let local = self.expect_assignment_local()?;
                    self.expect(Token::Comma)?;
                    let index = self.expect_index("assignment occurrence")?;
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::Assignment(local, index));
                    break;
                }
                "read" => {
                    let index = self.expect_index("read occurrence")?;
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::Read(index));
                    break;
                }
                "test" => {
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::Test);
                    break;
                }
                "and" | "or" | "ternary" => {
                    let kind = match step.as_str() {
                        "and" => crate::kernel::OperatorKind::And,
                        "or" => crate::kernel::OperatorKind::Or,
                        _ => crate::kernel::OperatorKind::Ternary,
                    };
                    let index = self.expect_index("operator occurrence")?;
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::Operator(kind, index));
                    break;
                }
                _ if matches!(self.peek(), Some(Token::Number(_))) => {
                    let index = self.expect_index("call index")?;
                    self.expect(Token::RParen)?;
                    steps.push(SourcePathStep::AnyCall(index));
                    break;
                }
                _ => {
                    steps.push(self.parse_call_step()?);
                    break;
                }
            }
        }
        if self.chained_region_follows(&["read_event"]) {
            self.expect(Token::Dot)?;
            self.expect_ident("read_event")?;
            self.expect(Token::LParen)?;
            let event = self.expect_index("read event index")?;
            self.expect(Token::RParen)?;
            steps.push(SourcePathStep::ReadEvent(event));
        }
        if matches!(steps.as_slice(), [SourcePathStep::Loop(_)]) {
            return Ok(CodeRegionRef::Loop(match steps[0] {
                SourcePathStep::Loop(index) => index,
                _ => unreachable!(),
            }));
        }
        Ok(CodeRegionRef::Path(steps))
    }

    /// The arguments of a `call` step after its `(`: `j)` for the `j`th
    /// call of any function, or `f, j)` for the `j`th call of `f`. A Rust
    /// sidecar writes `f` as its path, which arrives as the address of the
    /// function the importer names.
    fn parse_call_step(&mut self) -> Result<SourcePathStep, ClickError> {
        if matches!(self.peek(), Some(Token::Number(_))) {
            let index = self.expect_index("call index")?;
            self.expect(Token::RParen)?;
            return Ok(SourcePathStep::AnyCall(index));
        }
        if self.peek() == Some(&Token::Amp) && matches!(self.peek_next(), Some(Token::Ident(_))) {
            self.position += 1;
        }
        let function = self.expect_ident("called function")?;
        self.expect(Token::Comma)?;
        let index = self.expect_index("call index")?;
        self.expect(Token::RParen)?;
        Ok(SourcePathStep::Call(function, index))
    }

    fn parse_code_region_ref(&mut self) -> Result<CodeRegionRef, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "function" => Ok(CodeRegionRef::Function),
            // A function's `j`th call, counted among all its calls.
            Some(Token::Ident(kind)) if kind == "call" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let step = self.parse_call_step()?;
                Ok(CodeRegionRef::Path(vec![step]))
            }
            Some(Token::Ident(kind)) if kind == "loop" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("loop index")?;
                self.expect(Token::RParen)?;
                if self.chained_region_follows(&["back_edge"]) {
                    self.expect(Token::Dot)?;
                    self.expect_ident("back_edge")?;
                    self.expect(Token::LParen)?;
                    self.expect(Token::RParen)?;
                    return Ok(CodeRegionRef::BackEdge(Some(index)));
                }
                if self.source_path_step_follows() {
                    return self.parse_source_path(vec![SourcePathStep::Loop(index)]);
                }
                Ok(CodeRegionRef::Loop(index))
            }
            Some(Token::Ident(kind)) if kind == "region" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("region index")?;
                self.expect(Token::RParen)?;
                if self.chained_region_follows(&["read_event"]) {
                    return self.parse_source_path(vec![SourcePathStep::Region(index)]);
                }
                Ok(CodeRegionRef::Region(index))
            }
            Some(Token::Ident(kind)) if kind == "statement" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("statement index")?;
                self.expect(Token::RParen)?;
                self.parse_source_path(vec![SourcePathStep::Statement(index)])
            }
            Some(Token::Ident(kind)) if kind == "back_edge" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::BackEdge(None))
            }
            Some(Token::Ident(kind)) if kind == "read" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let occurrence = self.expect_index("read occurrence")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Read(occurrence))
            }
            Some(Token::Ident(kind)) if kind == "assignment" && self.peek() == Some(&Token::LParen) => {
                self.expect(Token::LParen)?;
                let local = self.expect_assignment_local()?;
                self.expect(Token::Comma)?;
                let occurrence = self.expect_index("assignment occurrence")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Assignment { local, occurrence })
            }
            Some(Token::Ident(label)) => Ok(CodeRegionRef::Label(label)),
            Some(token) => Err(self.error(format!(
                "expected code region `function`, `loop(N)`, `region(N)`, `assignment(local, N)`, `read(N)`, `back_edge()`, or label, got {token}"
            ))),
            None => Err(self.error(
                "expected code region `function`, `loop(N)`, `region(N)`, `assignment(local, N)`, `read(N)`, `back_edge()`, or label, got end of input",
            )),
        }
    }

    fn parse_tactic(&mut self) -> Result<SmartTactic, ClickError> {
        let tactic = match self.next() {
            Some(Token::Ident(name)) if name == "solve" => SmartTactic::Solve,
            Some(Token::Ident(name)) if let Some(refusal) = removed_tactic_refusal(&name) => {
                self.position -= 1;
                return Err(self.error(refusal));
            }
            Some(Token::Ident(name)) => {
                return Err(self.error(format!("expected tactic, got `{name}`")));
            }
            Some(token) => {
                return Err(self.error(format!("expected tactic, got {token}")));
            }
            None => return Err(self.error("expected tactic, got end of input")),
        };
        self.expect_empty_tactic_args("solve")?;
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    fn parse_ensure_expression(&mut self) -> Result<CExpression, ClickError> {
        self.parse_ensure_bitwise_or()
    }

    fn resource_expression_follows(&mut self) -> bool {
        let saved = self.position;
        loop {
            if self.peek() == Some(&Token::LParen) {
                self.position += 1;
            } else if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
                self.position += 2;
                if self.parse_program_point_selector().is_err()
                    || self.expect(Token::Comma).is_err()
                {
                    self.position = saved;
                    return false;
                }
            } else {
                break;
            }
        }
        let follows = self.peek_ident().is_some_and(|name| {
            self.resource_parameters.contains_key(name)
                || self.empty_resource_token_len(self.position).is_some()
                || (name == "memory" && self.peek_next() == Some(&Token::LParen))
                || (self.names.resource_bindings.contains_key(name)
                    && !matches!(self.peek_next(), Some(Token::Dot | Token::LParen)))
        });
        self.position = saved;
        follows
    }

    fn parse_contract_expression(&mut self) -> Result<ContractExpression, ClickError> {
        if self.resource_expression_follows() {
            return self
                .parse_resource_subject()
                .map(|r| ContractExpression::Resource(Box::new(r)));
        }
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
        let mut values = vec![self.parse_casts(first)?];
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
            let constructor = if self.verifies_rust() {
                match self.tokens.get(self.position - 1) {
                    Some(Token::ShiftLeft) => {
                        ContractExpression::RustShiftLeft as ContractBinaryConstructor
                    }
                    Some(Token::ShiftRight) => {
                        ContractExpression::RustShiftRight as ContractBinaryConstructor
                    }
                    _ => constructor,
                }
            } else {
                constructor
            };
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

    fn parse_measure_component(&mut self) -> Result<ContractExpression, ClickError> {
        let component = self.parse_contract_expression()?;
        // In a decreases clause a bare resource name selects its structural
        // measure, as before resource descriptors could be theorem arguments.
        let component = match component {
            ContractExpression::Resource(subject) => match *subject {
                ResourceSubject::Instance { name, .. } => ContractExpression::Binding(name),
                other => ContractExpression::Resource(Box::new(other)),
            },
            other => other,
        };
        Ok(self.at_integer_position(component))
    }

    fn parse_termination_measure(&mut self) -> Result<TerminationMeasure, ClickError> {
        let components = if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            if self.peek() == Some(&Token::RParen) {
                return Err(self.error("termination measure cannot be empty"));
            }
            let mut components = vec![self.parse_measure_component()?];
            while self.peek() == Some(&Token::Comma) {
                self.position += 1;
                components.push(self.parse_measure_component()?);
            }
            self.expect(Token::RParen)?;
            components
        } else {
            vec![self.parse_measure_component()?]
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
            let base = contract_expression_as_program_expression(&expression).ok_or_else(|| {
                self.error("memory segment base must be a current C pointer expression")
            })?;
            (expression, base)
        } else if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            let base = contract_expression_as_program_expression(&expression).ok_or_else(|| {
                self.error("memory segment base must be a current C pointer expression")
            })?;
            (expression, base)
        } else {
            self.parse_segment_primary()?
        };
        let mut struct_name = match &surface_base {
            ContractExpression::Field { .. } => self.contract_expression_struct_name(&surface_base),
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self.binding_struct_name(binding).cloned(),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
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
                lowered: ProgramExpression::Cast { pointee_struct, .. },
                ..
            }
            | ContractExpression::ProgramExpression(ProgramExpression::Cast {
                pointee_struct,
                ..
            }) => pointee_struct.clone(),
            _ => None,
        };
        if let ContractExpression::Binding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) = &surface_base
            && self
                .names
                .struct_params
                .contains_key(&struct_pointer_pointer_key(name))
        {
            struct_name = None;
        }
        let names_aggregate_object = match &surface_base {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self.binding_is_aggregate(binding),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => {
                self.names.aggregate_objects.contains_key(name)
                    || self.names.global_array_shapes.contains_key(name)
                    || self.qualified_object(name).is_some()
            }
            _ => false,
        };
        let mut dereferences_pointer = !names_aggregate_object;
        let mut union_name: Option<String> = None;
        let mut struct_array_element_width = match &surface_base {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self
                .local_bindings
                .info(binding)
                .filter(|info| info.array_shape.is_some())
                .and_then(|info| info.struct_name.as_ref())
                .and_then(|name| self.struct_layouts.get(name))
                .map(|layout| layout.size_bytes()),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) if self.names.contains(NameKind::StructArrayParameter, name) => struct_name
                .as_ref()
                .and_then(|name| self.struct_layouts.get(name))
                .map(|layout| layout.size_bytes()),
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some() && object.array_shape.is_some())
                .and_then(|object| object.struct_name.as_ref())
                .and_then(|name| self.struct_layouts.get(name))
                .map(|layout| layout.size_bytes()),
            _ => None,
        };
        let mut struct_array_shape = match &surface_base {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self
                .local_bindings
                .info(binding)
                .filter(|info| info.struct_name.is_some())
                .and_then(|info| info.array_shape.clone()),
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some())
                .and_then(|object| object.array_shape.clone()),
            _ => None,
        };
        let mut scalar_array_shape = match &surface_base {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self
                .local_bindings
                .info(binding)
                .filter(|info| info.struct_name.is_none())
                .and_then(|info| info.array_shape.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
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
        let mut indexed_scalar_field: Option<ProgramType> = None;
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
                let index = contract_expression_as_program_expression(&index).ok_or_else(|| {
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
                    // A single complete element retains typed indexing. Byte
                    // arithmetic below is for navigating further into a struct;
                    // its pointer result is not a place to take the address of.
                    if struct_array_shape.is_none()
                        && !matches!(
                            self.peek(),
                            Some(Token::Arrow | Token::Dot | Token::LBracket)
                        )
                    {
                        base = ProgramExpression::Index(Box::new(base), Box::new(index.clone()));
                        surface_base = ContractExpression::Index(
                            Box::new(surface_base_before_index),
                            Box::new(ContractExpression::ProgramExpression(index)),
                        );
                        struct_name = None;
                        union_name = None;
                        struct_array_element_width = None;
                        continue;
                    }
                    let mut indexes = vec![index.clone()];
                    let mut surface_indexes =
                        vec![ContractExpression::ProgramExpression(index.clone())];
                    while struct_array_shape.is_some() && self.peek() == Some(&Token::LBracket) {
                        self.position += 1;
                        let next_index = self.parse_contract_expression()?;
                        self.expect(Token::RBracket)?;
                        let next_index = contract_expression_as_program_expression(&next_index)
                            .ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                        indexes.push(next_index.clone());
                        surface_indexes.push(ContractExpression::ProgramExpression(next_index));
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
                    base =
                        ProgramExpression::Add(Box::new(struct_byte_base(base)), Box::new(stride));
                    surface_base = surface_indexes
                        .into_iter()
                        .fold(surface_base_before_index, |base, index| {
                            ContractExpression::Index(Box::new(base), Box::new(index))
                        });
                    struct_array_element_width = None;
                    indexed_scalar_field = None;
                } else if let Some(shape) = struct_array_shape.take() {
                    let mut indexes = vec![index.clone()];
                    let mut surface_indexes = vec![ContractExpression::ProgramExpression(index)];
                    while self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range()
                    {
                        self.position += 1;
                        let next_index = self.parse_contract_expression()?;
                        self.expect(Token::RBracket)?;
                        let next_index = contract_expression_as_program_expression(&next_index)
                            .ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                        indexes.push(next_index.clone());
                        surface_indexes.push(ContractExpression::ProgramExpression(next_index));
                    }
                    if indexes.len() != shape.len() {
                        return Err(self.error(format!(
                            "multidimensional scalar array field requires {} indices, got {}",
                            shape.len(),
                            indexes.len()
                        )));
                    }
                    let offset = flatten_array_indices(indexes, &shape);
                    base = ProgramExpression::Add(Box::new(base), Box::new(offset));
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
                    let mut surface_indexes = vec![ContractExpression::ProgramExpression(index)];
                    while self.peek() == Some(&Token::LBracket) && !self.contract_bracket_is_range()
                    {
                        self.position += 1;
                        let next_index = self.parse_contract_expression()?;
                        self.expect(Token::RBracket)?;
                        let next_index = contract_expression_as_program_expression(&next_index)
                            .ok_or_else(|| {
                                self.error("global array indices must be current C expressions")
                            })?;
                        indexes.push(next_index.clone());
                        surface_indexes.push(ContractExpression::ProgramExpression(next_index));
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
                        ProgramExpression::Index(Box::new(base), Box::new(offset))
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
                    let surface_index = ContractExpression::ProgramExpression(index.clone());
                    base = ProgramExpression::Index(Box::new(base), Box::new(index));
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
                            interface_type: InterfaceType::UInt8,
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
                    if field.struct_name.is_some() && !field.interface_type.is_pointer() {
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
                            interface_type: InterfaceType::UInt8,
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
                dereferences_pointer = field.interface_type.is_pointer();
                let pointer = self.offset_field_pointer(base, field.offset_bytes);
                let field_memory_pointer = field_has_direct_memory_place(&field);
                scalar_field = field_memory_pointer
                    && matches!(
                        field.interface_type,
                        InterfaceType::Int8
                            | InterfaceType::Int16
                            | InterfaceType::Int32
                            | InterfaceType::Char(_)
                            | InterfaceType::UInt8
                            | InterfaceType::UInt16
                            | InterfaceType::UInt32
                            | InterfaceType::Int64(_)
                            | InterfaceType::UInt64(_)
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
                dereferences_pointer = field.interface_type.is_pointer();
                let pointer = self.member_field_pointer(base, &field);
                let field_memory_pointer = field_has_direct_memory_place(&field);
                scalar_field = field_memory_pointer
                    && matches!(
                        field.interface_type,
                        InterfaceType::Int8
                            | InterfaceType::Int16
                            | InterfaceType::Int32
                            | InterfaceType::Char(_)
                            | InterfaceType::UInt8
                            | InterfaceType::UInt16
                            | InterfaceType::UInt32
                            | InterfaceType::Int64(_)
                            | InterfaceType::UInt64(_)
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
                    ProgramExpression::TypedLoad {
                        value_type:
                            ProgramType::Int32Array(_)
                            | ProgramType::UInt8Array(_)
                            | ProgramType::Int8Array(_)
                            | ProgramType::Int16Array(_)
                            | ProgramType::UInt16Array(_)
                            | ProgramType::UInt32Array(_)
                            | ProgramType::Int128Array(_)
                            | ProgramType::Int64Array(_)
                            | ProgramType::UInt128Array(_)
                            | ProgramType::UInt64Array(_),
                        ..
                    } => None,
                    ProgramExpression::TypedLoad { pointer, .. } => Some((**pointer).clone()),
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
            let address = ProgramExpression::AddressOf(Box::new(ProgramExpression::TypedLoad {
                pointer: Box::new(base.clone()),
                value_type: element_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            }));
            return Ok(vec![ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base,
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::CUnary {
                        operand: Box::new(surface_base),
                        lowered: address,
                    },
                    start: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(
                        0,
                    ))),
                    end: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
                },
            }]);
        }
        // A struct reference written alone is the struct it refers to.
        let carries_reference = |binding: &crate::kernel::BindingName| {
            binding.reference_referent().is_some_and(|referent| {
                self.names
                    .contains(NameKind::ReferenceParameter, referent.source_name())
            })
        };
        let names_reference = matches!(&surface_base,
            ContractExpression::ProgramExpression(ProgramExpression::Variable(binding))
                if carries_reference(binding));
        let names_scalar_referent = matches!(&surface_base,
            ContractExpression::ProgramExpression(ProgramExpression::Index(carrier, _))
                if matches!(carrier.as_ref(), ProgramExpression::Variable(binding) if carries_reference(binding)));

        if dereference && (names_reference || names_scalar_referent) {
            return Err(self.error(
                "a reference parameter already names what it refers to; write it without `*`",
            ));
        }
        // Written alone, a scalar referent is the one element behind its
        // carrier, typed and sized by the carrier.
        if names_scalar_referent
            && self.peek() != Some(&Token::LBracket)
            && let ProgramExpression::Index(carrier, _) = &base
        {
            let (start, end) = (
                ProgramExpression::Value(int32(0)),
                ProgramExpression::Value(int32(1)),
            );
            return Ok(vec![ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: (**carrier).clone(),
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::ProgramExpression((**carrier).clone()),
                    start: ContractExpression::ProgramExpression(start),
                    end: ContractExpression::ProgramExpression(end),
                },
            }]);
        }
        // Written alone, a struct reference is the object it refers to.
        let dereference = dereference
            || (names_reference
                && matches!(base, ProgramExpression::Variable(_))
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
            if let ProgramExpression::Variable(crate::kernel::BindingName::Named(name)) = &base
                && self.rust_slice_params.contains(name)
            {
                let length = ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    format!("{name}_len").into(),
                ));
                let end_expression = length;
                let end = contract_expression_as_program_expression(&end_expression)
                    .expect("a slice length is a C expression");
                let start = ProgramExpression::Value(int32(0));
                return Ok(vec![ContractSegment {
                    uninitialized: false,
                    state: ContractSegmentState::Current,
                    base,
                    start: start.clone(),
                    end,
                    surface: ContractSegmentSurface::Range {
                        base: surface_base,
                        start: ContractExpression::ProgramExpression(start),
                        end: end_expression,
                    },
                }]);
            }
            let (start, end) = (
                ProgramExpression::Value(int32(0)),
                ProgramExpression::Value(int32(1)),
            );
            let Some(struct_name) = struct_name else {
                return Ok(vec![ContractSegment {
                    uninitialized: false,
                    state: ContractSegmentState::Current,
                    base,
                    start: start.clone(),
                    end: end.clone(),
                    surface: ContractSegmentSurface::Range {
                        base: surface_base,
                        start: ContractExpression::ProgramExpression(start),
                        end: ContractExpression::ProgramExpression(end),
                    },
                }]);
            };
            return Ok(vec![self.object_segment(base, struct_name)?]);
        }
        // A declared struct object owns all of its storage, with the same
        // word-based size as `*p` for a pointer to that struct. Retain its
        // imported ABI so input cells use the actual field types.
        if postfixes == 0
            && self.peek() != Some(&Token::LBracket)
            && let ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) =
                &surface_base
        {
            let object = if name.named().is_none() {
                self.local_bindings
                    .info(name)
                    .filter(|info| info.aggregate)
                    .and_then(|info| info.struct_name.as_ref())
                    .map(|name| (name, ProgramExpression::AddressOf(Box::new(base.clone()))))
            } else if let Some(name) = name.named() {
                if !self.names.program_parameter_types.contains_key(name)
                    && !self.names.contains(NameKind::StructArrayParameter, name)
                    && let Some(struct_name) = self.names.aggregate_objects.get(name)
                {
                    Some((
                        struct_name,
                        ProgramExpression::AddressOf(Box::new(base.clone())),
                    ))
                } else {
                    self.qualified_object(name)
                        .filter(|object| object.address.is_none() && object.array_shape.is_none())
                        .and_then(|object| {
                            Some((object.struct_name.as_ref()?, object.expression.clone()))
                        })
                }
            } else {
                None
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
            if let ProgramExpression::Variable(crate::kernel::BindingName::Named(name)) = &base
                && self.names.struct_params.contains_key(name)
                && !names_aggregate_object
            {
                return Err(self.error(format!(
                    "`{name}` alone names the variable that holds the pointer, which a contract cannot own; write `*{name}` for the object it points at"
                )));
            }
            let base = match base {
                ProgramExpression::TypedLoad { pointer, .. } => *pointer,
                ProgramExpression::Value(ProgramValue::Pointer(_)) => {
                    let ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) =
                        &surface_base
                    else {
                        return Err(self.error("this C expression has no storage to own"));
                    };
                    name.named()
                        .and_then(|name| self.qualified_object(name))
                        .and_then(|object| object.address.clone())
                        .ok_or_else(|| self.error("this C expression has no storage to own"))?
                }
                expression => ProgramExpression::AddressOf(Box::new(expression)),
            };
            let surface_base =
                ContractExpression::ProgramExpression(ProgramExpression::AddressOf(Box::new(
                    contract_expression_as_program_expression(&surface_base)
                        .expect("C segment base"),
                )));
            return Ok(vec![ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base,
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: surface_base,
                    start: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(
                        0,
                    ))),
                    end: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
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
        let mut start = resource_body_program_expression(&start_expression).ok_or_else(|| {
            self.error(
                "memory segment start must be a current C expression or a scalar field of the resource being defined",
            )
        })?;
        self.expect(Token::DotDot)?;
        let end_expression = self.parse_contract_expression()?;
        let mut end = resource_body_program_expression(&end_expression).ok_or_else(|| {
            self.error(
                "memory segment end must be a current C expression or a scalar field of the resource being defined",
            )
        })?;
        self.expect(Token::RBracket)?;
        if let Some(offset) = scalar_range_offset {
            start = ProgramExpression::Add(Box::new(offset.clone()), Box::new(start));
            end = ProgramExpression::Add(Box::new(offset), Box::new(end));
        }
        Ok(vec![ContractSegment {
            uninitialized: false,
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
        base: ProgramExpression,
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
            uninitialized: false,
            state: ContractSegmentState::Current,
            base,
            start: ProgramExpression::Value(int32(0)),
            end: ProgramExpression::Value(int32(layout.size_bytes() / 4)),
            surface: ContractSegmentSurface::Object(struct_name),
        })
    }

    fn aggregate_field_segments(
        &self,
        base: ProgramExpression,
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
        base: ProgramExpression,
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
                .filter(|_| !resolved.interface_type.is_pointer())
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
                .ok_or_else(|| self.error("aggregate field size overflows"))?;
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
        base: ProgramExpression,
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
        base: ProgramExpression,
        surface_base: Option<ContractExpression>,
        field_name: &str,
    ) -> Result<ContractSegment, ClickError> {
        let Some(field) = self.resolve_field_metadata(&base, field_name)? else {
            // A base whose layout this parse cannot name, such as a loaded
            // pointer, keeps its field name for later lowering to resolve.
            return Ok(ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base,
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Field {
                    value_bytes: None,
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
        base: ProgramExpression,
        surface_base: Option<ContractExpression>,
        field_name: &str,
        field: &ResolvedField,
    ) -> ContractSegment {
        let array = match field.interface_type {
            InterfaceType::Int32Array(length) => Some((length, 4, ProgramType::Int32)),
            InterfaceType::Int64Array(_, length) => Some((length, 8, ProgramType::Int64)),
            InterfaceType::Int128Array(length) => Some((length, 16, ProgramType::Int128)),
            InterfaceType::UInt64Array(_, length) => Some((length, 8, ProgramType::UInt64)),
            InterfaceType::UInt128Array(length) => Some((length, 16, ProgramType::UInt128)),
            InterfaceType::CharArray(crate::languages::c::syntax::PlainChar::Unsigned, length)
            | InterfaceType::UInt8Array(length) => Some((length, 1, ProgramType::UInt8)),
            InterfaceType::CharArray(crate::languages::c::syntax::PlainChar::Signed, length)
            | InterfaceType::Int8Array(length) => Some((length, 1, ProgramType::Int8)),
            _ => None,
        };
        if let Some((length, element_width, element_type)) = array {
            let field_base =
                crate::kernel::program_expression::pointer_offset_bytes(base, field.offset_bytes);
            return ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: ProgramExpression::TypedLoad {
                    pointer: Box::new(field_base),
                    value_type: field.interface_type.to_kernel_type(),
                    volatile: false,
                    pointee_constant: field.pointee_constant,
                    access_class: None,
                    source: Default::default(),
                },
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(length)),
                surface: ContractSegmentSurface::Field {
                    value_bytes: None,
                    base: surface_base.map(Box::new),
                    name: field_name.to_string(),
                    element_width: Some(element_width),
                    element_type: Some(element_type),
                },
            };
        }
        let element_width = match field.interface_type {
            InterfaceType::Char(_) => 1,
            InterfaceType::UInt8 => 1,
            InterfaceType::Int8 => 1,
            InterfaceType::Int16 | InterfaceType::UInt16 => 2,
            InterfaceType::Int64(_) | InterfaceType::UInt64(_) => 8,
            InterfaceType::Float32 => 4,
            InterfaceType::Float64 => 8,
            _ => 4,
        };
        let start = field.offset_bytes / element_width;
        let end = field.slot_end_bytes / element_width;
        ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base,
            start: ProgramExpression::Value(int32(start)),
            end: ProgramExpression::Value(int32(end)),
            surface: ContractSegmentSurface::Field {
                base: surface_base.map(Box::new),
                name: field_name.to_string(),
                // Non-array fields use their ABI width as the resource slot
                // width. Smaller integer fields retain their natural
                // two-byte/one-byte units so a typed load is covered exactly.
                element_width: Some(element_width),
                element_type: Some(field.interface_type.to_kernel_type()),
                value_bytes: Some(element_width),
            },
        }
    }

    fn resolve_field_load(
        &self,
        base: ProgramExpression,
        field_name: &str,
    ) -> Result<ProgramExpression, ClickError> {
        self.refuse_trait_receiver_field(
            named_place_base(&base).and_then(crate::kernel::BindingName::named),
        )?;
        let Some(field) = self.resolve_field_metadata(&base, field_name)? else {
            return Ok(ProgramExpression::Load(Box::new(base)));
        };
        Ok(ProgramExpression::TypedLoad {
            pointer: Box::new(self.member_field_pointer(base, &field)),
            value_type: field.interface_type.to_kernel_type(),
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

    fn resolve_c_field_load(
        &self,
        base: CExpression,
        field_name: &str,
    ) -> Result<Option<CExpression>, ClickError> {
        if let CExpression::Variable(name) = &base {
            self.refuse_trait_receiver_field(name.named())?;
        }
        let struct_name = match &base {
            CExpression::Variable(base_name) => self.binding_struct_name(base_name),
            CExpression::Field {
                field_struct_name, ..
            } => field_struct_name.as_ref(),
            CExpression::AggregateAddress { struct_name, .. } => Some(struct_name),
            CExpression::Cast { struct_name, .. } => struct_name.as_ref(),
            _ => None,
        };
        if let Some(struct_name) = struct_name {
            let field = self.resolve_struct_field_metadata(struct_name, field_name)?;
            let pointer = self.offset_c_field_pointer(base.clone(), field.offset_bytes);
            return Ok(Some(if let Some(union_name) = field.union_name {
                CExpression::UnionAddress {
                    pointer: Box::new(pointer),
                    union_name,
                }
            } else if field.interface_type == InterfaceType::Int32 {
                if let Some(struct_name) = field.struct_name {
                    CExpression::AggregateAddress {
                        pointer: Box::new(pointer),
                        struct_name,
                    }
                } else {
                    CExpression::Field {
                        pointer: Box::new(pointer),
                        field_type: field.interface_type,
                        pointee_constant: field.pointee_constant,
                        field_struct_name: None,
                        function_pointer_signature: None,
                        array_shape: None,
                        source: None,
                        access_class: None,
                    }
                }
            } else {
                CExpression::Field {
                    pointer: Box::new(pointer),
                    field_type: field.interface_type,
                    pointee_constant: field.pointee_constant,
                    field_struct_name: field.struct_name,
                    function_pointer_signature: field.function_pointer_signature.clone(),
                    array_shape: field.array_shape,
                    source: None,
                    access_class: None,
                }
            }));
        }
        if let CExpression::UnionAddress { union_name, .. } = &base {
            let field = self.resolve_union_field_metadata(union_name, field_name)?;
            let pointer = self.offset_c_field_pointer(base.clone(), field.offset_bytes);
            return Ok(Some(CExpression::UnionField {
                pointer: Box::new(pointer),
                field_type: field.interface_type,
                union_name: union_name.clone(),
                pointee_constant: field.pointee_constant,
            }));
        }
        Ok(None)
    }

    fn resolve_field_metadata(
        &self,
        base: &ProgramExpression,
        field_name: &str,
    ) -> Result<Option<ResolvedField>, ClickError> {
        let Some(base_name) = named_place_base(base) else {
            return Ok(None);
        };
        let Some(struct_name) = self.binding_struct_name(base_name) else {
            if let Some(name) = base_name.named() {
                self.reject_non_struct_arm_base(name, field_name)?;
            }
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
    /// pointer value may come from another state while a later field load
    /// still reads the surrounding state.
    fn binding_struct_name(&self, binding: &crate::kernel::BindingName) -> Option<&String> {
        match binding {
            crate::kernel::BindingName::ReferenceCarrier(referent) => {
                self.binding_struct_name(referent)
            }
            crate::kernel::BindingName::ContractException => None,
            crate::kernel::BindingName::Generated(id) => match self.let_operands.types.get(id) {
                Some(ClickType::CObjectPointer { struct_name, .. }) => Some(struct_name),
                _ => None,
            },
            crate::kernel::BindingName::ContractResult => self
                .names
                .struct_params
                .get("result")
                .or_else(|| self.names.aggregate_objects.get("result")),
            crate::kernel::BindingName::Static(id) => {
                self.local_bindings.statics.get(id)?.struct_name.as_ref()
            }
            crate::kernel::BindingName::Local(id) => self
                .local_bindings
                .declarations
                .get(id)?
                .struct_name
                .as_ref(),
            crate::kernel::BindingName::Named(name) => self
                .names
                .struct_params
                .get(name)
                .or_else(|| self.names.aggregate_objects.get(name))
                .or_else(|| {
                    self.qualified_object(name)
                        .and_then(|object| object.struct_name.as_ref())
                }),
        }
    }
    fn binding_is_aggregate(&self, binding: &crate::kernel::BindingName) -> bool {
        match binding {
            crate::kernel::BindingName::ReferenceCarrier(_) => false,
            crate::kernel::BindingName::ContractException
            | crate::kernel::BindingName::Generated(_) => false,
            crate::kernel::BindingName::ContractResult => {
                self.names.aggregate_objects.contains_key("result")
            }
            crate::kernel::BindingName::Static(id) => self
                .local_bindings
                .statics
                .get(id)
                .is_some_and(|info| info.aggregate),
            crate::kernel::BindingName::Local(id) => self
                .local_bindings
                .declarations
                .get(id)
                .is_some_and(|info| info.aggregate),
            crate::kernel::BindingName::Named(name) => {
                self.names.aggregate_objects.contains_key(name)
            }
        }
    }

    fn contract_expression_struct_name(&self, expression: &ContractExpression) -> Option<String> {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self.binding_struct_name(binding).cloned(),
            ContractExpression::CUnary {
                lowered: ProgramExpression::Cast { pointee_struct, .. },
                ..
            }
            | ContractExpression::ProgramExpression(ProgramExpression::Cast {
                pointee_struct,
                ..
            }) => pointee_struct.clone(),
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
                .names
                .struct_params
                .get(name)
                .or_else(|| self.names.aggregate_objects.get(name))
                .cloned(),
            ContractExpression::Field { base, field, .. } => {
                let struct_name = self.contract_expression_struct_name(base)?;
                // Only nominal identity is needed here. Read the exact
                // declaration and field indexes, without preparing a resource
                // slot or inspecting the record's other fields.
                self.struct_layouts
                    .get(&struct_name)?
                    .field(field)?
                    .struct_name()
                    .map(str::to_string)
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
            .map(crate::languages::interface::RecordField::offset_bytes)
            .filter(|offset| *offset > field.offset_bytes())
            .min()
            .unwrap_or_else(|| layout.size_bytes());
        Ok(ResolvedField {
            interface_type: field.interface_type(),
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
            interface_type: field.interface_type(),
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
        if field.interface_type == InterfaceType::Int32
            && (field.struct_name.is_some() || field.union_name.is_some())
        {
            return Err(self.error(
                "aggregate struct and union field places are not supported; name a leaf field instead",
            ));
        }
        if matches!(
            field.interface_type,
            InterfaceType::Int32Array(_)
                | InterfaceType::CharArray(_, _)
                | InterfaceType::UInt8Array(_)
                | InterfaceType::Int128Array(_)
                | InterfaceType::Int64Array(_, _)
                | InterfaceType::UInt128Array(_)
                | InterfaceType::UInt64Array(_, _)
        ) {
            let width = match field.interface_type {
                InterfaceType::Int64Array(_, _) | InterfaceType::UInt64Array(_, _) => 8,
                InterfaceType::Int128Array(_) | InterfaceType::UInt128Array(_) => 16,
                InterfaceType::Int32Array(_) => 4,
                _ => 1,
            };
            if !field.offset_bytes.is_multiple_of(width)
                || field.slot_end_bytes < field.offset_bytes
                || !(field.slot_end_bytes - field.offset_bytes).is_multiple_of(width)
            {
                return Err(self.error("inline array field has an invalid resource size"));
            }
            return Ok(());
        }
        if matches!(
            field.interface_type,
            InterfaceType::Int16 | InterfaceType::UInt16
        ) {
            if !field.offset_bytes.is_multiple_of(2)
                || field.byte_width != 2
                || field.slot_end_bytes < field.offset_bytes
                || !(field.slot_end_bytes - field.offset_bytes).is_multiple_of(2)
            {
                return Err(self.error("16-bit field places require two-byte alignment and width"));
            }
            return Ok(());
        }
        if matches!(
            field.interface_type,
            InterfaceType::Int64(_) | InterfaceType::UInt64(_)
        ) {
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
        if matches!(
            field.interface_type,
            InterfaceType::Int8 | InterfaceType::Char(_) | InterfaceType::UInt8
        ) {
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

    fn member_field_pointer(
        &self,
        base: ProgramExpression,
        field: &ResolvedField,
    ) -> ProgramExpression {
        let pointer = self.offset_field_pointer(base, field.offset_bytes);
        if field.byte_width == 0 {
            return pointer;
        }
        ProgramExpression::Subobject {
            pointer: Box::new(pointer),
            width: field.byte_width,
        }
    }

    fn offset_field_pointer(
        &self,
        base: ProgramExpression,
        offset_bytes: u32,
    ) -> ProgramExpression {
        crate::kernel::program_expression::pointer_offset_bytes(base, offset_bytes)
    }

    fn offset_c_field_pointer(&self, base: CExpression, offset_bytes: u32) -> CExpression {
        if offset_bytes == 0 {
            base
        } else {
            CExpression::PointerOffsetBytes {
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
        operand: &ProgramExpression,
        struct_name: &str,
    ) -> Result<(), ClickError> {
        // Integer casts name the complete word's reconstructed pointer.
        // Unknown types (notably `result`) are checked after elaboration.
        if matches!(
            crate::surface::validation::infer_program_expression_type(
                operand,
                &self.names.program_parameter_types,
            ),
            None | Some(InterfaceType::Int64(_) | InterfaceType::UInt64(_))
        ) {
            return Ok(());
        }
        // An explicit conversion through void retains its target layout on
        // the expression. It does not assign a layout to the source parameter.
        if matches!(
            operand,
            ProgramExpression::Cast {
                target_type: ProgramType::VoidPointer,
                ..
            }
        ) {
            return Ok(());
        }
        if matches!(operand, ProgramExpression::Variable(name) if name.named().is_none() && name.program_type() == Some(ProgramType::VoidPointer))
        {
            return Ok(());
        }
        let name = match operand {
            ProgramExpression::Variable(name) => name.named(),
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

    /// Keep binding names disjoint from cast type names: in particular,
    /// `verifying "f.c" as uint32` would otherwise read as a cast.
    fn refuse_cast_type_binder(&self, name: &str) -> Result<(), ClickError> {
        if rust_syntax::click_numeric_cast_type(name).is_some()
            || (self.verifies_rust() && rust_syntax::rust_scalar_type(name).is_some())
        {
            return Err(self.error(format!(
                "`{name}` is a type name, which `as` reads as a cast; bind another name"
            )));
        }
        Ok(())
    }

    /// The refusal of a C-style cast in Click text: a Click cast is written
    /// after its operand, `e as T`, with a pointer target parenthesized.
    fn legacy_cast_error(&self, target: &str, pointer: bool) -> ClickError {
        let written = if pointer {
            format!("e as ({target})")
        } else {
            format!("e as {target}")
        };
        self.error(format!(
            "a Click cast is written after its operand: write `{written}`, not `({target}) e`"
        ))
    }

    /// A native cast target. Pointer qualifiers add to the source view;
    /// an unqualified byte cast still inherits its source qualification.
    fn parse_click_cast_type(&mut self) -> Result<(ProgramType, bool, bool), ClickError> {
        let mut constant = false;
        let mut volatile = false;
        while let Some(name) = self.peek_ident() {
            match name {
                "const" => constant = true,
                "volatile" => volatile = true,
                _ => break,
            }
            self.position += 1;
        }
        let parsed_type = self.parse_type()?;
        let target_type = parsed_type.interface_type.to_kernel_type();
        if parsed_type.reference
            || parsed_type.constant
            || (!target_type.is_pointer() && (constant || volatile))
        {
            return Err(self.error("contract cast qualifiers apply to a pointer's pointee"));
        }
        Ok((
            target_type,
            constant || parsed_type.pointee_constant,
            volatile,
        ))
    }

    /// A struct-pointer cast of `source_operand`, `p as (struct s *)`: the
    /// `void *` parameter it reads takes the struct's layout.
    fn lower_struct_pointer_cast(
        &mut self,
        cast: StructPointerCast,
        source_operand: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let Some(operand) = contract_expression_as_program_expression(&source_operand) else {
            return Err(self.error(
                "struct pointer cast expects a current C `void *` expression; put old(...) around the whole cast for an entry-state value",
            ));
        };
        let integer_source = crate::surface::validation::infer_program_expression_type(
            &operand,
            &self.names.program_parameter_types,
        )
        .is_some_and(|ty| matches!(ty, InterfaceType::Int64(_) | InterfaceType::UInt64(_)));
        if !integer_source {
            self.record_parameter_struct_cast(&operand, &cast.struct_name)?;
        }
        Ok(crate::surface::lowering::contract_c_unary(
            source_operand,
            ProgramExpression::Cast {
                expression: Box::new(operand),
                target_type: ProgramType::Int32Pointer,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: Some(cast.struct_name),
                pointee_volatile: false,
                pointee_constant: cast.pointee_constant,
                explicit_qualification: false,
            },
        ))
    }

    /// A Click cast of `operand` to a numeric or pointer `target_type`,
    /// `x as uint32` or `p as (uint8 *)`.
    fn lower_click_cast(
        &mut self,
        target_type: ProgramType,
        operand: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        self.lower_qualified_click_cast(target_type, false, false, operand)
    }

    fn lower_qualified_click_cast(
        &mut self,
        target_type: ProgramType,
        pointee_constant: bool,
        pointee_volatile: bool,
        operand: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let historical = crate::surface::validation::contains_old_expression(&operand)
            || crate::surface::validation::contains_at_expression(&operand);
        // Numeric casts consume the value observed by their operand.
        // Pointer casts retain their current-expression validation.
        let numeric_target = matches!(
            target_type,
            ProgramType::Float32
                | ProgramType::Float64
                | ProgramType::Int8
                | ProgramType::Int16
                | ProgramType::Int32
                | ProgramType::UInt8
                | ProgramType::UInt16
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
                | ProgramType::Int128
                | ProgramType::UInt128
        );
        if historical && !numeric_target {
            return Err(self.error("scalar cast expects a current expression; put old(...) around the whole cast for an entry-state value"));
        }
        let expression = contract_expression_as_program_expression(&operand)
            .unwrap_or(ProgramExpression::Value(int32(0)));
        if target_type == ProgramType::VoidPointer {
            crate::surface::validation::validate_void_pointer_cast_source(
                &expression,
                &self.names.program_parameter_types,
                "contract expression",
            )?;
        }
        Ok(ContractExpression::CUnary {
            operand: Box::new(operand),
            lowered: ProgramExpression::Cast {
                expression: Box::new(expression),
                target_type,
                // This cast was written in the contract. Pointer targets
                // use the specification cast rule, not the C conversion
                // marker also used for inserted pointer coercions. Authored
                // void and byte casts select the enclosing-object view.
                integer_mode: if target_type.is_pointer() {
                    crate::kernel::IntegerCastMode::Standard
                } else {
                    crate::kernel::IntegerCastMode::CConversion
                },
                pointee_struct: None,
                pointee_volatile,
                pointee_constant,
                explicit_qualification: false,
            },
        })
    }

    fn parse_contract_unary(&mut self) -> Result<ContractExpression, ClickError> {
        self.parse_contract_unary_at_depth(0)
    }

    fn parse_contract_unary_at_depth(
        &mut self,
        depth: usize,
    ) -> Result<ContractExpression, ClickError> {
        if let Some(cast) = self.peek_struct_pointer_cast() {
            return Err(self.legacy_cast_error(&cast.spelling(), true));
        }
        if self.starts_contract_scalar_cast() {
            let open = self.position;
            self.position += 1;
            let (target_type, _, _) = self.parse_click_cast_type()?;
            let close = self.position;
            self.expect(Token::RParen)?;
            let target = self.tokens[open + 1..close]
                .iter()
                .map(|token| match token {
                    Token::Ident(name) => name.clone(),
                    Token::Star => "*".to_string(),
                    token => token.to_string(),
                })
                .collect::<Vec<_>>()
                .join(" ");
            return Err(self.legacy_cast_error(&target, target_type.is_pointer()));
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
                return Ok(ContractExpression::ProgramExpression(
                    ProgramExpression::Value(ProgramValue::Int64(MachineTerm::int64_constant(
                        i64::MIN,
                    ))),
                ));
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
            let Some(pointer) = contract_expression_as_program_expression(&pointer) else {
                return Err(
                    self.error("pointer dereference is only supported on current C fragments")
                );
            };
            return Ok(crate::surface::lowering::contract_c_unary(
                source_pointer,
                ProgramExpression::Load(Box::new(pointer)),
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
                // `&p->f` (`design/pointer-subobject-bounds.md`), so a
                // contract's `&pair->second` is the program's pointer value
                // and is not equal to `&pair->first + 1`.
                if let ProgramExpression::TypedLoad { value_type, .. } = lowered
                    && value_type.pointer_to().is_some()
                {
                    return Ok(ContractExpression::CUnary {
                        operand: Box::new(expression.clone()),
                        lowered: ProgramExpression::AddressOf(Box::new(contract_member_lvalue(
                            lowered,
                        ))),
                    });
                }
                // An embedded record is already lowered as its address,
                // rather than a scalar load. Select that record's complete
                // subobject bounds, just as the source frontend does.
                if !matches!(lowered, ProgramExpression::TypedLoad { .. })
                    && let Some(name) = self.contract_expression_struct_name(&expression)
                    && let Some(layout) = self.struct_layouts.get(&name)
                {
                    return Ok(ContractExpression::CUnary {
                        operand: Box::new(expression.clone()),
                        lowered: ProgramExpression::Subobject {
                            pointer: Box::new(lowered.clone()),
                            width: layout.size_bytes(),
                        },
                    });
                }
                let source_base = (**base).clone();
                let Some(base) = contract_expression_as_program_expression(base) else {
                    return Err(self.error("address-of field requires a current C pointer base"));
                };
                return Ok(crate::surface::lowering::contract_c_unary(
                    source_base,
                    ProgramExpression::PointerOffsetBytes {
                        pointer: Box::new(base),
                        bytes: *offset_bytes,
                    },
                ));
            }
            let source_expression = expression.clone();
            let Some(expression) = contract_expression_as_program_expression(&expression) else {
                return Err(self.error("address-of is only supported on current C expressions"));
            };
            return Ok(crate::surface::lowering::contract_c_unary(
                source_expression,
                ProgramExpression::AddressOf(Box::new(expression)),
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

    fn reference_binding_carrier(&self, name: &str) -> crate::kernel::BindingName {
        if self.current_reference_result && name == "result" {
            "result".into()
        } else {
            crate::kernel::BindingName::reference_carrier(name)
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
        Ok(ContractExpression::ProgramExpression(
            ProgramExpression::Variable((carrier).into()),
        ))
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
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) = &expression
            && self.is_reference_binding(name)
        {
            let name = name.clone();
            let carrier = self.reference_binding_carrier(&name);
            let is_struct = self.names.struct_params.contains_key(carrier.source_name());
            if is_struct && !matches!(self.peek(), Some(Token::Arrow | Token::Dot)) {
                return Err(self.error(format!(
                    "`{name}` is a struct reference; name a field as `{name}.field`, or its address as `&{name}`"
                )));
            }
            expression = ContractExpression::ProgramExpression(ProgramExpression::Variable(
                (carrier).into(),
            ));
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
        if matches!(&expression, ContractExpression::RegionParameter { .. })
            || (matches!(&expression, ContractExpression::RegionResult(_))
                && self.peek() == Some(&Token::Dot))
        {
            return self.parse_region_parameter_suffix(expression);
        }
        expression = self.resolve_reference_parameter(expression)?;
        let mut struct_name = match &expression {
            ContractExpression::Field { .. } => self.contract_expression_struct_name(&expression),
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self.binding_struct_name(binding).cloned(),
            ContractExpression::CUnary {
                lowered: ProgramExpression::Cast { pointee_struct, .. },
                ..
            }
            | ContractExpression::ProgramExpression(ProgramExpression::Cast {
                pointee_struct,
                ..
            }) => pointee_struct.clone(),
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.struct_name.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
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
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) = &expression
            && self
                .names
                .struct_params
                .contains_key(&struct_pointer_pointer_key(name))
        {
            struct_name = None;
        }
        let mut union_name: Option<String> = None;
        let mut struct_array_element_width = match &expression {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self
                .local_bindings
                .info(binding)
                .filter(|info| info.array_shape.is_some())
                .and_then(|info| info.struct_name.as_ref())
                .and_then(|name| self.struct_layouts.get(name))
                .map(|layout| layout.size_bytes()),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
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
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self
                .local_bindings
                .info(binding)
                .filter(|info| info.struct_name.is_some())
                .and_then(|info| info.array_shape.clone()),
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .filter(|object| object.struct_name.is_some())
                .and_then(|object| object.array_shape.clone()),
            _ => None,
        };
        let mut scalar_array_shape = match &expression {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binding @ (crate::kernel::BindingName::ReferenceCarrier(_)
                | crate::kernel::BindingName::Local(_)
                | crate::kernel::BindingName::Static(_)),
            )) => self
                .local_bindings
                .info(binding)
                .filter(|info| info.struct_name.is_none())
                .and_then(|info| info.array_shape.clone()),
            ContractExpression::QualifiedC { name, .. } => self
                .qualified_object(name)
                .and_then(|object| object.array_shape.clone()),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self
                .names
                .global_array_shapes
                .get(name)
                .map(|array| array.shape.clone()),
            _ => None,
        };
        let mut postfixes = 0;
        loop {
            if self.certificate_operand_boundary && self.peek() == Some(&Token::LParen) {
                return Ok(expression);
            }

            if !matches!(
                self.peek(),
                Some(Token::LBracket | Token::Arrow | Token::Dot | Token::LParen)
            ) {
                return Ok(expression);
            }
            self.check_expression_chain_limit(postfixes)?;
            postfixes += 1;
            match self.peek() {
                Some(Token::LParen) => {
                    self.position += 1;
                    let mut arguments = Vec::new();
                    if self.peek() != Some(&Token::RParen) {
                        loop {
                            arguments.push(self.parse_contract_expression()?);
                            if self.peek() != Some(&Token::Comma) {
                                break;
                            }
                            self.position += 1;
                        }
                    }
                    self.expect(Token::RParen)?;
                    expression = ContractExpression::Apply {
                        function: Box::new(expression),
                        arguments,
                    };
                    struct_name = None;
                }
                // A slice parameter is a pointer and a length; its subslice
                // is the method on the slice value it stands for.
                Some(Token::LBracket)
                    if self.contract_bracket_is_range()
                        && let Some(slice) = self.slice_parameter_value(&expression) =>
                {
                    expression = self.parse_method_index(slice)?;
                }
                // An index or range index on a value of a Click type is a
                // method, resolved by the receiver's type.
                Some(Token::LBracket) if self.is_click_valued_receiver(&expression) => {
                    expression = self.parse_method_index(expression)?;
                }
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
                        let base = contract_expression_as_program_expression(&expression)
                            .ok_or_else(|| {
                                self.error(
                                    "struct array indexing is only supported on current C fragments",
                                )
                            })?;
                        let source_index = index.clone();
                        let index =
                            contract_expression_as_program_expression(&index).ok_or_else(|| {
                                self.error("struct array indices must be current C expressions")
                            })?;
                        let mut indexes = vec![source_index];
                        while struct_array_shape.is_some() && self.peek() == Some(&Token::LBracket)
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            contract_expression_as_program_expression(&next_index).ok_or_else(
                                || self.error("struct array indices must be current C expressions"),
                            )?;
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
                                        contract_expression_as_program_expression(index)
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
                                let address = ProgramExpression::Add(
                                    Box::new(struct_byte_base(base)),
                                    Box::new(stride),
                                );
                                if matches!(self.peek(), Some(Token::Arrow | Token::Dot)) {
                                    address
                                } else {
                                    // A bare struct subscript retains the legacy
                                    // first-word read; a following field uses the
                                    // byte-scaled address of the whole element.
                                    ProgramExpression::TypedLoad {
                                        pointer: Box::new(address),
                                        value_type: crate::kernel::ProgramType::Int32,
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
                        contract_expression_as_program_expression(&index).ok_or_else(|| {
                            self.error("struct array indices must be current C expressions")
                        })?;
                        let mut indexes = vec![index.clone()];
                        while self.peek() == Some(&Token::LBracket)
                            && !self.contract_bracket_is_range()
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            contract_expression_as_program_expression(&next_index).ok_or_else(
                                || self.error("struct array indices must be current C expressions"),
                            )?;
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
                                    contract_expression_as_program_expression(index)
                                        .expect("validated C index")
                                })
                                .collect(),
                            &shape,
                        );
                        // Keep the source rank of a multidimensional field
                        // access, as a global array access does: the
                        // flattened index alone prints as one subscript,
                        // which does not parse back.
                        expression = match contract_expression_as_program_expression(&expression) {
                            Some(lowered_base) if indexes.len() > 1 => {
                                ContractExpression::ArrayIndex {
                                    base: Box::new(expression),
                                    indexes,
                                    dimensions: shape.clone(),
                                    lowered: ProgramExpression::Index(
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
                                                Box::new(ContractExpression::ProgramExpression(
                                                    ProgramExpression::Value(int32(stride)),
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
                        contract_expression_as_program_expression(&index).ok_or_else(|| {
                            self.error("global array indices must be current C expressions")
                        })?;
                        let mut indexes = vec![index.clone()];
                        while self.peek() == Some(&Token::LBracket)
                            && !self.contract_bracket_is_range()
                        {
                            self.position += 1;
                            let next_index = self.parse_contract_expression()?;
                            self.expect(Token::RBracket)?;
                            contract_expression_as_program_expression(&next_index).ok_or_else(
                                || self.error("global array indices must be current C expressions"),
                            )?;
                            indexes.push(next_index);
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error(format!(
                                "multidimensional global array requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let lowered_base = contract_expression_as_program_expression(&expression)
                            .ok_or_else(|| {
                            self.error("global array base must be a current C expression")
                        })?;
                        let offset = flatten_array_indices(
                            indexes
                                .iter()
                                .map(|index| {
                                    contract_expression_as_program_expression(index)
                                        .expect("validated C index")
                                })
                                .collect(),
                            &shape,
                        );
                        expression = ContractExpression::ArrayIndex {
                            base: Box::new(expression),
                            indexes,
                            dimensions: shape.clone(),
                            lowered: ProgramExpression::Index(
                                Box::new(lowered_base),
                                Box::new(offset),
                            ),
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
                    if let ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        crate::kernel::BindingName::Named(owner),
                    )) = &expression
                        && self.peek() == Some(&Token::Dot)
                        && self.names.ended_instance_names.contains(owner)
                        && !self.names.is_bound(owner)
                    {
                        return Err(self.unknown_instance(owner, "resource instance"));
                    }
                    if let ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        crate::kernel::BindingName::Named(owner),
                    )) = &expression
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
                    // A method on a value of a Click type, resolved by the
                    // receiver's type during declaration expansion.
                    if self.peek() == Some(&Token::Dot)
                        && self.is_click_valued_receiver(&expression)
                        && matches!(self.tokens.get(self.position + 1), Some(Token::Ident(_)))
                        && self.tokens.get(self.position + 2) == Some(&Token::LParen)
                    {
                        self.position += 1;
                        let method = self.expect_ident("method name")?;
                        let arguments = self.parse_method_arguments()?;
                        expression = ContractExpression::MethodCall {
                            receiver: Box::new(expression),
                            method,
                            arguments,
                        };
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
                        } => contract_expression_as_program_expression(inner),
                        _ => contract_expression_as_program_expression(&expression),
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
                                .filter(|_| field.interface_type.is_pointer()),
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
                                .filter(|_| field.interface_type.is_pointer()),
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

    /// The fields and elements read through `R.parameter(name)`. The
    /// parameter's layout is the one the call binds, so its fields are
    /// resolved when the read is lowered at the call's parameter point; the
    /// chain keeps them by name. Its `lowered` form names no C object, so a
    /// lowering that bypasses that resolution refuses it.
    fn parse_region_parameter_suffix(
        &mut self,
        mut expression: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let unresolved = |expression: &ContractExpression| {
            ProgramExpression::Variable(
                format!(
                    "<{} read at its call>",
                    crate::surface::diagnostics::describe_contract_expression(expression)
                )
                .into(),
            )
        };
        loop {
            match self.peek() {
                Some(Token::Dot) => {
                    self.position += 1;
                    let field = self.expect_field_name()?;
                    let lowered = unresolved(&expression);
                    expression = ContractExpression::Field {
                        pointee_struct: None,
                        base: Box::new(expression),
                        field,
                        lowered,
                        offset_bytes: 0,
                    };
                }
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_contract_expression()?;
                    self.expect(Token::RBracket)?;
                    expression = ContractExpression::Index(Box::new(expression), Box::new(index));
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
                        bindings.push(self.expect_surface_binder("match pattern binding")?);
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
                .filter_map(|binding| binding.written().map(str::to_owned))
                .filter(|binding| {
                    self.names
                        .insert(NameKind::ContractBinding, (*binding).clone())
                })
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

    /// Whether a `<region>.result` starts here: a `statement(...)` or
    /// `region(N)` region followed by `.result`. Read ahead only.
    fn looks_like_region_result(&mut self) -> bool {
        if !matches!(self.peek_ident(), Some("statement" | "region" | "call"))
            || self.peek_next() != Some(&Token::LParen)
        {
            return false;
        }
        let start = self.position;
        let found = self.parse_code_region_ref().is_ok()
            && self.peek() == Some(&Token::Dot)
            && matches!(self.peek_next(), Some(Token::Ident(name)) if name == "result" || name == "allocation" || name == "parameter");
        self.position = start;
        found
    }

    /// A source literal object: `f.string_literal(i)` or `"file.c"::f.string_literal(i)`.
    fn take_string_literal_reference(&mut self) -> Result<Option<ContractExpression>, ClickError> {
        let start = self.position;
        let first = match self.peek() {
            Some(Token::Ident(name)) => (false, name.clone()),
            Some(Token::String(name)) => (true, name.clone()),
            _ => return Ok(None),
        };
        self.position += 1;
        let (source, function) = if self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            let Some(Token::Ident(function)) = self.peek() else {
                self.position = start;
                return Ok(None);
            };
            let function = function.clone();
            self.position += 1;
            let source = if first.0 {
                first.1.clone()
            } else {
                // An explicit source alias uses the same qualification as C objects.
                match self.source_aliases.get(&first.1) {
                    Some(source) => source.clone(),
                    None => {
                        self.position = start;
                        return Ok(None);
                    }
                }
            };
            (Some(source), function)
        } else {
            if first.0 {
                self.position = start;
                return Ok(None);
            }
            if let Some((alias, name)) = first.1.split_once("::") {
                let Some(source) = self.source_aliases.get(alias).cloned() else {
                    self.position = start;
                    return Ok(None);
                };
                (Some(source), name.to_string())
            } else {
                (None, first.1.clone())
            }
        };
        if self.peek() != Some(&Token::Dot)
            || self.peek_next() != Some(&Token::Ident("string_literal".into()))
        {
            self.position = start;
            return Ok(None);
        }
        self.position += 2;
        self.expect(Token::LParen)?;
        let ordinal = self.expect_index("string literal ordinal")?;
        self.expect(Token::RParen)?;
        let source = if source.is_some() {
            source
        } else {
            let owners = self.string_literal_owners.get(&function).ok_or_else(|| {
                self.error(format!("C function `{function}` has no string literals"))
            })?;
            if owners.len() != 1 {
                return Err(self.error(format!(
                    "literal owner `{function}` is ambiguous; qualify its C source"
                )));
            }
            owners.first().expect("registered owner").clone()
        };
        let mut id = crate::kernel::StringLiteralId::new(
            function,
            u32::try_from(ordinal).map_err(|_| self.error("string literal ordinal exceeds u32"))?,
        );
        if let Some(source) = source {
            id = id.with_source(source);
        }
        let value = self
            .string_literal_values
            .get(&id)
            .ok_or_else(|| self.error(format!("unknown string literal `{id}`")))?;
        Ok(Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(value.clone()),
        )))
    }

    fn finish_static_reference(
        &mut self,
        query: crate::kernel::StaticBindingId,
    ) -> Result<ContractExpression, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        let id = self
            .local_bindings
            .statics
            .get_key_value(&query)
            .map(|(id, _)| id.clone())
            .ok_or_else(|| self.error(format!("unknown C static declaration `{query}`")))?;
        if self.peek() == Some(&Token::Dot)
            && self.peek_next() == Some(&Token::Ident("storage".into()))
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
        {
            self.position += 2;
            self.expect(Token::LParen)?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::typed_pointer(
                    crate::kernel::Address {
                        base: crate::kernel::AddressBase::StaticObject { binding: id },
                        offset: crate::kernel::AddressOffset::Constant(0),
                    },
                    ProgramType::UInt8Pointer,
                )),
            ));
        }
        Ok(ContractExpression::ProgramExpression(
            ProgramExpression::Variable(id.into()),
        ))
    }

    fn take_local_binding_reference(&mut self) -> Result<Option<ContractExpression>, ClickError> {
        let start = self.position;
        let first = match self.peek() {
            Some(Token::Ident(name)) => (false, name.clone()),
            Some(Token::String(name)) => (true, name.clone()),
            _ => return Ok(None),
        };
        self.position += 1;
        let (source, function) = if self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            let Some(Token::Ident(function)) = self.peek() else {
                self.position = start;
                return Ok(None);
            };
            let function = function.clone();
            self.position += 1;
            let source = if first.0 {
                first.1.clone()
            } else {
                // An explicit source alias uses the same qualification as C objects.
                match self.source_aliases.get(&first.1) {
                    Some(source) => source.clone(),
                    None => {
                        self.position = start;
                        return Ok(None);
                    }
                }
            };
            (Some(source), function)
        } else {
            if first.0 {
                self.position = start;
                return Ok(None);
            }
            if let Some((alias, name)) = first.1.split_once("::") {
                let Some(source) = self.source_aliases.get(alias).cloned() else {
                    self.position = start;
                    return Ok(None);
                };
                (Some(source), name.to_string())
            } else {
                (None, first.1.clone())
            }
        };
        // A file owns its static declarations directly; a function's statics
        // use the same tree selector as its parameters and automatic locals.
        if function == "static" && self.peek() == Some(&Token::LParen) {
            self.position += 1;
            let source = if source.is_some() {
                source
            } else {
                if self.local_bindings.static_files.len() != 1 {
                    return Err(self.error("file-static owner is ambiguous; qualify its C source"));
                }
                self.local_bindings
                    .static_files
                    .first()
                    .expect("one file-static owner")
                    .clone()
            };
            let ordinal = u32::try_from(self.expect_index("static declaration ordinal")?)
                .map_err(|_| self.error("static declaration ordinal exceeds u32"))?;
            self.expect(Token::RParen)?;
            let query = crate::kernel::StaticBindingId::new(
                crate::kernel::StaticBindingOwner::File(source),
                ordinal,
                String::new(),
            );
            return self.finish_static_reference(query).map(Some);
        }
        if self.peek() == Some(&Token::Dot)
            && self.peek_next() == Some(&Token::Ident("static".into()))
        {
            self.position += 2;
            self.expect(Token::LParen)?;
            let source = if source.is_some() {
                source
            } else {
                let owners = self.local_bindings.owners.get(&function).ok_or_else(|| {
                    self.error(format!("unknown C declaration owner `{function}`"))
                })?;
                if owners.len() != 1 {
                    return Err(self.error(format!(
                        "declaration owner `{function}` is ambiguous; qualify its C source"
                    )));
                }
                owners.first().expect("one declaration owner").clone()
            };
            let ordinal = u32::try_from(self.expect_index("static declaration ordinal")?)
                .map_err(|_| self.error("static declaration ordinal exceeds u32"))?;
            self.expect(Token::RParen)?;
            let query = crate::kernel::StaticBindingId::new(
                crate::kernel::StaticBindingOwner::Function(crate::kernel::LocalFunctionId::new(
                    source, function,
                )),
                ordinal,
                String::new(),
            );
            return self.finish_static_reference(query).map(Some);
        }
        let mut path = Vec::new();
        while self.peek() == Some(&Token::Dot)
            && self.peek_next() == Some(&Token::Ident("statement".into()))
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
        {
            self.position += 2;
            self.expect(Token::LParen)?;
            path.push(
                u32::try_from(self.expect_index("statement ordinal")?)
                    .map_err(|_| self.error("statement ordinal exceeds u32"))?,
            );
            self.expect(Token::RParen)?;
        }
        if self.tokens.get(self.position + 2) != Some(&Token::LParen) {
            self.position = start;
            return Ok(None);
        }
        let parameter = match (self.peek(), self.peek_next()) {
            (Some(Token::Dot), Some(Token::Ident(selector))) if selector == "local" => false,
            (Some(Token::Dot), Some(Token::Ident(selector)))
                if selector == "parameter" && path.is_empty() =>
            {
                true
            }
            _ => {
                self.position = start;
                return Ok(None);
            }
        };
        // A code region's existing `.parameter(name)` names a by-value
        // call copy. Numeric declaration selectors use a separate grammar.
        if parameter && !matches!(self.tokens.get(self.position + 3), Some(Token::Number(_))) {
            self.position = start;
            return Ok(None);
        }
        self.position += 2;
        self.expect(Token::LParen)?;
        let source = if source.is_some() {
            source
        } else {
            let owners =
                self.local_bindings.owners.get(&function).ok_or_else(|| {
                    self.error(format!("unknown C declaration owner `{function}`"))
                })?;
            if owners.len() != 1 {
                return Err(self.error(format!(
                    "declaration owner `{function}` is ambiguous; qualify its C source"
                )));
            }
            owners
                .first()
                .expect("registered declaration owner")
                .clone()
        };
        let id = if path.is_empty() {
            let ordinal = u32::try_from(self.expect_index("declaration ordinal")?)
                .map_err(|_| self.error("declaration ordinal exceeds u32"))?;
            let owner = crate::kernel::LocalFunctionId::new(source, function);
            let query = crate::kernel::LocalBindingId::new(owner, parameter, ordinal, None);
            self.local_bindings
                .declarations
                .get_key_value(&query)
                .map(|(id, _)| id.clone())
                .ok_or_else(|| self.error(format!("unknown C declaration `{query}`")))?
        } else {
            let name = self.expect_ident("local declaration name")?;
            self.local_bindings
                .sites
                .get(&(source, function.clone(), path, name.clone()))
                .cloned()
                .ok_or_else(|| {
                    self.error(format!(
                        "statement of `{function}` does not declare local `{name}`"
                    ))
                })?
        };
        self.expect(Token::RParen)?;
        if self.peek() == Some(&Token::Dot)
            && self.peek_next() == Some(&Token::Ident("storage".into()))
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
        {
            self.position += 2;
            self.expect(Token::LParen)?;
            let kind = self.expect_ident("storage instance kind")?;
            let instance = match kind.as_str() {
                "implicit" => crate::kernel::LocalStorageInstance::Implicit,
                "parameter" => crate::kernel::LocalStorageInstance::ValueParameter,
                "lifetime" | "frame" => {
                    self.expect(Token::Comma)?;
                    let number = self.expect_index("storage instance number")? as u64;
                    if kind == "lifetime" {
                        crate::kernel::LocalStorageInstance::Lifetime(number)
                    } else {
                        crate::kernel::LocalStorageInstance::Frame(number)
                    }
                }
                _ => {
                    return Err(self.error(
                        "storage kind must be `implicit`, `parameter`, `lifetime` or `frame`",
                    ));
                }
            };
            self.expect(Token::RParen)?;
            return Ok(Some(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::typed_pointer(
                    crate::kernel::Address {
                        base: crate::kernel::AddressBase::AutomaticLocal {
                            binding: id,
                            instance,
                        },
                        offset: crate::kernel::AddressOffset::Constant(0),
                    },
                    ProgramType::UInt8Pointer,
                )),
            )));
        }
        Ok(Some(ContractExpression::ProgramExpression(
            ProgramExpression::Variable(id.into()),
        )))
    }

    fn parse_contract_primary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.peek_ident() == Some("binder") && self.peek_next() == Some(&Token::LParen) {
            return Ok(self.expect_surface_binder("binder reference")?.reference());
        }
        if let Some(binding) = self.take_local_binding_reference()? {
            return Ok(binding);
        }
        if let Some(literal) = self.take_string_literal_reference()? {
            return Ok(literal);
        }
        let start = self.position;
        if let Ok(region) = self.parse_code_region_ref()
            && self.peek() == Some(&Token::Dot)
            && matches!(self.peek_next(), Some(Token::Ident(name)) if name == "footprint")
        {
            self.position += 2;
            return Ok(ContractExpression::Resource(Box::new(
                ResourceSubject::Footprint(region),
            )));
        }
        self.position = start;
        // A loop's pass count past the loop, `loop(i).iterations`: a proof
        // Integer the path's recorded exit of that loop binds.
        if let Ok(CodeRegionRef::Loop(index)) = self.parse_code_region_ref()
            && self.peek() == Some(&Token::Dot)
            && matches!(self.peek_next(), Some(Token::Ident(name)) if name == "iter")
        {
            self.position += 2;
            if let Some(expression) = self.take_rust_iterator_method("iter", Some(index))? {
                return Ok(expression);
            }
            return Err(self.error(format!(
                "`loop({index}).iter` is read through one of Rust's accessors, such as `loop({index}).iter.len()`"
            )));
        }
        self.position = start;
        if let Ok(CodeRegionRef::Loop(index)) = self.parse_code_region_ref()
            && self.peek() == Some(&Token::Dot)
            && matches!(self.peek_next(), Some(Token::Ident(name)) if name == crate::surface::LOOP_ITERATIONS_NAME)
        {
            self.position += 2;
            return Ok(ContractExpression::Binding(
                crate::surface::loop_iterations_spelling(index),
            ));
        }
        self.position = start;
        // A proof may need the previous binding of a name shadowed by an
        // introduced quantifier. Keep the qualification on the variable name
        // until the proof scope substitutes its checked binder identity.
        if self.proof_nesting > 0
            && self.peek_ident() == Some("outer")
            && self.peek_next() == Some(&Token::Dot)
            // A source record named `outer` still has ordinary field
            // accesses in proofs, including expanded postconditions.
            && !self.names.struct_params.contains_key("outer")
            && !self.names.struct_params.contains_key("&outer")
            && !self.names.aggregate_objects.contains_key("outer")
        {
            let start = self.position;
            let mut depth = 0;
            while self.peek_ident() == Some("outer") && self.peek_next() == Some(&Token::Dot) {
                self.position += 2;
                depth += 1;
            }
            if let Some(name) = self.peek_ident().map(str::to_string) {
                self.position += 1;
                return Ok(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(
                        format!("{}{}", "outer.".repeat(depth), name).into(),
                    ),
                ));
            }
            self.position = start;
        }
        if self.is_qualified_program_name() {
            let (name, lowered) = self.parse_qualified_program_name()?;
            return Ok(ContractExpression::QualifiedC { name, lowered });
        }
        // Region values sit beside their `entry` and `exit` points: `.result`
        // is the returned value; `.allocation` is the fresh heap identity.
        if self.looks_like_region_result() {
            let region = self.parse_code_region_ref()?;
            let allocation = self.peek_next() == Some(&Token::Ident("allocation".to_string()));
            let parameter = self.peek_next() == Some(&Token::Ident("parameter".to_string()));
            self.position += 2;
            // `.parameter(name)` is a call's copy of a by-value aggregate
            // argument: an object whose layout the call bound.
            if parameter {
                self.expect(Token::LParen)?;
                let name = self.expect_ident("parameter name")?;
                self.expect(Token::RParen)?;
                return Ok(ContractExpression::RegionParameter { region, name });
            }
            return Ok(if allocation {
                ContractExpression::RegionAllocation(region)
            } else {
                ContractExpression::RegionResult(region)
            });
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
        // Exact outcome storage identities. Naming one grants no access rights.
        if matches!(self.peek_ident(), Some("result" | "exception"))
            && self.tokens.get(self.position + 1) == Some(&Token::Dot)
            && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(name)) if name == "storage")
            && self.tokens.get(self.position + 3) == Some(&Token::LParen)
        {
            let exceptional = self.peek_ident() == Some("exception");
            self.position += 4;
            let block = if exceptional {
                crate::kernel::AddressBase::ContractException
            } else if self.peek() == Some(&Token::RParen) {
                crate::kernel::AddressBase::ContractResult
            } else {
                let kind = self.expect_ident("return storage kind `frame`")?;
                if kind != "frame" {
                    return Err(self.error("return storage kind must be `frame`"));
                }
                self.expect(Token::Comma)?;
                let frame = self.expect_u64("return storage frame")?;
                crate::kernel::AddressBase::AggregateReturn { frame }
            };
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::typed_pointer(
                    crate::kernel::Address {
                        base: block,
                        offset: crate::kernel::AddressOffset::Constant(0),
                    },
                    ProgramType::UInt8Pointer,
                )),
            ));
        }

        if self.peek_next() == Some(&Token::LParen) {
            match self.peek_ident() {
                Some("float32_from_bits") => return self.parse_float_bits(32),
                Some("float64_from_bits") => return self.parse_float_bits(64),
                _ => {}
            }
        }
        if self.peek_ident() == Some("prop") && self.peek_next() == Some(&Token::LBrace) {
            self.position += 2;
            let proposition = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            return Ok(ContractExpression::Proposition(Box::new(proposition)));
        }
        if self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let mut parameters = Vec::new();
            let mut bound = BTreeSet::new();
            if self.peek() != Some(&Token::Pipe) {
                loop {
                    let name = self.expect_surface_binder("lambda parameter name")?;
                    self.refuse_bool_literal_binder(&name)?;
                    if !bound.insert(name.clone()) {
                        return Err(self.error(format!("duplicate lambda parameter `{name}`")));
                    }
                    self.expect(Token::Colon)?;
                    let (click_type, _) = self.parse_click_type()?;
                    parameters.push((name, click_type));
                    if self.peek() != Some(&Token::Comma) {
                        break;
                    }
                    self.position += 1;
                }
            }
            self.expect(Token::Pipe)?;
            self.expect(Token::Arrow)?;
            let (result, _) = self.parse_click_type()?;
            self.expect(Token::LBrace)?;
            let previous_bool = std::mem::replace(&mut self.bool_value_context, false);
            let previous_integer = std::mem::replace(
                &mut self.integer_literal_context,
                result == ClickType::Integer,
            );
            let scope = self.names.scope();
            let mut shadowed = Vec::new();
            for (name, ty) in &parameters {
                self.names.set_scoped(NameKind::ContractBinding, name, true);
                self.names
                    .set_scoped(NameKind::IntegerParameter, name, *ty == ClickType::Integer);
                self.names.set_scoped(NameKind::IntegerLet, name, false);
                self.names.set_scoped_struct_param(name, None);
                shadowed.push(self.bind_let_operand(name, Some(ty), None));
            }
            let body = if result == ClickType::Proposition {
                self.parse_proposition()
                    .map(|body| ContractExpression::Proposition(Box::new(body)))
            } else {
                self.parse_branch_value(result == ClickType::Program(InterfaceType::Bool))
                    .and_then(|body| match &result {
                        ClickType::Integer => Ok(self.at_integer_position(body)),
                        ClickType::Program(ty) => {
                            self.typed_let_literal("lambda result", *ty, body)
                        }
                        _ => Ok(body),
                    })
            };
            self.unbind_let_operands(shadowed);
            self.names.end(scope);
            self.bool_value_context = previous_bool;
            self.integer_literal_context = previous_integer;
            let body = body?;
            self.expect(Token::RBrace)?;
            super::lambdas::validate_body_state(&body)?;
            return Ok(ContractExpression::Lambda {
                parameters,
                result,
                body: Box::new(body),
            });
        }

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
            let arguments = self.observe_integer_fields(&algebraic_type.name, &variant, arguments);
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
                if parsed_type.interface_type == InterfaceType::Void {
                    return Err(self.error("`sizeof(void)` is not supported"));
                }
                if let InterfaceType::Parameter(_) = parsed_type.interface_type {
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
                    _ => parsed_type.interface_type.abi_size_bytes(),
                }
            };
            return Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(int32(bytes)),
            ));
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
            self.refuse_result_in_program_point_expression(None, &expression)?;
            return Ok(ContractExpression::Old(Box::new(expression)));
        }

        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let selector = self.parse_program_point_selector()?;
            self.expect(Token::Comma)?;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            self.refuse_result_in_program_point_expression(Some(&selector), &expression)?;
            return Ok(ContractExpression::At {
                selector,
                expression: Box::new(expression),
            });
        }

        // `program::name` names the verified program's binding `name`, as the
        // program itself resolves it at this point, where a Click name has the
        // same spelling (`result`, `iterations`). The form is the same in every
        // source language.
        if self.peek_ident() == Some("program")
            && self.peek_next() == Some(&Token::ColonColon)
            && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_)))
        {
            self.position += 2;
            let name = self.expect_ident("program binding name")?;
            self.refuse_unknown_loop_value(&name)?;
            return Ok(ContractExpression::ProgramBinding(name));
        }
        // The earlier language-named forms are refused with their replacement.
        if matches!(self.peek_ident(), Some("c" | "rust"))
            && self.peek_next() == Some(&Token::LParen)
            && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(_)))
            && self.tokens.get(self.position + 3) == Some(&Token::RParen)
            && !matches!(
                self.peek_ident()
                    .and_then(|name| self.specification_binding_kind(name)),
                Some(spec_arithmetic::SpecificationBinding::Function { .. })
            )
        {
            let (Some(Token::Ident(form)), Some(Token::Ident(name))) = (
                self.tokens.get(self.position),
                self.tokens.get(self.position + 2),
            ) else {
                unreachable!("checked above");
            };
            return Err(self.error(format!(
                "`{form}({name})` is no longer Click syntax: a program binding is `program::{name}`"
            )));
        }

        if self.peek_ident() == Some("address") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let pointer = self.parse_contract_expression()?;
            let source_pointer = pointer;
            // As with numeric casts, the contract operand supplies the value.
            // Saved reads and named call results need not have a current C AST.
            let pointer = contract_expression_as_program_expression(&source_pointer)
                .unwrap_or(ProgramExpression::Value(int32(0)));
            self.expect(Token::RParen)?;
            let cast = ProgramExpression::Cast {
                expression: Box::new(pointer),
                target_type: ProgramType::UInt64,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            };
            self.address_casts.insert(cast.clone());
            // Preserve the canonical C form for ordinary names (alignment
            // recognition and stored-origin inference use it). Historical and
            // constructed operands retain their authoritative Surface operand.
            if matches!(
                &source_pointer,
                ContractExpression::Binding(_)
                    | ContractExpression::ProgramBinding(_)
                    | ContractExpression::ProgramExpression(_)
                    | ContractExpression::QualifiedC { .. }
            ) {
                return Ok(crate::surface::lowering::contract_c_unary(
                    source_pointer,
                    cast,
                ));
            }
            return Ok(ContractExpression::CUnary {
                operand: Box::new(source_pointer),
                lowered: cast,
            });
        }

        if self.peek_ident() == Some("byte_offset") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let source_pointer = self.parse_contract_expression()?;
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
            let lowered = |pointer| ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(pointer),
                bytes,
            };
            return Ok(
                match contract_expression_as_program_expression(&source_pointer) {
                    Some(pointer) => {
                        crate::surface::lowering::contract_c_unary(source_pointer, lowered(pointer))
                    }
                    None => ContractExpression::CUnary {
                        operand: Box::new(source_pointer),
                        lowered: lowered(ProgramExpression::Value(int32(0))),
                    },
                },
            );
        }

        let typed_load = typed_load_type_from_name(self.peek_ident());
        if self.peek_next() == Some(&Token::LParen)
            && let Some(value_type) = typed_load
        {
            self.position += 2;
            let pointer = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            let source_pointer = pointer.clone();
            if let Some(pointer) = contract_expression_as_program_expression(&pointer) {
                return Ok(crate::surface::lowering::contract_c_unary(
                    source_pointer,
                    ProgramExpression::TypedLoad {
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
            // the surrounding clause's memory state.
            let pointer = ProgramExpression::Value(int32(0));
            return Ok(ContractExpression::CUnary {
                operand: Box::new(source_pointer),
                lowered: ProgramExpression::TypedLoad {
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
            if self.names.contains(NameKind::ContractBinding, &name)
                || matches!(
                    self.specification_binding_kind(&name),
                    Some(spec_arithmetic::SpecificationBinding::Function { .. })
                )
            {
                return Ok(ContractExpression::Apply {
                    function: Box::new(ContractExpression::Binding(name)),
                    arguments,
                });
            }
            let call = ContractExpression::Call {
                name: name.clone(),
                arguments,
            };
            if self.peek() == Some(&Token::Dot) && self.declared_resource_fields.contains_key(&name)
            {
                let target = self
                    .names
                    .resource_targets
                    .select(&call)
                    .map_err(|()| {
                        self.error(format!(
                            "resource selector `{}` is ambiguous; use an instance name",
                            crate::surface::diagnostics::describe_contract_expression(&call)
                        ))
                    })?
                    .ok_or_else(|| {
                        self.error(format!(
                            "resource selector `{}` has no instance in scope",
                            crate::surface::diagnostics::describe_contract_expression(&call)
                        ))
                    })?;
                let ResourceClause::Named { binding, .. } = target else {
                    unreachable!()
                };
                let identity = binding.identity;
                let mut path = Vec::new();
                while self.peek() == Some(&Token::Dot) {
                    self.position += 1;
                    path.push(self.expect_ident("resource child or field name")?);
                }
                // Hidden records retain a flat schema key such as first.v.
                // This selects that exact slot, without opening the child.
                return Ok(ContractExpression::ResourceField(ResourceFieldAccess {
                    owner: crate::surface::diagnostics::describe_contract_expression(&call),
                    resource_name: name,
                    identity,
                    children: vec![],
                    field: path.join("."),
                    field_index: 0,
                    click_type: None,
                }));
            }
            return Ok(call);
        }

        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected contract expression, got `by`"))
            }
            Some(Token::Ident(name)) => {
                if let Some(field) = self.names.resource_fields.get(&name) {
                    return Ok(ContractExpression::ResourceField(field.clone()));
                }
                // Inside a loop, `iter` is the loop's iterator, read through
                // its accessors, even where the function has a local of
                // that name, which is `program::iter`.
                if name == "iter"
                    && let Some(expression) = self.take_rust_iterator_method(&name, None)?
                {
                    return Ok(expression);
                }
                if self.names.contains_any(NameKind::VALUES, &name) || self.specification_binding_kind(&name).is_some()
                {
                    Ok(ContractExpression::Binding(name))
                } else {
                    match self.names.algebraic_params.get(&name) {
                        Some((algebraic_type, binder_index)) => {
                            Ok(ContractExpression::AlgebraicVariable {
                                name: name.into(),
                                algebraic_type: algebraic_type.clone(),
                                binder_index: *binder_index,
                            })
                        }
                        None => match self.bool_literal_spelling(&name) {
                            Some(value) => Ok(bool_literal(value)),
                            None => self.c_variable_expression(name),
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
            Some(Token::UInt8Number(value)) => Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(crate::kernel::uint8(u32::from(value))),
            )),
            Some(Token::UInt32Number(value)) => Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::uint32_constant(value))),
            )),
            Some(Token::Int64MinimumMagnitude) => Err(self.error(
                "positive int64 literal `9223372036854775808i64` is outside 0..9223372036854775807; this magnitude is allowed only after unary minus",
            )),
            Some(Token::Int64Number(value)) => Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::Int64(MachineTerm::int64_constant(value))),
            )),
            Some(Token::UInt64Number(value)) => Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(value))),
            )),
            Some(Token::CharLiteral(value)) => Ok(ContractExpression::ProgramExpression(
                ProgramExpression::Value(self.character_constant_value(value)?),
            )),
            Some(Token::LParen) => {
                let start = self.position;
                let boundary = std::mem::replace(&mut self.certificate_operand_boundary, false);
                let expression = self.parse_contract_expression();
                self.certificate_operand_boundary = boundary;
                let expression = expression?;
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
                if self.peek() == Some(&Token::Colon) {
                    self.position += 1;
                    let (ty, _) = self.parse_click_type()?;
                    if ty != ClickType::Integer {
                        return Err(self.error("expression type context currently requires `Integer`"));
                    }
                    self.expect(Token::RParen)?;
                    return Ok(ContractExpression::IntegerContext(Box::new(self.at_integer_position(expression))));
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
        if self.tokens.get(self.position + 1) == Some(&Token::Ident("binder".into()))
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
        {
            self.expect_ident_spelling("let")?;
            let name = self.expect_surface_binder("let binding")?;
            let click_type = if self.peek() == Some(&Token::Colon) {
                self.position += 1;
                Some(self.parse_click_type()?.0)
            } else {
                None
            };
            self.expect(Token::Equal)?;
            let previous_integer = std::mem::replace(
                &mut self.integer_literal_context,
                click_type == Some(ClickType::Integer),
            );
            let value = self.parse_contract_expression();
            self.integer_literal_context = previous_integer;
            let value = value?;
            let value = match &click_type {
                Some(ClickType::Integer) => self.at_integer_position(value),
                Some(ClickType::Program(ty)) => {
                    self.typed_let_literal("generated binder", *ty, value)?
                }
                _ => value,
            };
            self.expect(Token::Semicolon)?;
            let shadowed = self.bind_let_operand(&name, click_type.as_ref(), Some(&value));
            let body = self.parse_branch_value(self.bool_value_context);
            self.unbind_let_operands(vec![shadowed]);
            return Ok(ContractExpression::Let {
                name,
                click_type,
                value: Box::new(value),
                body: Box::new(body?),
            });
        }
        let bool_body = std::mem::take(&mut self.bool_value_context);
        let mut bindings = Vec::new();
        let mut shadowed_lets = Vec::new();
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
            shadowed_lets.push(self.bind_let_operand(
                &binding.name,
                binding.click_type.as_ref(),
                Some(&value),
            ));
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
        self.unbind_let_operands(shadowed_lets);
        for (name, _, _, binding_was_in_scope, previous_integer_context) in bindings.iter().rev() {
            self.integer_literal_context = *previous_integer_context;
            if !*binding_was_in_scope {
                self.names.remove(NameKind::ContractBinding, name);
            }
        }
        let mut body = body?;
        for (name, click_type, value, _, _) in bindings.into_iter().rev() {
            body = ContractExpression::Let {
                name: name.into(),
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

    /// Whether an identifier starts `Name::Variant` or `Name<arguments>::Variant`.
    fn looks_like_algebraic_constructor(&self) -> bool {
        if !matches!(self.peek(), Some(Token::Ident(_))) {
            return false;
        }
        // `program::name` is a program binding, never a datatype's variant.
        if self.peek_ident() == Some("program") {
            return false;
        }
        if self.peek_next() == Some(&Token::ColonColon) {
            return true;
        }
        if self.peek_next() != Some(&Token::LessThan) {
            return false;
        }
        // A type argument list ends before anything that ends the
        // proposition around it, so the scan stops there: an ordinary
        // comparison `x < y` reads only to the end of its own conjunct, not
        // to the end of the file.
        let mut index = self.position + 2;
        let mut nested = 1usize;
        let mut enclosed = 0usize;
        while let Some(token) = self.tokens.get(index) {
            #[cfg(test)]
            CONSTRUCTOR_LOOKAHEAD_TOKENS.with(|count| count.set(count.get() + 1));
            match token {
                Token::LParen | Token::LBracket => enclosed += 1,
                Token::RParen | Token::RBracket if enclosed == 0 => return false,
                Token::RParen | Token::RBracket => enclosed -= 1,
                Token::Semicolon if enclosed == 0 => return false,
                Token::LBrace
                | Token::RBrace
                | Token::FatArrow
                | Token::Equal
                | Token::EqualEqual
                | Token::BangEqual
                | Token::LessEqual
                | Token::GreaterEqual => return false,
                Token::Ident(word)
                    if matches!(
                        word.as_str(),
                        "and" | "or" | "implies" | "by" | "using" | "else" | "if" | "produces"
                    ) =>
                {
                    return false;
                }
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

    /// `&u8` as a type argument in a Rust sidecar: the pointer type of a
    /// shared reference to a scalar. `&[u8]`, a shared slice, is the
    /// library's `Slice<u8>`. Nothing is consumed otherwise.
    fn take_rust_reference_type_argument(&mut self) -> Option<ClickType> {
        if !self.verifies_rust() || self.peek() != Some(&Token::Amp) {
            return None;
        }
        if self.peek_next() == Some(&Token::LBracket)
            && let Some(Token::Ident(element)) = self.tokens.get(self.position + 2)
            && self.tokens.get(self.position + 3) == Some(&Token::RBracket)
        {
            let element = rust_syntax::rust_scalar_type(element)?;
            self.position += 4;
            return Some(ClickType::Algebraic(AlgebraicTypeApplication {
                rigid: false,
                name: "Slice".into(),
                arguments: vec![ClickType::Program(element)],
            }));
        }
        let Some(Token::Ident(pointee)) = self.peek_next() else {
            return None;
        };
        let pointer = match rust_syntax::rust_scalar_type(pointee)? {
            InterfaceType::Int8 => InterfaceType::Int8Pointer,
            InterfaceType::UInt8 => InterfaceType::UInt8Pointer,
            InterfaceType::Int16 => InterfaceType::Int16Pointer,
            InterfaceType::UInt16 => InterfaceType::UInt16Pointer,
            InterfaceType::Int32 => InterfaceType::Int32Pointer,
            InterfaceType::UInt32 => InterfaceType::UInt32Pointer,
            _ => return None,
        };
        self.position += 2;
        Some(ClickType::Program(pointer))
    }

    fn parse_algebraic_type_application_arguments(
        &mut self,
        name: String,
    ) -> Result<AlgebraicTypeApplication, ClickError> {
        self.position += 1;
        let mut arguments = Vec::new();
        loop {
            // A Rust sidecar writes the library's `Option` of a shared
            // reference to a scalar as Rust does, `Option<&u8>`: the item a
            // slice iterator yields. The value is that reference's pointer.
            if let Some(reference) = self.take_rust_reference_type_argument() {
                arguments.push(reference);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        continue;
                    }
                    Some(Token::GreaterThan) => {
                        self.position += 1;
                        break;
                    }
                    Some(Token::ShiftRight) => {
                        self.tokens[self.position] = Token::GreaterThan;
                        break;
                    }
                    _ => return Err(self.error("expected `,` or `>` after datatype argument")),
                }
            }
            let (mut argument, parsed_c_type) = self.parse_click_type()?;
            if let Some(parsed) = parsed_c_type {
                if !algebraic_field_c_type_supported(parsed.interface_type) {
                    return Err(self.error("algebraic datatype arguments must be value types"));
                }
                if parsed.interface_type.is_pointer()
                    && let Some(struct_name) = parsed.struct_name
                {
                    argument = ClickType::CObjectPointer {
                        interface_type: parsed.interface_type,
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

    /// Refuses `result` in a state that precedes the return; see
    /// [`program_point_can_name_result`]. Kept out of the recursive parser frame,
    /// like the other helpers here.
    #[inline(never)]
    fn refuse_result_in_program_point_expression(
        &self,
        selector: Option<&ProgramPointSelector>,
        expression: &ContractExpression,
    ) -> Result<(), ClickError> {
        let mut names = BTreeSet::new();
        collect_current_contract_expression_variables(expression, &mut names);
        self.refuse_result_in_program_point(selector, names.contains("result"))
    }

    #[inline(never)]
    fn refuse_result_in_program_point_proposition(
        &self,
        selector: &ProgramPointSelector,
        proposition: &ClickProposition,
    ) -> Result<(), ClickError> {
        self.refuse_result_in_program_point(Some(selector), proposition_names_result(proposition))
    }

    fn refuse_result_in_program_point(
        &self,
        selector: Option<&ProgramPointSelector>,
        names_result: bool,
    ) -> Result<(), ClickError> {
        if !names_result || program_point_can_name_result(selector) {
            return Ok(());
        }
        let point_form = match selector {
            None => "old(...)".to_string(),
            Some(selector) => format!(
                "at({}, ...)",
                diagnostics::describe_program_point_selector(selector)
            ),
        };
        Err(self.error(format!(
            "`result` cannot be named inside `{point_form}`: that program point precedes the \
             return, where `result` does not exist yet; state the claim about `result` \
             outside that `at` or `old` expression, or at `function.exit`"
        )))
    }

    fn parse_program_point_selector(&mut self) -> Result<ProgramPointSelector, ClickError> {
        if let (Some(Token::Ident(name)), Some(Token::Comma)) = (self.peek(), self.peek_next()) {
            let name = name.clone();
            self.position += 1;
            return Ok(ProgramPointSelector::Mark(name));
        }
        Ok(ProgramPointSelector::ProgramPoint(
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
        // The untyped two-name spelling is contextual lambda sugar.
        // A typed literal or any other expression is an ordinary step value.
        let binder_end = if self.tokens.get(self.position + 1)
            == Some(&Token::Ident("binder".into()))
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
        {
            self.position + 5
        } else {
            self.position + 2
        };
        let untyped_binder = self.peek() == Some(&Token::Pipe)
            && matches!(self.peek_next(), Some(Token::Ident(_)))
            && self.tokens.get(binder_end) == Some(&Token::Comma);
        if !untyped_binder {
            let step = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(lambdas::range_fold(start, end, initial, step));
        }
        self.expect(Token::Pipe)?;
        let accumulator = self.expect_surface_binder("fold accumulator name")?;
        self.expect(Token::Comma)?;
        let item = self.expect_surface_binder("fold item name")?;
        self.expect(Token::Pipe)?;
        let binder_scope = self.loop_proof_value_names.clone();
        if let Some(name) = accumulator.written() {
            self.loop_proof_value_names = self.loop_proof_value_names.with_value(name.to_owned());
        }
        if let Some(name) = item.written() {
            self.loop_proof_value_names = self.loop_proof_value_names.with_value(name.to_owned());
        }
        let body = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let body = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            body
        } else {
            self.parse_contract_expression()?
        };
        self.expect(Token::RParen)?;

        self.loop_proof_value_names = binder_scope;
        Ok(ContractExpression::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        })
    }

    fn parse_ensure_bitwise_or(&mut self) -> Result<CExpression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_xor()?;
        let mut operands = 1;
        while self.peek() == Some(&Token::Pipe) {
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_bitwise_xor()?;
            expression = CExpression::BitwiseOr(Box::new(expression), Box::new(right));
            operands += 1;
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_xor(&mut self) -> Result<CExpression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_and()?;
        let mut operands = 1;
        while self.peek() == Some(&Token::Caret) {
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_bitwise_and()?;
            expression = CExpression::BitwiseXor(Box::new(expression), Box::new(right));
            operands += 1;
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_and(&mut self) -> Result<CExpression, ClickError> {
        let mut expression = self.parse_ensure_shift()?;
        let mut operands = 1;
        while self.peek() == Some(&Token::Amp) {
            self.check_expression_chain_limit(operands)?;
            self.position += 1;
            let right = self.parse_ensure_shift()?;
            expression = CExpression::BitwiseAnd(Box::new(expression), Box::new(right));
            operands += 1;
        }
        Ok(expression)
    }

    fn parse_ensure_shift(&mut self) -> Result<CExpression, ClickError> {
        let mut expression = self.parse_ensure_add()?;
        let mut operands = 1;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    operands += 1;
                    CExpression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    operands += 1;
                    CExpression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_add(&mut self) -> Result<CExpression, ClickError> {
        let mut expression = self.parse_ensure_multiply()?;
        let mut operands = 1;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    operands += 1;
                    CExpression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.check_expression_chain_limit(operands)?;
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    operands += 1;
                    CExpression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_multiply(&mut self) -> Result<CExpression, ClickError> {
        let mut expression = self.parse_ensure_unary()?;
        let mut operands = 1;
        while let Some(operator) = self.peek() {
            let constructor = match operator {
                Token::Star => CExpression::Multiply,
                Token::Slash => CExpression::Divide,
                Token::Percent => CExpression::Remainder,
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

    fn parse_ensure_unary(&mut self) -> Result<CExpression, ClickError> {
        self.parse_ensure_unary_at_depth(0)
    }

    fn parse_ensure_unary_at_depth(&mut self, depth: usize) -> Result<CExpression, ClickError> {
        if self.peek() == Some(&Token::Minus) {
            self.check_unary_nesting_limit(depth)?;
            if let Some((literal, end)) = self.negated_rust_literal() {
                self.position = end;
                return literal
                    .program_expression(true)
                    .map_err(|message| self.error(message));
            }
            if self.peek_next() == Some(&Token::Int64MinimumMagnitude) {
                self.position += 2;
                return Ok(CExpression::Int64Literal(i64::MIN));
            }
            if let Some(value) = self.peek_next().and_then(negatable_int32_magnitude) {
                self.position += 2;
                return Ok(CExpression::Int32Literal(0u32.wrapping_sub(value)));
            }
            self.position += 1;
            return Ok(CExpression::Subtract(
                Box::new(CExpression::Int32Literal(0)),
                Box::new(self.parse_ensure_unary_at_depth(depth + 1)?),
            ));
        }
        if self.peek() == Some(&Token::Tilde) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            return Ok(CExpression::BitwiseNot(Box::new(
                self.parse_ensure_unary_at_depth(depth + 1)?,
            )));
        }
        if self.peek() == Some(&Token::Amp) && self.at_reference_parameter_address() {
            let Some(Token::Ident(name)) = self.peek_next() else {
                unreachable!()
            };
            let carrier = self.reference_binding_carrier(name);
            self.position += 2;
            return Ok(CExpression::Variable((carrier).into()));
        }
        if self.peek() == Some(&Token::Amp) {
            self.check_unary_nesting_limit(depth)?;
            self.position += 1;
            return Ok(CExpression::AddressOf(Box::new(
                self.parse_ensure_unary_at_depth(depth + 1)?,
            )));
        }

        self.parse_ensure_postfix()
    }

    fn parse_ensure_postfix(&mut self) -> Result<CExpression, ClickError> {
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
                    expression = CExpression::Index(Box::new(expression), Box::new(index), None);
                }
                Some(Token::Arrow | Token::Dot) => {
                    self.position += 1;
                    let field_name = self.expect_field_name()?;
                    let base = expression;
                    expression = self
                        .resolve_c_field_load(base.clone(), &field_name)?
                        .unwrap_or_else(|| CExpression::Load(Box::new(base), None));
                }
                _ => unreachable!("postfix expression token checked above"),
            }
        }
    }

    fn parse_ensure_primary(&mut self) -> Result<CExpression, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected result expression, got `by`"))
            }
            Some(Token::Ident(name)) if self.is_reference_binding(&name) => {
                let carrier = self.reference_binding_carrier(&name);
                let is_struct = self.names.struct_params.contains_key(carrier.source_name());
                let carrier = CExpression::Variable((carrier).into());
                Ok(if is_struct {
                    carrier
                } else {
                    CExpression::Index(
                        Box::new(carrier),
                        Box::new(CExpression::Int32Literal(0)),
                        None,
                    )
                })
            }
            Some(Token::Ident(name)) => {
                self.refuse_unknown_loop_value(&name)?;
                let name = self.take_rust_slice_len(&name).unwrap_or(name);
                Ok(CExpression::Variable((name).into()))
            }
            Some(Token::RustInteger(literal)) => literal.program_expression(false).map_err(|message| self.error(message)),
            Some(Token::Number(value)) => Ok(CExpression::Int32Literal(value)),
            Some(Token::UInt8Number(value)) => Ok(CExpression::UInt8Literal(value)),
            Some(Token::UInt32Number(value)) => Ok(CExpression::UInt32Literal(value)),
            Some(Token::Int64MinimumMagnitude) => Err(self.error(
                "positive int64 literal `9223372036854775808i64` is outside 0..9223372036854775807; this magnitude is allowed only after unary minus",
            )),
            Some(Token::Int64Number(value)) => Ok(CExpression::Int64Literal(value)),
            Some(Token::UInt64Number(value)) => Ok(CExpression::UInt64Literal(value)),
            Some(Token::CharLiteral(value)) => Ok(
                match self.character_constant_value(value)? {
                    ProgramValue::Int32(bits32_constant!(bits)) => CExpression::Int32Literal(constant_u32(bits)),
                    _ => CExpression::UInt8Literal(value),
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
                        &operand.to_kernel_expression(), &self.names.program_parameter_types, "contract expression"
                    )?;
                    return Ok(CExpression::Cast {
                        expression: Box::new(operand),
                        interface_type: InterfaceType::VoidPointer,
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
                    return Ok(CExpression::Cast {
                        expression: Box::new(operand),
                        interface_type: InterfaceType::Int32Pointer,
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

    fn expect_surface_binder(&mut self, expected: &str) -> Result<SurfaceBinder, ClickError> {
        if self.peek_ident() == Some("binder") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let number = self.expect_u64("binder identity")?;
            self.expect(Token::RParen)?;
            let id = crate::kernel::GeneratedBinderId::from_spelling(number);
            Ok(SurfaceBinder::Generated(id))
        } else {
            self.expect_ident(expected).map(Into::into)
        }
    }

    fn expect_number(&mut self, expected: &str) -> Result<u32, ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::RustInteger(literal)) => {
                literal
                    .program_expression(false)
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

    fn expect_u64(&mut self, expected: &str) -> Result<u64, ClickError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Number(value)) => Ok(u64::from(value)),
            Some(Token::UnsuffixedUInt64(value) | Token::UInt64Number(value)) => Ok(value),
            Some(Token::UnsuffixedInt64(value) | Token::Int64Number(value)) => u64::try_from(value)
                .map_err(|_| self.error_at(at, format!("expected nonnegative {expected}"))),
            Some(Token::RustInteger(literal)) => {
                literal
                    .program_expression(false)
                    .map_err(|message| self.error_at(at.clone(), message))?;
                literal
                    .digits
                    .parse::<u64>()
                    .map_err(|_| self.error_at(at, format!("expected {expected} to fit in uint64")))
            }
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

    fn starts_float_pointer_cast_at(&self, index: usize) -> bool {
        self.tokens.get(index) == Some(&Token::LParen)
            && matches!(self.tokens.get(index + 1), Some(Token::Ident(name)) if matches!(name.as_str(), "float" | "double"))
            && self.tokens.get(index + 2) == Some(&Token::Star)
            && self.tokens.get(index + 3) == Some(&Token::RParen)
    }

    fn starts_contract_scalar_cast(&self) -> bool {
        if self.peek() != Some(&Token::LParen) {
            return false;
        }
        let mut index = self.position + 1;
        while matches!(self.tokens.get(index), Some(Token::Ident(name)) if matches!(name.as_str(), "const" | "volatile"))
        {
            index += 1;
        }
        match self.tokens.get(index) {
            Some(Token::Ident(name)) if matches!(name.as_str(), "void" | "float" | "double") => {
                (self.tokens.get(index + 1) == Some(&Token::Star)
                    && self.tokens.get(index + 2) == Some(&Token::RParen))
                    || (index == self.position + 1
                        && matches!(name.as_str(), "float" | "double")
                        && self.tokens.get(index + 1) == Some(&Token::RParen))
            }
            Some(Token::Ident(name)) => matches!(
                name.as_str(),
                "int8"
                    | "uint8"
                    | "int16"
                    | "uint16"
                    | "uint32"
                    | "int32"
                    | "uint64"
                    | "int64"
                    | "int128"
                    | "uint128"
            ),
            _ => false,
        }
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
                Token::LParen
                    | Token::EqualEqual
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
        ) || self.starts_cast_at(close + 1)
    }

    /// Whether `as` at `index` begins a cast: `as` and a numeric type name,
    /// or `as (` with a pointer type, so `(a + b) as uint32 == c` reads its
    /// parentheses as an expression.
    fn starts_cast_at(&self, index: usize) -> bool {
        if !matches!(self.tokens.get(index), Some(Token::Ident(name)) if name == "as") {
            return false;
        }
        if self.starts_float_pointer_cast_at(index + 1) {
            return true;
        }
        match self.tokens.get(index + 1) {
            Some(Token::Ident(name)) => {
                rust_syntax::click_numeric_cast_type(name).is_some()
                    || (self.verifies_rust() && rust_syntax::rust_scalar_type(name).is_some())
            }
            Some(Token::LParen) => matches!(
                self.tokens.get(index + 2),
                Some(Token::Ident(name)) if matches!(name.as_str(), "void" | "struct" | "const" | "volatile")
                    || rust_syntax::click_numeric_cast_type(name).is_some()
            ),
            _ => false,
        }
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
    fn character_constant_value(&self, byte: u8) -> Result<ProgramValue, ClickError> {
        if byte < 0x80 {
            return Ok(crate::kernel::uint8(u32::from(byte)));
        }
        match self.plain_char {
            Some(syntax::PlainChar::Unsigned) => {
                Ok(crate::kernel::uint8(u32::from(byte)))
            }
            Some(plain @ syntax::PlainChar::Signed) => Ok(ProgramValue::Int32(MachineTerm::constant(
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

fn typed_load_type_from_name(name: Option<&str>) -> Option<ProgramType> {
    match name {
        Some("load_int32") => Some(ProgramType::Int32),
        Some("load_uint8") => Some(ProgramType::UInt8),
        Some("load_uint16") => Some(ProgramType::UInt16),
        Some("load_uint32") => Some(ProgramType::UInt32),
        Some("load_int64") => Some(ProgramType::Int64),
        Some("load_uint64") => Some(ProgramType::UInt64),
        Some("load_int32_pointer") => Some(ProgramType::Int32Pointer),
        Some("load_uint8_pointer") => Some(ProgramType::UInt8Pointer),
        Some("load_uint16_pointer") => Some(ProgramType::UInt16Pointer),
        Some("load_int32_pointer_pointer") => Some(ProgramType::Int32PointerPointer),
        Some("load_uint8_pointer_pointer") => Some(ProgramType::UInt8PointerPointer),
        Some("load_uint16_pointer_pointer") => Some(ProgramType::UInt16PointerPointer),
        _ => None,
    }
}

fn float_classification_from_name(name: &str) -> Option<syntax::CFloatClassification> {
    match name {
        "isfinite" => Some(syntax::CFloatClassification::Finite),
        "isinf" => Some(syntax::CFloatClassification::Infinite),
        "iszero" => Some(syntax::CFloatClassification::Zero),
        "issubnormal" => Some(syntax::CFloatClassification::Subnormal),
        "isnan" => Some(syntax::CFloatClassification::Nan),
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

fn named_place_base(expression: &ProgramExpression) -> Option<&crate::kernel::BindingName> {
    match expression {
        ProgramExpression::Variable(name) => Some(name),
        ProgramExpression::AddressOf(inner) => match inner.as_ref() {
            ProgramExpression::Variable(name) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

pub(in crate::surface) fn flatten_array_indices(
    indexes: Vec<ProgramExpression>,
    dimensions: &[u32],
) -> ProgramExpression {
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
            ProgramExpression::Multiply(
                Box::new(expression),
                Box::new(ProgramExpression::Value(int32(stride))),
            )
        });
    }
    let mut terms = terms.into_iter();
    let mut offset = terms
        .next()
        .expect("a multidimensional access has at least one index");
    for term in terms {
        offset = ProgramExpression::Add(Box::new(offset), Box::new(term));
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
/// contract's `&p->f`: the address keeps the member's bounds as the C
/// frontend's member address does. The specification lowers the address as
/// one C fragment, so the kernel evaluates the narrowing.
fn contract_member_lvalue(load: &ProgramExpression) -> ProgramExpression {
    let mut load = load.clone();
    if let ProgramExpression::TypedLoad {
        pointer,
        value_type,
        ..
    } = &mut load
    {
        let width = value_type.byte_width();
        if width != 0 {
            let member = std::mem::replace(
                pointer.as_mut(),
                ProgramExpression::Variable((String::new()).into()),
            );
            **pointer = ProgramExpression::Subobject {
                pointer: Box::new(member),
                width,
            };
        }
    }
    load
}

fn lowered_field_expression(
    pointer: ProgramExpression,
    field: &ResolvedField,
) -> ProgramExpression {
    if field.interface_type == InterfaceType::Int32
        && (field.struct_name.is_some() || field.union_name.is_some())
    {
        pointer
    } else {
        ProgramExpression::TypedLoad {
            pointer: Box::new(pointer),
            value_type: field.interface_type.to_kernel_type(),
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
        field.interface_type,
        InterfaceType::Int8
            | InterfaceType::Int16
            | InterfaceType::Int32
            | InterfaceType::Char(_)
            | InterfaceType::UInt8
            | InterfaceType::UInt16
            | InterfaceType::UInt32
            | InterfaceType::Int64(_)
            | InterfaceType::UInt64(_)
            | InterfaceType::Int32Array(_)
            | InterfaceType::Int128Array(_)
            | InterfaceType::Int64Array(_, _)
            | InterfaceType::UInt128Array(_)
            | InterfaceType::UInt64Array(_, _)
            | InterfaceType::CharArray(_, _)
            | InterfaceType::UInt8Array(_)
    )
}

fn scalar_array_field_element(field: &ResolvedField) -> Option<(u32, ProgramType)> {
    if field.struct_name.is_some() || field.union_name.is_some() || field.array_shape.is_none() {
        return None;
    }
    match field.interface_type {
        InterfaceType::Int32Array(_) => Some((4, ProgramType::Int32)),
        InterfaceType::Int64Array(_, _) => Some((8, ProgramType::Int64)),
        InterfaceType::Int128Array(_) => Some((16, ProgramType::Int128)),
        InterfaceType::UInt64Array(_, _) => Some((8, ProgramType::UInt64)),
        InterfaceType::UInt128Array(_) => Some((16, ProgramType::UInt128)),
        InterfaceType::CharArray(plain, _) => Some((1, plain.byte_type().to_kernel_type())),
        InterfaceType::UInt8Array(_) => Some((1, ProgramType::UInt8)),
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
                let preceding = index.checked_sub(1).and_then(|i| tokens.get(i));
                // The outer `both` braces group the labeled arms. Only
                // the arm bodies add proof nesting.
                let both_container = matches!(preceding, Some(Token::Ident(name)) if name == "both")
                    && matches!(tokens.get(index + 1..index + 4),
                        Some([Token::Ident(label), Token::FatArrow, Token::LBrace]) if label == "left");
                // Proof `if` else blocks are read by the iterative spine
                // parser. They retain a scope, but no recursive parser frame.
                let recursive_proof = proof
                    && !both_container
                    && !matches!(preceding, Some(Token::Ident(name)) if name == "else");
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
fn aligned_proposition(pointer: ProgramExpression, alignment: u64) -> ClickProposition {
    let uint64 = |value: u64| {
        ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(
            MachineTerm::uint64_constant(value),
        )))
    };
    ClickProposition::Comparison {
        left: ContractExpression::BitwiseAnd(
            Box::new(ContractExpression::ProgramExpression(
                ProgramExpression::Cast {
                    expression: Box::new(pointer),
                    target_type: ProgramType::UInt64,
                    integer_mode: crate::kernel::IntegerCastMode::Standard,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            )),
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
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
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
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
    out: &mut Vec<ClickProposition>,
) {
    match requirement {
        Requirement::Resource(clause) => out.extend(object_alignment_fact(clause, struct_layouts)),
        Requirement::LoadableSegment { .. } | Requirement::Proposition(_) => {}
    }
}

#[cfg(test)]
thread_local! {
    /// Tokens `looks_like_algebraic_constructor` has examined on this thread.
    static CONSTRUCTOR_LOOKAHEAD_TOKENS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/surface/parser.rs");
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
    fn nested_program_binder_restores_integer_shadowing() {
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
    fn c_shadow_preserves_wide_literal_source_for_validation() {
        let mut rejected =
            Parser::new("forall (z: Integer) { exists (z: int32) { z == 100000000000000000000 } }")
                .unwrap();
        // Literal source text is retained through parsing.  The C-range
        // rejection belongs to semantic lowering, where the binder type is
        // available, rather than to the parser's context-sensitive grammar.
        assert!(rejected.parse_proposition().is_ok());

        let mut restored =
            Parser::new("forall (z: Integer) { exists (z: int32) { z == 0 } and z > 0 }").unwrap();
        assert!(restored.parse_proposition().is_ok());
    }

    #[test]
    fn integer_comparison_observes_a_let_body_in_its_lexical_scope() {
        for text in [
            "to_integer(x) == (let saved: int32 = x; to_integer(saved))",
            "to_integer(x) == (let saved: Integer = to_integer(x); saved)",
            "to_integer(x) == (let saved = to_integer(x); saved)",
        ] {
            let mut parser = Parser::new(text).unwrap();
            parser.integer_arithmetic = true;
            let ClickProposition::Comparison { right, .. } = parser.parse_proposition().unwrap()
            else {
                panic!("expected a comparison");
            };
            assert!(
                matches!(right, ContractExpression::Let { .. }),
                "{text}: {right:?}"
            );
        }
        let mut parser = Parser::new(
            "to_integer(x) == (let saved: Integer = to_integer(x); let saved: int32 = x; saved)",
        )
        .unwrap();
        parser.integer_arithmetic = true;
        let ClickProposition::Comparison { right, .. } = parser.parse_proposition().unwrap() else {
            panic!("expected a comparison");
        };
        assert!(matches!(right, ContractExpression::Call { name, arguments }
            if name == "to_integer" && matches!(arguments.as_slice(), [ContractExpression::Let { .. }])));
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
            ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) if name.is_named("saved")
        ));
    }

    #[test]
    fn state_of_pure_call_can_continue_into_comparison() {
        let source = r#"
            function identity(x: int32) -> int32 { x }
            theorem state_call(x: int32) {
                ensures x == x by {
                    have at(saved, identity(x)) == at(saved, 1) by { known(); }
                    known();
                }
            }
        "#;
        Parser::new(source).unwrap().parse_file_items().expect(
            "an expression at a program point must not parse as a proposition at that point",
        );
    }
}

/// Preserve the C parser's exact, widened struct byte stride in sidecars.
fn struct_byte_stride(index: ProgramExpression, width: u32) -> ProgramExpression {
    ProgramExpression::Multiply(
        Box::new(ProgramExpression::Cast {
            expression: Box::new(index),
            target_type: crate::kernel::ProgramType::Int64,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        }),
        Box::new(ProgramExpression::Value(crate::kernel::int64(
            crate::kernel::MachineTerm::int64_constant(i64::from(width)),
        ))),
    )
}

fn struct_byte_base(base: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Cast {
        expression: Box::new(base),
        target_type: crate::kernel::ProgramType::UInt8Pointer,
        integer_mode: crate::kernel::IntegerCastMode::Standard,
        pointee_struct: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    }
}

#[cfg(test)]
mod tactic_classification_tests {
    use super::*;
    use crate::surface::proof_certificate::certificate_step_class;

    #[test]
    fn logical_bindings_use_let_and_round_trip() {
        for source in [
            "intro();",
            "let x = intro();",
            "let binder(7) = intro();",
            "let ih = induct(n);",
        ] {
            let tactic = Parser::new(source).unwrap().parse_proof_tactic().unwrap();
            let printed = super::super::printing::format_partial_tactic_sequence(
                std::slice::from_ref(&tactic),
            );
            assert_eq!(printed, source);
            Parser::new(&printed).unwrap().parse_proof_tactic().unwrap();
            match (source, &tactic) {
                ("intro();", ProofTactic::Intro) => {}
                ("let x = intro();", ProofTactic::IntroAs(name)) => assert_eq!(name, "x"),
                ("let binder(7) = intro();", ProofTactic::IntroBinder(_)) => {}
                (
                    "let ih = induct(n);",
                    ProofTactic::Induct {
                        parameter,
                        hypothesis,
                    },
                ) => {
                    assert_eq!(parameter, "n");
                    assert_eq!(hypothesis, "ih");
                }
                _ => panic!("unexpected tactic: {source}"),
            }
        }
        for source in [
            "intro() as x;",
            "intro() as binder(7);",
            "induct(n) as ih;",
            "let x = intro(3);",
            "let ih = induct(n, m);",
            "let ih = induct();",
            "let { x: y } = intro();",
            "let { x: y } = induct(n);",
            "let x = intro()",
            "let ih = induct(n)",
        ] {
            assert!(
                Parser::new(source).unwrap().parse_proof_tactic().is_err(),
                "{source}"
            );
        }
        for source in [
            "induct(xs) as ih { List::Nil => {} }",
            "induct(xs) { List::Nil => {} }",
        ] {
            assert!(
                Parser::new(source).unwrap().parse_proof_tactic().is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn witness_accepts_only_nonempty_positional_values() {
        for (source, count) in [
            ("witness(3);", 1),
            ("witness(3, 4);", 2),
            ("witness(3, 4,);", 2),
        ] {
            let ProofTactic::Witness(witness) =
                Parser::new(source).unwrap().parse_proof_tactic().unwrap()
            else {
                panic!("expected witness: {source}");
            };
            assert_eq!(witness.values().count(), count);
        }
        for source in [
            "witness();",
            "witness { x: 3 };",
            "witness(x: 3);",
            "witness(3,,4);",
            "witness(3)",
        ] {
            assert!(
                Parser::new(source).unwrap().parse_proof_tactic().is_err(),
                "{source}"
            );
        }
    }

    /// One written instance of every public tactic form. The parser is given
    /// a contract `Contract`, a callee `f`, and a user tactic `name`, each
    /// declaring one supplied binder `cell`, and a held instance `c`.
    const FORM_INSTANCES: &[(&str, &str)] = &[
        ("mark", "mark name;"),
        ("step", "step();"),
        ("step-result", "let { result: value } = step();"),
        ("step-contract", "step(Contract);"),
        ("step-contract-application", "step(Contract, { cell: c });"),
        ("step-call", "step(f, { cell: c });"),
        (
            "step-contract-map",
            "let { result: r } = step(Contract, { cell: c });",
        ),
        ("step-by", "step() by { normalize(); }"),
        (
            "step-requires",
            "step() { requires x == 1 by { normalize(); }; }",
        ),
        ("user-tactic", "name(x, { cell: c });"),
        ("step-until", "step_until(label);"),
        ("unfold-predicate", "unfold(predicate(x));"),
        ("unfold-function", "unfold(f(x));"),
        ("unfold-resource", "unfold(reference(p));"),
        ("fold-resource", "fold(reference(p));"),
        ("unfold-slot", "unfold(reference(p)[0]);"),
        ("fold-slot", "fold(reference(p)[0]);"),
        ("gather-resource", "gather(reference(p));"),
        ("scatter-resource", "scatter(reference(p));"),
        ("construct-resource", "construct(reference(p));"),
        ("induct", "let ih = induct(n);"),
        (
            "proof-match",
            "match value { List::Nil => { normalize(); } }",
        ),
        ("apply-induction", "apply(ih(m));"),
        ("apply-induction-using", "apply(ih(m)) using { m == 1; };"),
        ("apply-fact", "apply(x > 0 implies y > 0);"),
        (
            "apply-fact-using",
            "apply(x > 0 implies y > 0) using { x > 0; };",
        ),
        ("apply-theorem", "apply(theorem(x));"),
        (
            "apply-theorem-using",
            "apply(theorem(x)) using { x == 1; };",
        ),
        ("have", "have x == 1 by { normalize(); }"),
        ("open", "open(reference(p)) { normalize(); }"),
        ("if", "if x == 1 { normalize(); } else { normalize(); }"),
        (
            "cases",
            "cases { x == 1 => { normalize(); } x != 1 => { normalize(); } }",
        ),
        (
            "both",
            "both { left => { normalize(); } right => { normalize(); } }",
        ),
        (
            "branch",
            "branch ensuring { fact x == 1; } { true => { normalize(); } false => { normalize(); } }",
        ),
        (
            "outcomes",
            "outcomes { returned => { normalize(); } threw => { normalize(); } }",
        ),
        (
            "loop",
            "loop { invariant x == 1; initialize by { normalize(); } preserve by { normalize(); } }",
        ),
        ("observe-resource", "observe(reference(p));"),
        ("witness", "witness(1);"),
        ("obtain", "let x = obtain(exists (k: Integer) { k == k });"),
        ("known", "known();"),
        ("normalize", "normalize();"),
        ("normalize-using", "normalize() using { x == 1; };"),
        ("preserve", "preserve(memory(*p), statement(0));"),
        ("intro", "intro();"),
        ("intro-as", "let name = intro();"),
        ("enumerate", "enumerate();"),
        ("contradiction", "contradiction(x == 1);"),
        ("rewrite", "rewrite(x, 1);"),
        ("transport", "transport(x == 1, y == 1);"),
        (
            "transport-using",
            "transport(x == 1, y == 1) using { x == y; };",
        ),
        ("instantiate", "instantiate(F, 1);"),
        ("solve", "solve();"),
        ("solve-using", "solve() using { x == 1; };"),
        ("check-termination-local", "check_termination_local(\"f\");"),
        (
            "check-termination-component",
            "check_termination_component(\"f\", normal);",
        ),
        (
            "check-termination-callbacks",
            "check_termination_callbacks();",
        ),
    ];

    #[test]
    fn branch_requires_two_distinct_labeled_arms() {
        for (branch, expected) in [
            ("branch { true => {} }", "`branch` needs both"),
            (
                "branch { true => {} true => {} }",
                "duplicate `branch` arm `true`",
            ),
            (
                "branch { yes => {} false => {} }",
                "`branch` arms are `true` and `false`",
            ),
        ] {
            let source = format!("void f() {{}} by {{ {branch} }}");
            assert!(parse(&source).unwrap_err().message().contains(expected));
        }
        assert!(parse("void f() {} by { branch {} else {} }").is_err());
        assert!(
            parse("void f() {} by { branch ensuring { fact true; } then {} else {} }").is_err()
        );
    }

    fn label(class: TacticClass) -> &'static str {
        match class {
            TacticClass::Simple(_) => "simple",
            TacticClass::Smart(_) => "smart",
            TacticClass::Control(_) => "control",
            TacticClass::Sorry => "sorry",
        }
    }

    /// Catches a tactic whose class is stored inconsistently: the registry
    /// (and through `tests/documentation.rs` the reference table), the parsed
    /// tactic's `class()`, and the class of the certificate step it prints as
    /// must agree for every public form.
    #[test]
    fn every_public_form_has_one_class() {
        let instances = FORM_INSTANCES.iter().map(|&(id, _)| id).collect::<Vec<_>>();
        let registry = PUBLIC_TACTIC_FORMS
            .iter()
            .map(|form| form.id)
            .collect::<Vec<_>>();
        assert_eq!(instances, registry, "one instance per registered form");
        let mut failures = Vec::new();
        let mut classes = BTreeMap::new();
        for (form, &(_, written)) in PUBLIC_TACTIC_FORMS.iter().zip(FORM_INSTANCES) {
            let parsed = Parser::new(written).and_then(|mut parser| {
                let cell = BTreeMap::from([(
                    "cell".to_string(),
                    CalleeResourceBinder {
                        identity: Variable(1),
                        family: Some("reference".to_string()),
                        resource: None,
                        parameter_names: Vec::new(),
                        kind: CalleeResourceBinderKind::Supplied,
                    },
                )]);
                parser.tactic_names.insert("name".to_string());
                for callee in ["f", "name"] {
                    parser
                        .callee_resource_binders
                        .insert(callee.to_string(), cell.clone());
                }
                parser
                    .contract_resource_binders
                    .insert("Contract".to_string(), cell);
                parser
                    .names
                    .resource_bindings
                    .insert("c".to_string(), (Variable(2), "reference".to_string()));
                parser.parse_proof_tactic()
            });
            let tactic = match parsed {
                Ok(tactic) => tactic,
                Err(error) => {
                    failures.push(format!("{}: `{written}` does not parse: {error}", form.id));
                    continue;
                }
            };
            let class = tactic.class();
            classes.insert(form.id, class);
            if label(class) != form.class {
                failures.push(format!(
                    "{}: registry says {}, `{written}` parses as {class:?}",
                    form.id, form.class
                ));
            }
            if let Ok(certificate) = ProofCertificate::from_proof_tactics(&[tactic]) {
                let step_class = certificate_step_class(&certificate.steps()[0]);
                if step_class != class {
                    failures.push(format!(
                        "{}: tactic class {class:?}, certificate step class {step_class:?}",
                        form.id
                    ));
                }
            } else if !matches!(class, TacticClass::Smart(_)) {
                failures.push(format!("{}: non-smart form has no certificate", form.id));
            }
        }
        // An elided form is the simple tactic its `-using` form writes out.
        for (id, class) in &classes {
            let TacticClass::Smart(SmartSite::Elided(elided)) = class else {
                continue;
            };
            let written = classes.get(format!("{id}-using").as_str());
            if written != Some(&TacticClass::Simple(elided.written_form())) {
                failures.push(format!(
                    "{id}: elided form of {:?}, but `{id}-using` parses as {written:?}",
                    elided.written_form()
                ));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }
}

#[cfg(test)]
mod loop_name_tests {
    use super::*;

    fn parse_loop(body: &str) -> Result<ClickFile, ClickError> {
        let source = format!(
            "predicate reflexive() {{ forall (introduced: int32) {{ introduced == introduced }} }} predicate alias() {{ reflexive() }} int32 lp(int32 n, int32* p) {{ ensures result == n; }} by {{ loop {{ {body} }} }}"
        );
        let mut layouts = ProgramLayouts::default();
        layouts.program_object_names.insert(
            "lp".to_string(),
            std::sync::Arc::new(["n", "p", "i"].map(str::to_string).into()),
        );
        Parser::with_program_layouts(&source, layouts, None)?.parse_file_items()
    }

    #[test]
    fn loop_unknown_names_are_type_errors_before_proof_execution() {
        for (body, clause) in [
            ("invariant bogus <= n;", "invariant"),
            ("invariant bogus == bogus;", "invariant"),
            ("invariant program::bogus == n;", "invariant"),
            (
                "invariant (0..n).all(|bogus| { bogus == bogus }); invariant bogus == 0;",
                "invariant",
            ),
            ("decreases bogus;", "decreases"),
            ("views p[0..bogus];", "views"),
            ("views bogus[0..1];", "views"),
            ("owns p[0..bogus];", "owns"),
            ("owns bogus[0..1];", "owns"),
            (
                "invariant i <= n; preserve by { have bogus == i; }",
                "preserve",
            ),
            (
                "invariant i <= n; initialize by { have bogus == i; }",
                "initialize",
            ),
            ("if bogus == 0 { views p[0..1]; }", "if"),
            (
                "invariant i <= n; preserve by { if i == 0 { let { result: bogus } = step(); } else { step(); } have bogus == n; }",
                "preserve",
            ),
        ] {
            let error = parse_loop(body).unwrap_err();
            assert_eq!(error.kind(), ClickErrorKind::Type, "{body}: {error}");
            assert!(
                error
                    .message()
                    .contains(&format!("unknown name `bogus` in loop {clause} clause")),
                "{body}: {error}"
            );
        }
    }

    #[test]
    fn loop_names_keep_program_locals_quantifiers_and_phase_binders() {
        parse_loop("decreases n - i; invariant forall (k: int32) { k == k }; invariant i <= n; views p[0..n]; preserve by { have forall (saved: int32) { saved == saved } by { intro(); have saved == saved; } }").unwrap();
    }

    #[test]
    fn loop_range_binders_and_invariant_proof_binders_are_recognized() {
        parse_loop("invariant (0..n).all(|k| { k >= 0 }); invariant (0..n).fold(0, |acc, k| { acc + k }) >= 0; invariant forall (v: int32) { v == v }; preserve by { intro(); have v == v; }").unwrap();
    }

    #[test]
    fn loop_phase_proofs_recognize_binders_from_predicate_goals() {
        parse_loop("invariant alias(); initialize by { intro(); have introduced == introduced; } preserve by { have alias() by { intro(); have introduced == introduced; } }").unwrap();
    }

    #[test]
    fn loop_proof_values_remain_visible_in_nested_blocks() {
        parse_loop("invariant i <= n; preserve by { let { result: saved } = step(); if i == 0 { have forall (k: int32) { saved == saved } by { intro(); have saved == saved; } } else { have saved == n; } }").unwrap();
    }

    #[test]
    fn nested_loop_restores_the_enclosing_phase_name_context() {
        let error = parse_loop(
            "invariant i <= n; preserve by { loop { invariant i <= n; } have bogus == i; }",
        )
        .unwrap_err();
        assert!(
            error
                .message()
                .contains("unknown name `bogus` in loop preserve clause"),
            "{error}"
        );
    }
}

#[cfg(test)]
mod preserve_syntax_tests {
    use super::*;

    fn parser(source: &str) -> Parser {
        let mut parser = Parser::new(source).unwrap();
        parser
            .names
            .resource_bindings
            .insert("r".into(), (Variable(123), "Node".into()));
        parser.resource_parameters.insert("R".into(), 0);
        parser
            .declared_resource_fields
            .insert("Node".into(), Vec::new());
        parser
    }

    #[test]
    fn preserve_arguments_retain_exact_separation_and_snapshot_scopes() {
        for (source, evidence) in [
            ("preserve(r, call(0));", "separate(call(0).footprint, r)"),
            (
                "preserve(at(saved, r), call(0));",
                "separate(call(0).footprint, at(saved, r))",
            ),
            (
                "preserve((at(saved, r)), call(0));",
                "separate(call(0).footprint, at(saved, r))",
            ),
            (
                "preserve(memory(*p), statement(0));",
                "separate(statement(0).footprint, memory(*p))",
            ),
            (
                "preserve(memory(p[i]), loop(1).statement(2));",
                "separate(loop(1).statement(2).footprint, memory(p[i]))",
            ),
            (
                "preserve(at(saved, memory(*p)), region(3));",
                "separate(region(3).footprint, at(saved, memory(*p)))",
            ),
            (
                "preserve(at(outer, at(inner, memory(*p))), region(3));",
                "separate(region(3).footprint, at(outer, at(inner, memory(*p))))",
            ),
            (
                "preserve(memory(at(saved, p)[0]), region(3));",
                "separate(region(3).footprint, memory(at(saved, p)[0]))",
            ),
        ] {
            let tactic = parser(source).parse_proof_tactic().unwrap();
            let expected = parser(evidence).parse_proposition().unwrap();
            assert_eq!(tactic, ProofTactic::Preserve(expected));
            let printed =
                crate::surface::printing::format_proof_tactics(std::slice::from_ref(&tactic))
                    .unwrap();
            assert!(!printed.contains("preserve(separate("), "{printed}");
            let reparsed = parser(&printed).parse_proof_clause_or_default().unwrap();
            let SourceProof::Script(reparsed) = reparsed else {
                panic!("expected a script")
            };
            // Resource printing canonicalizes cell sugar to a range. Check
            // the canonical evidence, rather than incidental source metadata.
            let ProofTactic::Preserve(actual) = &reparsed[0] else {
                panic!("expected preserve")
            };
            let ProofTactic::Preserve(expected) = &tactic else {
                unreachable!()
            };
            assert_eq!(
                printing::source_click_proposition(actual),
                printing::source_click_proposition(expected),
                "{source} -> {printed}"
            );
        }
    }

    #[test]
    fn snapshot_resources_share_one_grammar_and_parentheses_only_group() {
        for subject in [
            "r",
            "R",
            "memory(*p)",
            "Node()",
            "separation::emp",
            "memory(*p) * r",
        ] {
            let resource = format!("at(saved, {subject})");
            let expected = parser(&resource).parse_resource_subject().unwrap();
            for resource in [
                resource,
                format!("(at(saved, {subject}))"),
                format!("at(saved, ({subject}))"),
                format!("((at(saved, (({subject})))))"),
            ] {
                assert_eq!(
                    parser(&resource).parse_resource_subject().unwrap(),
                    expected,
                    "{resource}"
                );
                let ProofTactic::Preserve(ClickProposition::Separate { right, .. }) =
                    parser(&format!("preserve({resource}, statement(0));"))
                        .parse_proof_tactic()
                        .unwrap()
                else {
                    panic!("expected preserve")
                };
                assert_eq!(right, expected, "{resource}");
                let ClickProposition::Separate { right, .. } =
                    parser(&format!("separate(statement(0).footprint, {resource})"))
                        .parse_proposition()
                        .unwrap()
                else {
                    panic!("expected separation")
                };
                assert_eq!(right, expected, "{resource}");
                let actual = parser(&resource).parse_contract_expression().unwrap();
                if subject == "Node()" {
                    // Constructor calls are resolved after all declarations,
                    // including when nested under a snapshot.
                    assert!(
                        matches!(actual, ContractExpression::At { .. }),
                        "{resource}"
                    );
                } else {
                    assert_eq!(
                        actual,
                        ContractExpression::Resource(Box::new(expected.clone())),
                        "{resource}"
                    );
                }
            }
        }
        for value in ["at(saved, x)", "at(saved, f(x))", "at(saved, r.field)"] {
            assert!(
                matches!(
                    parser(value).parse_contract_expression().unwrap(),
                    ContractExpression::At { .. }
                ),
                "{value}"
            );
        }
    }

    #[test]
    fn preserve_refuses_the_old_proposition_argument_and_wrong_arity() {
        for source in [
            "preserve(separate(statement(0).footprint, memory(*p)));",
            "preserve();",
            "preserve(memory(*p));",
            "preserve(memory(*p), statement(0).footprint);",
            "preserve(memory(*p), statement(0), statement(1));",
            "preserve(at(saved, separate(statement(0).footprint, memory(*p))));",
        ] {
            assert!(
                Parser::new(source).unwrap().parse_proof_tactic().is_err(),
                "{source}"
            );
        }
    }
}

#[cfg(test)]
mod rewrite_syntax_tests {
    use super::*;

    #[test]
    fn rewrite_endpoints_round_trip_with_nested_arguments_and_states() {
        for source in [
            "rewrite(x, y);",
            "rewrite(y, x);",
            "rewrite(at(function.entry, x), old(y));",
            "rewrite(f(x, y), if x == y { 1 } else { 2 });",
        ] {
            let tactic = Parser::new(source).unwrap().parse_proof_tactic().unwrap();
            let printed =
                crate::surface::printing::format_proof_tactics(std::slice::from_ref(&tactic))
                    .unwrap();
            let reparsed = Parser::new(&printed)
                .unwrap()
                .parse_proof_clause_or_default()
                .unwrap();
            assert_eq!(
                reparsed,
                SourceProof::Script(vec![tactic]),
                "{source} -> {printed}"
            );
        }
    }

    #[test]
    fn rewrite_arguments_keep_specification_equality_arithmetic() {
        for (source, equality) in [
            ("rewrite(x + 1, y);", "x + 1 == y"),
            ("rewrite(x - y, 0u64);", "x - y == 0u64"),
            (
                "rewrite(to_integer(x), to_integer(y));",
                "to_integer(x) == to_integer(y)",
            ),
            (
                "rewrite((x + y) as uint64, 0u64);",
                "(x + y) as uint64 == 0u64",
            ),
        ] {
            let ProofTactic::Rewrite(actual) =
                Parser::new(source).unwrap().parse_proof_tactic().unwrap()
            else {
                panic!("expected rewrite");
            };
            let expected = Parser::new(equality).unwrap().parse_proposition().unwrap();
            assert_eq!(actual, expected, "{source}");
        }
    }

    #[test]
    fn rewrite_refuses_the_old_equality_argument_and_wrong_arity() {
        let error = Parser::new("rewrite(x == y);")
            .unwrap()
            .parse_proof_tactic()
            .unwrap_err();
        assert!(error.message().contains("write `rewrite(x, y)`"));
        for source in ["rewrite(x);", "rewrite();", "rewrite(x, y, z);"] {
            assert!(
                Parser::new(source).unwrap().parse_proof_tactic().is_err(),
                "{source}"
            );
        }
    }
}

#[cfg(test)]
mod qualified_native_pointer_cast_tests {
    use super::*;

    #[test]
    fn native_pointer_cast_qualifiers_survive_both_source_renderers() {
        for qualifiers in ["const", "volatile", "const volatile"] {
            for ty in ["int8", "uint8", "void", "float", "double"] {
                let source = format!("p as ({qualifiers} {ty} *)");
                let parse = |source: &str| {
                    Parser::new(source)
                        .unwrap()
                        .parse_contract_expression()
                        .unwrap_or_else(|error| panic!("{source}: {error}"))
                };
                let expression = parse(&source);
                let lowered = contract_expression_as_program_expression(&expression).unwrap();
                let ProgramExpression::Cast {
                    pointee_constant,
                    pointee_volatile,
                    ..
                } = &lowered
                else {
                    panic!("pointer cast")
                };
                assert_eq!(*pointee_constant, qualifiers.contains("const"));
                assert_eq!(*pointee_volatile, qualifiers.contains("volatile"));
                for rendered in [
                    diagnostics::describe_contract_expression(&expression),
                    diagnostics::describe_program_expression(&lowered),
                ] {
                    assert_eq!(
                        contract_expression_as_program_expression(&parse(&rendered)).unwrap(),
                        lowered,
                        "{source}: {rendered}"
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod lambda_certificate_parser_tests {}

#[cfg(test)]
mod local_binding_tests;

impl ProgramLayouts {
    fn register_static_binding(&mut self, binding: &crate::kernel::BindingName) {
        crate::instrumentation::record_deterministic_work(1);
        let Some(id) = binding.static_id() else {
            return;
        };
        let Some(metadata) = id.metadata() else {
            return;
        };
        let index = std::sync::Arc::make_mut(&mut self.local_bindings);
        if let Some(function) = id.function() {
            index
                .owners
                .entry(function.to_owned())
                .or_default()
                .insert(id.source().map(str::to_owned));
        } else {
            index.static_files.insert(id.source().map(str::to_owned));
        }
        index.statics.insert(
            id.clone(),
            SourceBindingInfo {
                struct_name: id.struct_name().map(str::to_owned),
                aggregate: metadata.aggregate || metadata.array_shape.is_some(),
                array_shape: id.array_shape().map(<[u32]>::to_vec),
            },
        );
    }
    fn register_function_static_bindings(
        &mut self,
        function: &crate::languages::interface::ImportedFunction,
    ) {
        for object in function.static_locals().values() {
            self.register_static_binding(object.kernel_name());
        }
        for object in function.static_arrays().values() {
            self.register_static_binding(object.kernel_name());
        }
        for object in function.static_aggregates().values() {
            self.register_static_binding(object.kernel_name());
        }
        for object in function.static_aggregate_arrays().values() {
            self.register_static_binding(object.kernel_name());
        }
    }
    pub(in crate::surface) fn register_file_static_bindings(
        &mut self,
        unit: &syntax::CTranslationUnit,
    ) {
        for object in unit.globals.values() {
            self.register_static_binding(object.kernel_name());
        }
        for object in unit.global_arrays.values() {
            self.register_static_binding(object.kernel_name());
        }
        for object in unit.global_aggregates.values() {
            self.register_static_binding(object.kernel_name());
        }
        for object in unit.global_aggregate_arrays.values() {
            self.register_static_binding(object.kernel_name());
        }
    }
}
