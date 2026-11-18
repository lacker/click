//! Qualified Click library names: `click::list::append`, `list::append`
//! when the module is in scope, and `append` after
//! `import click::list::{append};`. A library path is joined into the
//! declaration it names before parsing, keeping its written spelling for a
//! C or C++ declaration of the same spelling. A selectively imported bare
//! name is resolved by the parser where it reads a Click reference.

use super::parser::{Token, tokenizer};
use super::*;

/// A kind of declaration a file makes at top level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DeclarationKind {
    Theorem,
    Function,
    Predicate,
    Resource,
    Enum,
    Tactic,
    /// `extern <return type> name(...)`.
    Extern,
    /// A named contract. Only an imported module's are recorded: the
    /// top-level walk does not read them.
    Contract,
}

/// Where a declaration in a [`SymbolTable`] comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclarationOrigin {
    /// The file itself.
    File,
    /// A user module the file imports.
    Imported,
}

/// A declaration a file makes at top level, as its tokens show it: the
/// kind, the name, and the token index of the name.
#[derive(Clone, Debug)]
pub(super) struct TopLevelDeclaration {
    pub(super) kind: DeclarationKind,
    pub(super) name: String,
    pub(super) at: usize,
}

/// The declarations a file makes at top level, in source order: one walk of
/// its tokens outside every bracket. Every index of a file's or a library
/// module's top-level names reads this walk. It records no deterministic
/// work: the library's walk is taken once per process, whichever
/// verification asks first, so its caller charges a file's walk.
pub(super) fn top_level_declarations(tokens: &[Token]) -> Vec<TopLevelDeclaration> {
    let mut declarations = Vec::new();
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate() {
        match token {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => {
                depth = depth.saturating_sub(1);
            }
            Token::Ident(word) if depth == 0 => {
                let kind = match word.as_str() {
                    // A library `axiom` is cited as a theorem is.
                    "theorem" | "axiom" => DeclarationKind::Theorem,
                    "function" => DeclarationKind::Function,
                    "predicate" => DeclarationKind::Predicate,
                    "resource" => DeclarationKind::Resource,
                    // `spec enum Name` and a library primitive `type Name`.
                    "enum" | "type" => DeclarationKind::Enum,
                    "tactic" => DeclarationKind::Tactic,
                    // `extern <return type> name(...)`: the name precedes the
                    // parameter list. A member such as `V::length` declares no
                    // bare name.
                    "extern" => {
                        let open = tokens[index..]
                            .iter()
                            .position(|token| *token == Token::LParen)
                            .map(|offset| index + offset);
                        if let Some(open) = open
                            && let Some(Token::Ident(name)) = tokens.get(open.wrapping_sub(1))
                            && tokens.get(open.wrapping_sub(2)) != Some(&Token::ColonColon)
                        {
                            declarations.push(TopLevelDeclaration {
                                kind: DeclarationKind::Extern,
                                name: name.clone(),
                                at: open - 1,
                            });
                        }
                        continue;
                    }
                    _ => continue,
                };
                if let Some(Token::Ident(name)) = tokens.get(index + 1) {
                    declarations.push(TopLevelDeclaration {
                        kind,
                        name: name.clone(),
                        at: index + 1,
                    });
                }
            }
            _ => {}
        }
    }
    declarations
}

/// Each Click library module's tokens, read once per process for the tables
/// below. Each table once tokenized the whole library itself, so every
/// process tokenized it four times, the parse included.
fn library_tokens() -> &'static [(&'static str, Vec<Token>)] {
    static TOKENS: std::sync::OnceLock<Vec<(&'static str, Vec<Token>)>> =
        std::sync::OnceLock::new();
    TOKENS.get_or_init(|| {
        super::CLICK_LIBRARY_MODULES
            .iter()
            .filter_map(|(identity, source)| {
                let (tokens, _) = tokenizer::tokenize(source, None).ok()?;
                Some((*identity, tokens))
            })
            .collect()
    })
}

/// The top-level declarations of each Click library module, read from its
/// tokens once per process. The library's parsed declarations are not used:
/// library modules are themselves parsed through this resolution.
pub(super) fn library_declarations() -> &'static BTreeMap<&'static str, Vec<TopLevelDeclaration>> {
    static DECLARATIONS: std::sync::OnceLock<BTreeMap<&'static str, Vec<TopLevelDeclaration>>> =
        std::sync::OnceLock::new();
    DECLARATIONS.get_or_init(|| {
        library_tokens()
            .iter()
            .map(|(identity, tokens)| (*identity, top_level_declarations(tokens)))
            .collect()
    })
}

/// The positions of the `Integer` parameters of each Click library function
/// and theorem that has any, by the name a reference to it resolves to.
/// Read from the library's tokens once per process.
pub(super) fn library_integer_parameters() -> &'static BTreeMap<String, Vec<usize>> {
    static POSITIONS: std::sync::OnceLock<BTreeMap<String, Vec<usize>>> =
        std::sync::OnceLock::new();
    POSITIONS.get_or_init(|| {
        let mut positions = BTreeMap::new();
        for (identity, tokens) in library_tokens() {
            for declaration in top_level_declarations(tokens) {
                if !matches!(
                    declaration.kind,
                    DeclarationKind::Function | DeclarationKind::Theorem
                ) {
                    continue;
                }
                if let Some(integers) =
                    super::parser::written_integer_parameters(tokens, declaration.at + 1)
                {
                    positions.insert(resolved_name(identity, &declaration.name), integers);
                }
            }
        }
        positions
    })
}

/// The Click library functions whose declared result is a pointer, by the
/// name a reference to each resolves to: a call of one is a pointer operand.
/// Read from the library's tokens once per process.
pub(super) fn library_pointer_result_functions() -> &'static BTreeSet<String> {
    static FUNCTIONS: std::sync::OnceLock<BTreeSet<String>> = std::sync::OnceLock::new();
    FUNCTIONS.get_or_init(|| {
        let mut functions = BTreeSet::new();
        for (identity, tokens) in library_tokens() {
            for declaration in top_level_declarations(tokens) {
                if declaration.kind == DeclarationKind::Function
                    && declares_pointer_result(tokens, declaration.at + 1)
                {
                    functions.insert(resolved_name(identity, &declaration.name));
                }
            }
        }
        functions
    })
}

/// The method names that are a Click library function returning a pointer,
/// such as `as_ptr`: a method call of one is a pointer operand, whatever
/// its receiver, since a library type's methods are its library functions.
pub(super) fn library_pointer_result_methods() -> &'static BTreeSet<&'static str> {
    static METHODS: std::sync::OnceLock<BTreeSet<&'static str>> = std::sync::OnceLock::new();
    METHODS.get_or_init(|| {
        library_pointer_result_functions()
            .iter()
            .filter_map(|name| name.rsplit("::").next())
            .collect()
    })
}

/// Whether the pure function whose type parameters or parameter list start
/// at `start` declares a pointer result: `-> T*`, `-> uint8*`,
/// `-> struct node*`, or Rust's `-> *const u8`.
pub(super) fn declares_pointer_result(tokens: &[Token], start: usize) -> bool {
    let mut at = start;
    if tokens.get(at) == Some(&Token::LessThan) {
        let Some(close) = tokens[at..]
            .iter()
            .position(|token| *token == Token::GreaterThan)
        else {
            return false;
        };
        at += close + 1;
    }
    if tokens.get(at) != Some(&Token::LParen) {
        return false;
    }
    let mut depth = 0usize;
    let mut close = None;
    for (index, token) in tokens.iter().enumerate().skip(at) {
        match token {
            Token::LParen => depth += 1,
            Token::RParen => {
                depth -= 1;
                if depth == 0 {
                    close = Some(index);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(close) = close else {
        return false;
    };
    tokens.get(close + 1) == Some(&Token::Arrow)
        && tokens[close + 2..]
            .iter()
            .take_while(|token| !matches!(token, Token::LBrace | Token::Semicolon))
            .any(|token| *token == Token::Star)
}

/// The names a library module declares of the kinds `kinds`.
fn library_names_of<'k>(
    identity: &str,
    kinds: &'k [DeclarationKind],
) -> impl Iterator<Item = &'static str> + use<'k> {
    library_declarations()
        .get(identity)
        .into_iter()
        .flatten()
        .filter(move |declaration| kinds.contains(&declaration.kind))
        .map(|declaration| declaration.name.as_str())
}

/// The top-level declaration names of each Click library module.
fn library_declaration_names() -> &'static BTreeMap<&'static str, BTreeSet<String>> {
    static NAMES: std::sync::OnceLock<BTreeMap<&'static str, BTreeSet<String>>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        library_declarations()
            .iter()
            .map(|(identity, declarations)| {
                (
                    *identity,
                    declarations
                        .iter()
                        .map(|declaration| declaration.name.clone())
                        .collect(),
                )
            })
            .collect()
    })
}

/// Each Click library theorem's bare name and its qualified identity,
/// `click::module::name`, which the verifier uses for it: a file theorem of
/// the same name is a different theorem, and built-in tactics name library
/// theorems by this identity. A bare name two modules declare keeps the
/// later module's identity; tests use it for names declared once.
#[cfg(test)]
fn library_theorem_identities() -> &'static BTreeMap<String, String> {
    static THEOREMS: std::sync::OnceLock<BTreeMap<String, String>> = std::sync::OnceLock::new();
    THEOREMS.get_or_init(|| {
        let mut theorems = BTreeMap::new();
        for identity in library_declarations().keys() {
            let path = crate::surface::library_module_path(identity);
            for name in library_names_of(identity, &[DeclarationKind::Theorem]) {
                theorems.insert(name.to_string(), format!("{path}::{name}"));
            }
        }
        theorems
    })
}

/// The Click library modules whose functions and predicates, not only
/// theorems, have qualified verifier identities. A module joins when its
/// names drop their prefixes and its uses move to paths.
const QUALIFIED_MODULES: &[&str] = &[
    "library/separation.click",
    "library/nat.click",
    "library/list.click",
    "library/option.click",
    "library/result.click",
    "library/bytes.click",
    "library/cstr.click",
    "library/permutation.click",
    "library/integer.click",
    "library/c/stdio.click",
    "library/rust/i8.click",
    "library/rust/i16.click",
    "library/rust/i32.click",
    "library/rust/i64.click",
    "library/rust/isize.click",
    "library/rust/u8.click",
    "library/rust/u16.click",
    "library/rust/u32.click",
    "library/rust/u64.click",
    "library/rust/usize.click",
    "library/rust/vec.click",
    "library/rust/slice.click",
];

/// Whether the library declaration `name` in module `identity` is known to
/// the verifier by its qualified identity.
pub(in crate::surface) fn is_qualified_declaration(identity: &str, name: &str) -> bool {
    library_theorem_names()
        .get(identity)
        .is_some_and(|names| names.contains(name))
        || (QUALIFIED_MODULES.contains(&identity)
            && library_functions_and_predicates()
                .get(identity)
                .is_some_and(|names| names.contains(name)))
}

/// The theorems of each Click library module. Every library theorem has a
/// qualified identity, so two modules may declare theorems of one bare name
/// (`u32::multiply_to_integer` and `usize::multiply_to_integer`).
fn library_theorem_names() -> &'static BTreeMap<&'static str, BTreeSet<String>> {
    static NAMES: std::sync::OnceLock<BTreeMap<&'static str, BTreeSet<String>>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        library_declarations()
            .keys()
            .map(|identity| {
                (
                    *identity,
                    library_names_of(identity, &[DeclarationKind::Theorem])
                        .map(str::to_string)
                        .collect(),
                )
            })
            .collect()
    })
}

/// The pure functions and predicates of each Click library module. Types,
/// constructors and resources keep their bare names.
fn library_functions_and_predicates() -> &'static BTreeMap<&'static str, BTreeSet<String>> {
    static NAMES: std::sync::OnceLock<BTreeMap<&'static str, BTreeSet<String>>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        library_declarations()
            .keys()
            .map(|identity| {
                (
                    *identity,
                    library_names_of(
                        identity,
                        &[DeclarationKind::Function, DeclarationKind::Predicate],
                    )
                    .map(str::to_string)
                    .collect(),
                )
            })
            .collect()
    })
}

/// The qualified identity of each pure function a Click library module
/// declares: `click::m::f` for a qualified module, else the bare name.
pub(super) fn library_pure_function_names() -> &'static BTreeSet<String> {
    static NAMES: std::sync::OnceLock<BTreeSet<String>> = std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = BTreeSet::new();
        for identity in library_declarations().keys() {
            let path = crate::surface::library_module_path(identity);
            for name in library_names_of(identity, &[DeclarationKind::Function]) {
                if is_qualified_declaration(identity, name) {
                    names.insert(format!("{path}::{name}"));
                } else {
                    names.insert(name.to_string());
                }
            }
        }
        names
    })
}

/// Whether Click library module `identity` declares `name` at top level.
pub(super) fn module_declares(identity: &str, name: &str) -> bool {
    library_declaration_names()
        .get(identity)
        .is_some_and(|names| names.contains(name))
}

/// The identity of the Click library module whose source is `file`.
fn module_identity_of_file(file: &str) -> Option<&'static str> {
    super::CLICK_LIBRARY_MODULES
        .iter()
        .map(|(module, _)| *module)
        .find(|module| *module == file)
}

/// The `library/` identity of a module path such as `["c", "string"]`.
fn module_identity(segments: &[&str]) -> Option<&'static str> {
    let identity = format!("library/{}.click", segments.join("/"));
    super::CLICK_LIBRARY_MODULES
        .iter()
        .map(|(module, _)| *module)
        .find(|module| *module == identity)
}

/// Rewrites each qualified library name to the declaration it names, and
/// records how it was written ([`WrittenPath`]). A selectively imported bare
/// name is left as written: only the parser knows whether it is read as a
/// Click reference ([`SymbolTable::reference`]).
///
/// `click::m::name` names `name` in module `click::m` and needs no import;
/// its module joins the returned set, which the file adds to its library
/// imports. `m::name` names the same declaration when module `m` is in scope:
/// an implicit module, or one the file imports. A path whose last segment is
/// not a declaration of that module is left alone, so constructor paths such
/// as `Nat::Zero` parse as before. Inside library module `file`, the module
/// is in scope by its own short name, and a path to it brings nothing.
pub(super) struct ResolvedLibraryTokens {
    pub(super) tokens: Vec<Token>,
    pub(super) positions: Vec<SourcePosition>,
    pub(super) path_modules: BTreeSet<&'static str>,
    pub(super) symbols: SymbolTable,
}

/// A library path joined into one token, as it was written. A C or C++
/// declaration name such as `list::append` reads this spelling: the join
/// cannot tell a namespace member from a Click reference, but the parser can.
/// A path through a library module the file does not import is joined as
/// written and keeps the refusal a Click reference to it receives.
#[derive(Clone, Debug)]
pub(super) struct WrittenPath {
    pub(super) written: String,
    pub(super) refusal: Option<String>,
}

pub(super) fn resolve_library_paths(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    file: Option<&str>,
) -> Result<ResolvedLibraryTokens, ClickError> {
    if !tokens.contains(&Token::ColonColon) {
        let scope = SymbolTable::from_tokens(&tokens, &positions, file)?;
        return Ok(ResolvedLibraryTokens {
            tokens,
            positions,
            path_modules: BTreeSet::new(),
            symbols: scope,
        });
    }
    let names = library_declaration_names();
    let scope = SymbolTable::from_tokens(&tokens, &positions, file)?;
    let mut scope = scope;
    let mut written_paths = BTreeMap::new();
    let SymbolTable {
        in_scope,
        import_spans,
        own,
        ..
    } = &scope;
    let mut resolved_tokens = Vec::with_capacity(tokens.len());
    let mut resolved_positions = Vec::with_capacity(positions.len());
    let mut path_modules = BTreeSet::new();
    let mut index = 0;
    while index < tokens.len() {
        if let Some(&end) = import_spans.get(&index) {
            for skipped in index..end {
                resolved_tokens.push(tokens[skipped].clone());
                resolved_positions.push(positions[skipped].clone());
            }
            index = end;
            continue;
        }
        if let Some((path, consumed, module)) =
            library_path_at(&tokens, index, names, in_scope, &positions)?
        {
            if let Some(module) = module
                && Some(module) != *own
            {
                path_modules.insert(module);
            }
            let written = (index..index + consumed)
                .map(|token| match &tokens[token] {
                    Token::Ident(segment) => segment.as_str(),
                    _ => "::",
                })
                .collect::<String>();
            let (name, refusal) = match path {
                LibraryPath::Resolved(name) => (name, None),
                LibraryPath::Unimported(refusal) => (written.clone(), Some(refusal)),
            };
            if name != written || refusal.is_some() {
                written_paths.insert(positions[index].clone(), WrittenPath { written, refusal });
            }
            resolved_tokens.push(Token::Ident(name));
            resolved_positions.push(positions[index].clone());
            index += consumed;
            continue;
        }
        resolved_tokens.push(tokens[index].clone());
        resolved_positions.push(positions[index].clone());
        index += 1;
    }
    scope.written_paths = written_paths;
    Ok(ResolvedLibraryTokens {
        tokens: resolved_tokens,
        positions: resolved_positions,
        path_modules,
        symbols: scope,
    })
}

fn short_module_name(identity: &str) -> &str {
    identity
        .strip_prefix("library/")
        .and_then(|path| path.strip_suffix(".click"))
        .and_then(|path| path.rsplit('/').next())
        .unwrap_or(identity)
}

/// What a qualified library name names.
enum LibraryPath {
    /// The declaration's resolved name.
    Resolved(String),
    /// A declaration of a module the file does not import, with the refusal
    /// a Click reference to it receives.
    Unimported(String),
}

/// The declaration a qualified library name at `start` names, the number of
/// tokens it spans, and, for a full `click::` path, the module it brings.
fn library_path_at(
    tokens: &[Token],
    start: usize,
    names: &BTreeMap<&'static str, BTreeSet<String>>,
    in_scope: &BTreeMap<String, &'static str>,
    positions: &[SourcePosition],
) -> Result<Option<(LibraryPath, usize, Option<&'static str>)>, ClickError> {
    let Some(Token::Ident(first)) = tokens.get(start) else {
        return Ok(None);
    };
    // The tail of a longer path, `core::u32::min`, is no library path, and
    // nor is the path a function head declares, `fn slice::len<T>(...)`: a
    // Rust contract's path names the program's function, which may share a
    // library module function's path.
    if tokens.get(start + 1) != Some(&Token::ColonColon)
        || start.checked_sub(1).is_some_and(|previous| {
            matches!(&tokens[previous], Token::ColonColon)
                || matches!(&tokens[previous], Token::Ident(word) if word == "fn")
        })
    {
        return Ok(None);
    }
    let mut segments = vec![first.as_str()];
    let mut cursor = start + 1;
    while tokens.get(cursor) == Some(&Token::ColonColon) {
        let Some(Token::Ident(segment)) = tokens.get(cursor + 1) else {
            break;
        };
        segments.push(segment.as_str());
        cursor += 2;
    }
    let (declaration, module_path) = segments.split_last().expect("a path has segments");
    let consumed = segments.len() * 2 - 1;
    if first == "click" {
        let Some(identity) = module_identity(&module_path[1..]) else {
            return Ok(None);
        };
        if !names[identity].contains(*declaration) {
            return Err(path_error(
                positions,
                start,
                format!(
                    "`{}` names no declaration of Click library module `{}`",
                    segments.join("::"),
                    module_path.join("::")
                ),
            ));
        }
        return Ok(Some((
            LibraryPath::Resolved(resolved_name(identity, declaration)),
            consumed,
            Some(identity),
        )));
    }
    let [module] = module_path else {
        return Ok(None);
    };
    if let Some(identity) = in_scope.get(*module) {
        if names[identity].contains(*declaration) {
            return Ok(Some((
                LibraryPath::Resolved(resolved_name(identity, declaration)),
                consumed,
                None,
            )));
        }
        return Ok(None);
    }
    // A module the file has not imported: say which import or path names it.
    let unimported = super::CLICK_LIBRARY_MODULES
        .iter()
        .map(|(identity, _)| *identity)
        .find(|identity| {
            short_module_name(identity) == *module && names[identity].contains(*declaration)
        });
    if let Some(identity) = unimported {
        let path = crate::surface::library_module_path(identity);
        return Ok(Some((
            LibraryPath::Unimported(format!(
                "`{module}::{declaration}` names Click library module `{path}`, which this file does not import; add `import {path};` or write `{path}::{declaration}`"
            )),
            consumed,
            None,
        )));
    }
    Ok(None)
}

/// The name a path to `declaration` in module `identity` resolves to: a
/// theorem's qualified identity, and any other declaration's bare name.
fn resolved_name(identity: &str, declaration: &str) -> String {
    if is_qualified_declaration(identity, declaration) {
        format!(
            "{}::{declaration}",
            crate::surface::library_module_path(identity)
        )
    } else {
        declaration.to_string()
    }
}

fn path_error(positions: &[SourcePosition], index: usize, message: String) -> ClickError {
    match positions.get(index) {
        Some(position) => ClickError::new(format!("{position}: {message}")),
        None => ClickError::new(message),
    }
    .with_kind(ClickErrorKind::Syntax)
}

/// A file's symbol table: the top-level declarations of the file and of the
/// user modules it imports, and the library modules and selectively imported
/// names in scope. Lowering resolves file-level names here, and source
/// spelling asks it how to write a name ([`Self::spelling`]). Canonical
/// library identities never depend on printed text. Names bound inside a
/// declaration are the parser's scoped `NameTable`.
#[derive(Clone, Debug, Default)]
pub(super) struct SymbolTable {
    in_scope: BTreeMap<String, &'static str>,
    selected: BTreeMap<String, String>,
    import_spans: BTreeMap<usize, usize>,
    own: Option<&'static str>,
    /// Each declared name's kinds and origins. A name declared twice keeps
    /// both entries; validation refuses the duplicate.
    declared: BTreeMap<String, Vec<(DeclarationKind, DeclarationOrigin)>>,
    explicit_paths: BTreeSet<String>,
    /// The library paths joined into one token, by their first position.
    written_paths: BTreeMap<SourcePosition, WrittenPath>,
}

impl SymbolTable {
    fn from_tokens(
        tokens: &[Token],
        positions: &[SourcePosition],
        file: Option<&str>,
    ) -> Result<Self, ClickError> {
        // Modules in scope by their last path segment: the implicit modules and
        // the file's own `import click::...;` lines.
        let mut in_scope = BTreeMap::<String, &'static str>::new();
        let own = file.and_then(module_identity_of_file);
        for identity in crate::surface::validation::implicit_library_modules().chain(own) {
            in_scope.insert(short_module_name(identity).to_string(), identity);
        }
        // Names a selective import brings, and the token ranges of the import
        // statements, which are left as written.
        let mut selected = BTreeMap::<String, String>::new();
        let mut import_spans = BTreeMap::new();
        let mut declared = BTreeMap::<String, Vec<(DeclarationKind, DeclarationOrigin)>>::new();
        for declaration in top_level_declarations(tokens) {
            declared
                .entry(declaration.name)
                .or_default()
                .push((declaration.kind, DeclarationOrigin::File));
        }
        for (index, token) in tokens.iter().enumerate() {
            if *token != Token::Ident("import".to_string())
                || tokens.get(index + 1) != Some(&Token::Ident("click".to_string()))
            {
                continue;
            }
            let mut segments = Vec::new();
            let mut cursor = index + 2;
            while tokens.get(cursor) == Some(&Token::ColonColon) {
                let Some(Token::Ident(segment)) = tokens.get(cursor + 1) else {
                    break;
                };
                segments.push(segment.as_str());
                cursor += 2;
            }
            let Some(identity) = module_identity(&segments) else {
                continue;
            };
            in_scope.insert(short_module_name(identity).to_string(), identity);
            if tokens.get(cursor) == Some(&Token::ColonColon)
                && tokens.get(cursor + 1) == Some(&Token::LBrace)
            {
                cursor += 2;
                while let Some(Token::Ident(name)) = tokens.get(cursor) {
                    if declared.contains_key(name) {
                        return Err(path_error(
                            positions,
                            cursor,
                            format!(
                                "`{name}` is imported from `{}` and also declared in this file; drop the import, rename the declaration, or write the library's by its path",
                                crate::surface::library_module_path(identity)
                            ),
                        ));
                    }
                    let resolved = resolved_name(identity, name);
                    if let Some(previous) = selected.insert(name.clone(), resolved.clone())
                        && previous != resolved
                    {
                        return Err(path_error(
                            positions,
                            cursor,
                            format!("`{name}` is imported twice, as `{previous}` and `{resolved}`"),
                        ));
                    }
                    cursor += 1;
                    if tokens.get(cursor) == Some(&Token::Comma) {
                        cursor += 1;
                    }
                }
            }
            let end = tokens[index..]
                .iter()
                .position(|token| *token == Token::Semicolon)
                .map_or(tokens.len(), |offset| index + offset);
            import_spans.insert(index, end);
        }

        // A file enum named like an in-scope library module would make
        // `m::x` name both its constructor and the module's declaration.
        if !file.is_some_and(|file| file.starts_with("library/")) {
            for (index, pair) in tokens.windows(2).enumerate() {
                if let [Token::Ident(keyword), Token::Ident(name)] = pair
                    && keyword == "enum"
                    && let Some(identity) = in_scope.get(name)
                {
                    return Err(path_error(
                        positions,
                        index + 1,
                        format!(
                            "enum `{name}` takes the name of Click library module `{}`, so `{name}::...` would name both; rename the enum",
                            crate::surface::library_module_path(identity)
                        ),
                    ));
                }
            }
        }
        let mut explicit_paths = BTreeSet::new();
        for start in 0..tokens.len() {
            if tokens[start] != Token::Ident("click".to_string()) {
                continue;
            }
            let mut path = String::from("click");
            let mut cursor = start + 1;
            while tokens.get(cursor) == Some(&Token::ColonColon) {
                let Some(Token::Ident(segment)) = tokens.get(cursor + 1) else {
                    break;
                };
                path.push_str("::");
                path.push_str(segment);
                cursor += 2;
            }
            explicit_paths.insert(path);
        }
        Ok(Self {
            in_scope,
            selected,
            import_spans,
            own,
            declared,
            explicit_paths,
            written_paths: BTreeMap::new(),
        })
    }

    /// The declaration a Click reference written `name` at `position` names:
    /// a selectively imported name's library declaration, or the refusal of
    /// a path through a module the file does not import.
    pub(super) fn reference(
        &self,
        name: String,
        position: &SourcePosition,
    ) -> Result<String, String> {
        if let Some(path) = self.written_paths.get(position) {
            return match &path.refusal {
                Some(refusal) => Err(refusal.clone()),
                None => Ok(name),
            };
        }
        Ok(self.selected.get(&name).cloned().unwrap_or(name))
    }

    /// How a library path joined at `position` was written, for a reader of
    /// C and C++ declaration names.
    pub(super) fn written_path(&self, position: &SourcePosition) -> Option<&str> {
        self.written_paths
            .get(position)
            .map(|path| path.written.as_str())
    }

    /// Binds the declarations of the user modules this file imports as the
    /// file's own bind theirs: an imported theorem shadows a bare library
    /// theorem, and a selective import of a name an imported module declares
    /// is refused, so one bare name never reads as two declarations.
    pub(super) fn import_declarations(
        &mut self,
        imported: &[(DeclarationKind, String)],
    ) -> Result<(), ClickError> {
        if let Some((_, name)) = imported
            .iter()
            .find(|(_, name)| self.selected.contains_key(name))
        {
            return Err(ClickError::new(format!(
                "`{name}` is imported from the Click library as `{}` and also declared by an imported module; drop the library import, rename the declaration, or write the library's by its path",
                self.selected[name]
            ))
            .with_kind(ClickErrorKind::Syntax));
        }
        for (kind, name) in imported {
            self.declared
                .entry(name.clone())
                .or_default()
                .push((*kind, DeclarationOrigin::Imported));
        }
        Ok(())
    }

    /// Records the file's declarations as the parser reads them, after the
    /// rewrites that write out declarations the source does not spell, such
    /// as a Rust generic function's instances.
    pub(super) fn declare_file(&mut self, declarations: &[TopLevelDeclaration]) {
        for declaration in declarations {
            let entries = self.declared.entry(declaration.name.clone()).or_default();
            if !entries.contains(&(declaration.kind, DeclarationOrigin::File)) {
                entries.push((declaration.kind, DeclarationOrigin::File));
            }
        }
    }

    /// Whether the file or a user module it imports declares `name` as `kind`.
    pub(super) fn declares(&self, kind: DeclarationKind, name: &str) -> bool {
        self.declared
            .get(name)
            .is_some_and(|entries| entries.iter().any(|(declared, _)| *declared == kind))
    }

    /// The names the user modules this file imports declare as `kind`.
    pub(super) fn imported_names(&self, kind: DeclarationKind) -> impl Iterator<Item = &str> {
        self.declared.iter().filter_map(move |(name, entries)| {
            entries
                .contains(&(kind, DeclarationOrigin::Imported))
                .then_some(name.as_str())
        })
    }

    /// Whether a call `name(...)` reads a pure function: one the file, an
    /// imported module or the Click library declares. A bare call written
    /// where a proposition is expected reads as `f(args) == true` when it
    /// names one, and as a predicate call otherwise.
    pub(super) fn is_pure_function(&self, name: &str) -> bool {
        self.declares(DeclarationKind::Function, name)
            || library_pure_function_names().contains(name)
    }

    pub(super) fn for_source(source: &str) -> Result<Self, ClickError> {
        let (tokens, positions) = tokenizer::tokenize(source, None)?;
        Self::from_tokens(&tokens, &positions, None)
    }

    pub(super) fn visible_modules(&self) -> Vec<String> {
        self.in_scope
            .values()
            .map(|identity| identity.to_string())
            .collect()
    }

    /// The identity a Click reference written `spelling` names in this file,
    /// by the rules the parser applies: a path `click::m::x`, or `m::x` with
    /// `m` in scope, names the library declaration; a bare name reads a
    /// selective import, else a declaration of this file or of an imported
    /// module. Spellings are chosen
    /// ([`Self::spelling`]) by these rules and no others.
    pub(super) fn resolve(&self, spelling: &str) -> String {
        if let Some((module, name)) = spelling.rsplit_once("::") {
            let identity = match module.strip_prefix("click::") {
                Some(path) => module_identity(&path.split("::").collect::<Vec<_>>()),
                None => self.in_scope.get(module).copied(),
            };
            return match identity {
                Some(identity) if module_declares(identity, name) => resolved_name(identity, name),
                _ => spelling.to_string(),
            };
        }
        self.selected
            .get(spelling)
            .cloned()
            .unwrap_or_else(|| spelling.to_string())
    }

    /// The shortest spelling of `path` that [`Self::resolve`] reads back as
    /// `path`: its bare name, its module's short path, or the full path. A
    /// path the file wrote explicitly keeps its spelling.
    pub(super) fn spelling<'a>(&self, path: &'a str) -> std::borrow::Cow<'a, str> {
        crate::instrumentation::record_deterministic_work(1);
        let Some((module, bare)) = path.rsplit_once("::") else {
            return path.into();
        };
        if self.explicit_paths.contains(path) {
            return path.into();
        }
        if self.resolve(bare) == path {
            return bare.into();
        }
        let short = format!("{}::{bare}", module.rsplit("::").next().unwrap_or(module));
        if self.resolve(&short) == path {
            return short.into();
        }
        path.into()
    }
}

/// The qualified identity of the Click library theorem `name`: `name`
/// itself when it is already qualified or names no library theorem.
#[cfg(test)]
pub(in crate::surface) fn library_theorem_identity(name: &str) -> String {
    library_theorem_identities()
        .get(name)
        .cloned()
        .unwrap_or_else(|| name.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    // A function head's path is the program's function, even where it is a
    // library module function's path: the library's `extern fn
    // slice::len<T>` models Rust's `<[T]>::len`, and its contract's
    // `slice::len(s)` is the `click::rust::slice` function.
    #[test]
    fn a_function_head_path_is_not_a_library_path() {
        let source = "import click::rust::slice; \
                      extern fn slice::len<T>(s: Slice<T>) -> usize { ensures result == slice::len(s); }";
        let (tokens, positions) = tokenizer::tokenize(source, None).unwrap();
        let tokens = resolve_library_paths(tokens, positions, None)
            .unwrap()
            .tokens;
        let head = tokens
            .iter()
            .position(|token| *token == Token::Ident("fn".into()))
            .unwrap();
        assert_eq!(
            tokens[head + 1..head + 4],
            [
                Token::Ident("slice".into()),
                Token::ColonColon,
                Token::Ident("len".into())
            ]
        );
        assert!(tokens[head + 4..].contains(&Token::Ident(resolved_name(
            "library/rust/slice.click",
            "len"
        ))));
    }
}
